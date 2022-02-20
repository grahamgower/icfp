-- ICFP2006: http://www.boundvariable.org/task.shtml

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
-- base
import Data.Bits
import Data.Char
import Data.Word
import Text.Printf
import Control.Monad.Primitive (PrimState)
import qualified Data.List as L
import qualified System.Environment
import qualified System.Exit
import qualified System.IO

-- bytestring
import qualified Data.ByteString.Lazy as B
-- containers
import qualified Data.IntMap.Strict as IntMap
-- vector
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV

data Instruction
  = Move Int Int Int
  | ArrayIndex Int Int Int
  | ArrayAmend Int Int Int
  | Add Int Int Int
  | Mul Int Int Int
  | Div Int Int Int
  | Nand Int Int Int
  | Halt
  | Alloc Int Int
  | Free Int
  | Output Int
  | Input Int
  | LoadProgram Int Int
  | Orthography Int Word32
  deriving Show

{-# INLINE decodeInstr #-}
decodeInstr :: Word32 -> Instruction
decodeInstr instr =
  let opcode = (instr `shiftR` 28) .&. 0xf
      iA = fromIntegral $ (instr `shiftR` 6) .&. 0x7
      iB = fromIntegral $ (instr `shiftR` 3) .&. 0x7
      iC = fromIntegral $ instr .&. 0x7
  in
    case opcode of
      0 -> Move iA iB iC
      1 -> ArrayIndex iA iB iC
      2 -> ArrayAmend iA iB iC
      3 -> Add iA iB iC
      4 -> Mul iA iB iC
      5 -> Div iA iB iC
      6 -> Nand iA iB iC
      7 -> Halt
      8 -> Alloc iB iC
      9 -> Free iC
      10 -> Output iC
      11 -> Input iC
      12 -> LoadProgram iB iC
      13 ->
        let iA' = fromIntegral $ (instr `shiftR` 25) .&. 0x7
            val = instr .&. 0x1ffffff
        in
          Orthography iA' val
      _ -> error $ "invalid instruction " <> show instr

{-
dumpState :: Instruction -> Int -> MV.MVector Word32 -> IntMap.IntMap (V.Vector Word32) -> IO ()
dumpState op finger reg mem = do
  let reg_list = [MV.read reg i | i <- [0..((MV.length reg) - 1)]]
  let reg_str = (L.intercalate " " (map (printf "0x%08x") reg_list)) :: String
  let op_str = show op
  hPrintf System.IO.stderr "%04x: %-20s  | %s | %d arrays\n" finger op_str reg_str (IntMap.size mem)
-}

spinCycle :: Int
  -> MV.MVector (PrimState IO) Word32
  -> MV.MVector (PrimState IO) Word32
  -> IntMap.IntMap (V.Vector Word32)
  -> [Int]
  -> IO ()
spinCycle finger reg program mem freekeys = do
  instr <- MV.read program finger
  let op = decodeInstr instr
  let finger' = finger + 1
  --dumpState op finger reg mem
  case op of

    Move iA iB iC -> do
      -- The register A receives the value in register B,
      -- unless the register C contains 0.
      rC <- MV.unsafeRead reg iC
      if rC /= 0 then do
        rB <- MV.unsafeRead reg iB
        MV.unsafeWrite reg iA rB
      else
        return ()
      spinCycle finger' reg program mem freekeys

    ArrayIndex iA iB iC -> do
      -- The register A receives the value stored at offset
      -- in register C in the array identified by B.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      rA' <-
        if rB == 0 then
          MV.read program (fromIntegral rC)
        else 
          let array = mem IntMap.! (fromIntegral rB)
          in return (array V.! (fromIntegral rC))
      MV.unsafeWrite reg iA rA'
      spinCycle finger' reg program mem freekeys

    ArrayAmend iA iB iC -> do
      -- The array identified by A is amended at the offset
      -- in register B to store the value in register C.
      rA <- MV.unsafeRead reg iA
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      if rA == 0 then do
        MV.write program (fromIntegral rB) rC
        spinCycle finger' reg program mem freekeys
      else do
        let frob_array = (V.// [((fromIntegral rB), rC)])
        let mem' = IntMap.adjust frob_array (fromIntegral rA) mem
        spinCycle finger' reg program mem' freekeys

    Add iA iB iC -> do
      -- The register A receives the value in register B plus 
      -- the value in register C, modulo 2^32.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      MV.unsafeWrite reg iA (rB + rC)
      spinCycle finger' reg program mem freekeys

    Mul iA iB iC -> do
      -- The register A receives the value in register B times
      -- the value in register C, modulo 2^32.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      MV.unsafeWrite reg iA (rB * rC)
      spinCycle finger' reg program mem freekeys

    Div iA iB iC -> do
      -- The register A receives the value in register B
      -- divided by the value in register C, if any, where
      -- each quantity is treated treated as an unsigned 32
      -- bit number.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      MV.unsafeWrite reg iA (rB `div` rC)
      spinCycle finger' reg program mem freekeys

    Nand iA iB iC -> do
      -- Each bit in the register A receives the 1 bit if
      -- either register B or register C has a 0 bit in that
      -- position.  Otherwise the bit in register A receives
      -- the 0 bit.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      let rA' = complement (rB .&. rC)
      MV.unsafeWrite reg iA rA'
      spinCycle finger' reg program mem freekeys

    Halt ->
      -- The universal machine stops computation.
      return ()

    Alloc iB iC -> do
      -- A new array is created with a capacity of platters
      -- commensurate to the value in the register C. This
      -- new array is initialized entirely with platters
      -- holding the value 0. A bit pattern not consisting of
      -- exclusively the 0 bit, and that identifies no other
      -- active allocated array, is placed in the B register.
      rC <- MV.unsafeRead reg iC
      let k = head freekeys
      let freekeys' = tail freekeys
      let array = V.replicate (fromIntegral rC) (0 :: Word32)
      let mem' = IntMap.insert k array mem
      MV.unsafeWrite reg iB (fromIntegral k)
      spinCycle finger' reg program mem' freekeys'

    Free iC -> do
      -- The array identified by the register C is abandoned.
      -- Future allocations may then reuse that identifier.
      rC <- MV.unsafeRead reg iC
      let freekeys' = (fromIntegral rC) : freekeys
      spinCycle finger' reg program mem freekeys'

    Output iC -> do
      -- The value in the register C is displayed on the console
      -- immediately. Only values between and including 0 and 255
      -- are allowed.
      rC <- MV.unsafeRead reg iC
      putChar $ chr $ fromIntegral (rC .&. 0xff)
      System.IO.hFlush System.IO.stdout
      spinCycle finger' reg program mem freekeys

    Input iC -> do
      -- The universal machine waits for input on the console.
      -- When input arrives, the register C is loaded with the
      -- input, which must be between and including 0 and 255.
      -- If the end of input has been signaled, then the 
      -- register C is endowed with a uniform value pattern
      -- where every place is pregnant with the 1 bit.
      eof <- System.IO.isEOF
      rC' <-
        if eof then
          return 0xffffffff
        else
          getChar >>= (return . fromIntegral . ord)
      MV.unsafeWrite reg iC rC'
      spinCycle finger' reg program mem freekeys

    LoadProgram iB iC -> do
      -- The array identified by the B register is duplicated
      -- and the duplicate shall replace the '0' array,
      -- regardless of size. The execution finger is placed
      -- to indicate the platter of this array that is
      -- described by the offset given in C, where the value
      -- 0 denotes the first platter, 1 the second, et cetera.
      --
      -- The '0' array shall be the most sublime choice for
      -- loading, and shall be handled with the utmost velocity.
      rB <- MV.unsafeRead reg iB
      rC <- MV.unsafeRead reg iC
      let finger'' = fromIntegral rC
      if rB == 0 then
        spinCycle finger'' reg program mem freekeys
      else do
        program' <- V.thaw $ mem IntMap.! (fromIntegral rB)
        spinCycle finger'' reg program' mem freekeys

    Orthography iA val -> do
      -- The value indicated is loaded into the register A forthwith.
      MV.unsafeWrite reg iA val
      spinCycle finger' reg program mem freekeys


runUM :: (V.Vector Word32) -> IO ()
runUM program = do
  -- Set the initial state and start the spin cycle.
  let finger = 0
  registers <- MV.replicate 8 (0 :: Word32)
  program' <- V.thaw program
  let memory = IntMap.empty
  let freekeys = [1..]  -- Available keys in the memory map.
  spinCycle finger registers program' memory freekeys

pack32 :: [Word8] -> [Word32]
pack32 (a:b:c:d:rest) =
  let bytes = map fromIntegral [a, b, c, d]
      w32 = sum $ zipWith shiftL bytes [24, 16, 8, 0]
  in
    w32 : pack32 rest
pack32 _ = []

readScroll :: FilePath -> IO (V.Vector Word32)
readScroll filename = do
  bytes <- B.readFile filename
  if B.length bytes `mod` 4 /= 0 then
    error $ filename <> ": length is not modulo 4"
  else
    return $ V.fromList $ (pack32 . B.unpack) bytes

main :: IO ()
main = do
  args <- System.Environment.getArgs
  case args of
    [filename] -> do
      program <- readScroll filename
      runUM program
    _ -> do
      prog_name <- System.Environment.getProgName
      putStrLn $ "usage: " <> prog_name <> " scroll.umz"
      System.Exit.exitFailure
