{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}

-- | This module contains a permuted linear congruential pseudorandom number
-- generator, as described by M.E. O'Neill (<pcg-random.org>). This version
-- holds two 'Word64' values and outputs a 'Word32' of randomness each time you
-- use it. Compared to the 'StdGen' type from "System.Random", it's around a
-- 2.5x to 3x speedup on a 64-bit system. It runs somewhat slower than @StdGen@
-- on a 32-bit system (the @Word64@ values must be emulated after all), but
-- there aren't too many of those in play these days anyway. Raspberry Pi is the
-- only common thing I can think of, which isn't the best for Haskell in the
-- first place. If you somehow are using 32-bit all the time I guess this module
-- isn't for you.
--
-- The first @Word64@ is the @state@, which changes with each step of the
-- generator. The second @Word64@ is the @inc@, which stays fixed from step to
-- step and controls what stream of numbers is generated. The @inc@ is always
-- bitwise OR'd with 1 during computations, so there are only 2^63 distinct
-- number streams (eg: @inc@ 2 and 3 are the same number stream). The @state@
-- value eventually returns to its initial value after 2^64 uses and the whole
-- sequence loops around.
module Data.PCGen (
    PCGen(PCGen),
    mkPCGen,
    stepGen
    ) where

-- base
import Data.Bits
import Data.Word (Word32,Word64)
import Data.Int (Int32)
import Foreign.Storable
import Foreign.Ptr
import Control.Exception
import GHC.Exts ((+#), (*#), Addr#, ByteArray#, Int(I#), Int#, MutableByteArray#, State#)
-- random
import System.Random
-- primitive
import Data.Primitive.Types (Prim(..), defaultSetByteArray#, defaultSetOffAddr#)

-- | The @PCGen@ data type. You can use the constructor yourself with two
-- @Word64@ values, but with human picked seeds the first result will generally
-- be 0. To avoid that you can use the 'mkPCGen' helper.
data PCGen = PCGen !Word64 !Word64
    -- Programmer's Note: GHC unpacks small fields by default when they're
    -- strict, and if the user for some reason *did* turn that feature off, then
    -- we should respect their wishes and not unpack our crap in their space. So
    -- we deliberately leave out the UNPACK directive on these fields.
    deriving (Read, Show, Eq, Ord)

-- | Creates a new PCGen value by using the Integral given as both the @state@
-- and @inc@ values for the generator. The state of the generator is then
-- advanced once, because otherwise the first result tends to be 0 with human
-- picked seeds.
mkPCGen :: Integral i => i -> PCGen
mkPCGen n = let
    n' = fromIntegral n
    in snd $ stepGen $ PCGen n' n'

-- | Advances the given generator one step, giving back a @Word32@ of output and
-- the resultant generator as well. This is the most basic way to advance the
-- generator. You probably want to use the 'RandomGen' instance and the 'next'
-- method, along with something like 'MonadRandom'
stepGen :: PCGen -> (Word32,PCGen)
stepGen (PCGen state inc) = let
    newState = state * 6364136223846793005 + (inc .|. 1)
    xorShifted = fromIntegral (((state `shiftR` 18) `xor` state) `shiftR` 27) :: Word32
    rot = fromIntegral (state `shiftR` 59) :: Word32
    out = (xorShifted `shiftR` (fromIntegral rot)) .|. (xorShifted `shiftL` fromIntegral ((-rot) .&. 31))
    in (out, PCGen newState inc)

instance RandomGen PCGen where
    genWord32 = stepGen

    -- The only real spec here is that the two result generators be dissimilar
    -- from each other and also from the input generator. So we just do some
    -- nonsense shuffling around to achieve that.
    split gen@(PCGen state inc) = let -- no statistical foundation for this!
        (q,nGen1@(PCGen sa ia)) = stepGen gen
        (w,nGen2@(PCGen sb ib)) = stepGen nGen1
        (e,nGen3@(PCGen sc ic)) = stepGen nGen2
        (r,nGen4@(PCGen sd id)) = stepGen nGen3
        stateA = sd `rotateR` 5
        stateB = sd `rotateR` 3
        incA = ((fromIntegral q) `shiftL` 32) .|. (fromIntegral w)
        incB = ((fromIntegral e) `shiftL` 32) .|. (fromIntegral r)
        outA = PCGen stateA (incA .|. 1)
        outB = PCGen stateB (incB .|. 1)
        in (outA, outB)
        -- TODO: This could probably be faster while still conforming to spec.

instance Uniform PCGen where
    uniform gen = do
        x <- uniform gen
        return $ mkPCGen (x :: Word64)

instance Storable PCGen where
    sizeOf _ = sizeOf (undefined :: Word64) * 2
    alignment _ = alignment (undefined :: Word64)
    peek ptr = do
        if alignPtr ptr (alignment (undefined :: PCGen)) == ptr
            then do
                let word64Ptr = castPtr ptr
                    offset = sizeOf (undefined :: Word64)
                s <- peek word64Ptr :: IO Word64
                i <- peek (plusPtr word64Ptr offset) :: IO Word64
                pure $ PCGen s i
            else error "The Ptr is not correctly aligned"
    poke ptr (PCGen s i) = do
        if alignPtr ptr (alignment (undefined :: PCGen)) == ptr
            then do
                let word64Ptr = castPtr ptr
                    offset = sizeOf (undefined :: Word64)
                poke word64Ptr s
                poke (plusPtr word64Ptr offset) i
            else error "The Ptr is not correctly aligned"

instance Prim PCGen where
  sizeOf#         = sizeOf128#
  alignment#      = alignment128#
  indexByteArray# = indexByteArray128#
  readByteArray#  = readByteArray128#
  writeByteArray# = writeByteArray128#
  setByteArray#   = setByteArray128#
  indexOffAddr#   = indexOffAddr128#
  readOffAddr#    = readOffAddr128#
  writeOffAddr#   = writeOffAddr128#
  setOffAddr#     = setOffAddr128#
  {-# INLINE sizeOf# #-}
  {-# INLINE alignment# #-}
  {-# INLINE indexByteArray# #-}
  {-# INLINE readByteArray# #-}
  {-# INLINE writeByteArray# #-}
  {-# INLINE setByteArray# #-}
  {-# INLINE indexOffAddr# #-}
  {-# INLINE readOffAddr# #-}
  {-# INLINE writeOffAddr# #-}
  {-# INLINE setOffAddr# #-}

{-# INLINE sizeOf128# #-}
sizeOf128# :: PCGen -> Int#
sizeOf128# _ = 2# *# sizeOf# (undefined :: Word64)

{-# INLINE alignment128# #-}
alignment128# :: PCGen -> Int#
alignment128# _ = 2# *# alignment# (undefined :: Word64)

{-# INLINE indexByteArray128# #-}
indexByteArray128# :: ByteArray# -> Int# -> PCGen
indexByteArray128# arr# i# =
  let i2# = 2# *# i#
      x = indexByteArray# arr# (i2# +# unInt index1)
      y = indexByteArray# arr# (i2# +# unInt index0)
  in PCGen x y

{-# INLINE readByteArray128# #-}
readByteArray128# :: MutableByteArray# s -> Int# -> State# s -> (# State# s, PCGen #)
readByteArray128# arr# i# =
  \s0 -> case readByteArray# arr# (i2# +# unInt index1) s0 of
    (# s1, x #) -> case readByteArray# arr# (i2# +# unInt index0) s1 of
      (# s2, y #) -> (# s2, PCGen x y #)
  where i2# = 2# *# i#

{-# INLINE writeByteArray128# #-}
writeByteArray128# :: MutableByteArray# s -> Int# -> PCGen -> State# s -> State# s
writeByteArray128# arr# i# (PCGen a b) =
  \s0 -> case writeByteArray# arr# (i2# +# unInt index1) a s0 of
    s1 -> case writeByteArray# arr# (i2# +# unInt index0) b s1 of
      s2 -> s2
  where i2# = 2# *# i#

{-# INLINE setByteArray128# #-}
setByteArray128# :: MutableByteArray# s -> Int# -> Int# -> PCGen -> State# s -> State# s
setByteArray128# = defaultSetByteArray#

{-# INLINE indexOffAddr128# #-}
indexOffAddr128# :: Addr# -> Int# -> PCGen
indexOffAddr128# addr# i# =
  let i2# = 2# *# i#
      x = indexOffAddr# addr# (i2# +# unInt index1)
      y = indexOffAddr# addr# (i2# +# unInt index0)
  in PCGen x y

{-# INLINE readOffAddr128# #-}
readOffAddr128# :: Addr# -> Int# -> State# s -> (# State# s, PCGen #)
readOffAddr128# addr# i# =
  \s0 -> case readOffAddr# addr# (i2# +# unInt index1) s0 of
    (# s1, x #) -> case readOffAddr# addr# (i2# +# unInt index0) s1 of
      (# s2, y #) -> (# s2, PCGen x y #)
  where i2# = 2# *# i#

{-# INLINE writeOffAddr128# #-}
writeOffAddr128# :: Addr# -> Int# -> PCGen -> State# s -> State# s
writeOffAddr128# addr# i# (PCGen a b) =
  \s0 -> case writeOffAddr# addr# (i2# +# unInt index1) a s0 of
    s1 -> case writeOffAddr# addr# (i2# +# unInt index0) b s1 of
      s2 -> s2
  where i2# = 2# *# i#

{-# INLINE setOffAddr128# #-}
setOffAddr128# :: Addr# -> Int# -> Int# -> PCGen -> State# s -> State# s
setOffAddr128# = defaultSetOffAddr#

unInt :: Int -> Int#
unInt (I# i#) = i#

-- Use these indices to get the peek/poke ordering endian correct.
index0, index1 :: Int
#if WORDS_BIGENDIAN
index0 = 1
index1 = 0
#else
index0 = 0
index1 = 1
#endif
