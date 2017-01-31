
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}

module Main where

-- The basic imports for working with rationals and ratios
import Data.Ratio

-- memoize important computations to prevent repetition
import Data.Function.Memoize

-- Add qualified instance so that we can use other definitions as needed
import Prelude hiding (min,max,(<*>))
import qualified Prelude as P

import qualified Math.Combinatorics.Exact.Binomial as C
import Math.Combinatorics.Exact.Factorial

import Data.Bits (bit)
import Crypto.Number.Basic (log2)

import Data.Maybe
import Data.Complex
import Data.Bits
import Data.List (group,sort)

import Data.Aeson hiding (Array)
import Data.Aeson.Encode.Pretty
import GHC.Generics

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

import Text.Show.Pretty

import Foreign.C.Types

import Data.Array.Repa.FFTW
import Data.Array.Repa.Index
import Data.Array.Repa.Repr.ForeignPtr
import Data.Array.Repa hiding (map,zipWith,(++))
import qualified Data.Array.Repa as A
import Data.Array.Repa.Eval (fromList)


-- import Numeric.FFT
import qualified Data.ByteString.Lazy as BS
import Debug.Trace

import Data.IORef

import Data.Foldable (foldl')

import System.Directory (createDirectoryIfMissing)

import Control.Monad (when)


rmdups :: (Ord a) => [a] -> [a]
rmdups = map head . group . sort

-- | This is the type we use for various sorts of distributions we're working
--   with
data Dist prob dom where
  Dist :: (Ord dom,Enum dom, Real prob) => {
    -- | The cumulative distribution function over the space in which we're
    --   working, we assume that the domain is an enumerable type with a useful
    --   predecessor and sucessor function.
      cdf :: dom -> prob
    -- | The PDF of the function we're working with, it should always be
    --   identical to `(\ x -> cdf x - cdf (pred x))`
    , pdf :: dom -> prob
    -- | The minimum value of a range outside of which the PDF is always 0
    , min :: !dom
    -- | The maximum value of a range outside of which the PDF is always 0
    , max :: !dom
    -- | The list of CDF values such that
    --   `cLst == map cdf [min..max]`
    --   with whatever intermediate coersion that implies
    , cLst :: Array F DIM1 (Complex Double)
    -- | The list of PDF values such that
    --   `pLst == map pdf [min..max]`
    --   with whatever intermediate coersion that implies
    , pLst :: Array F DIM1 (Complex Double)
    } -> Dist prob dom

printDist :: (Integral d,Enum d,Real p) => Dist p d -> String
printDist Dist{..} = ppShow (
  toInteger min,
  toInteger max,
  map (\ p -> (toInteger p,fromRational @Double . toRational $ cdf p)) [min..max])

printCDF :: (Integral d,Enum d,Real p) => CDF p d -> String
printCDF CDF{..} = ppShow (
  toInteger min,
  toInteger max,
  map (\ p -> (toInteger p,fromRational @Double . toRational $ cdf p)) [min..max])


-- This is the temporary CDF constructor that we use to construct a Dist as
-- needed, we generally work with things in their CDF form since it's much
-- more convinient and efficient than the PDF form.
data CDF prob dom where
  CDF :: (Ord dom, Fractional prob) => {
      cdf :: dom -> prob
    , min :: !dom
    , max :: !dom
    } -> CDF prob dom

-- typeclass to covert specific distribution types into Dist values that we
-- can use quickly.
class ToDist a prob dom where
  toDist :: a prob dom -> Dist prob dom

-- | Get the index of the last zero in a CDF's distribution, useful for
--   shrinking the domain of Dist when things look like a normal distribution
--
--   TODO :: Good lord, i think I've managed to fuck up writing an elegant
--           binary search.
getLastZero :: (Ord dom, Integral dom, RealFrac prob) => CDF prob dom -> dom
getLastZero c@CDF{..} | cdf min > 0 = min
                      | otherwise = {- trace ("cdf: " ++ printCDF c) $ -} search (min,max)

  where
    search (min,max) | min + 1 == max && cdf max <= thresh = max
                     | min + 1 == max && cdf min <= thresh = min
                     | min >= max && cdf max <= thresh = max
                     | cdf min <= thresh && cdf mid > thresh = search (min,mid)
                     | cdf mid <= thresh && cdf max > thresh = search (mid,max)
                     | otherwise = error $ "getLastZero is broken:" ++ printCDF c
      where
        thresh = 0.000001
        mid = {- trace ("glz: " ++ show (
           (toInteger min,fromRational @Double . toRational $ cdf min)
          ,(toInteger m' ,fromRational @Double . toRational $ cdf m')
          ,(toInteger max,fromRational @Double . toRational $ cdf max))) $ -} m'
        m' = (min + max) `div` 2

-- | Get the index of the first 1 in a CDF's distribution, useful for
--   shrinking the domain of Dist when things look like a normal distribution
getFirstOne :: (Ord dom, Integral dom, RealFrac prob) => CDF prob dom -> dom
getFirstOne CDF{..}  | cdf max < 1 = max
                     | otherwise = search (min,max)
  where
    search (min,max) | min + 1 == max && cdf min >= thresh = min
                     | min + 1 == max && cdf max >= thresh = max
                     | min >= max && cdf min >= thresh = min
                     | cdf mid < thresh && cdf max >= thresh = search (mid,max)
                     | cdf min < thresh && cdf mid >= thresh = search (min,mid)
                     | otherwise = error "GetFirstOne is Broken"
      where
        thresh = 0.999999
        mid = {- trace ("gfo: " ++ show (toInteger min,toInteger m',toInteger max)) $ -} m'
        m' = (min + max) `div` 2

-- | Get the index of the last zero in a CDF's distribution, useful for
--   shrinking the domain of Dist when things look like a normal distribution
--
--   TODO :: Good lord, i think I've managed to fuck up writing an elegant
--           binary search.
getLastZero' :: (Ord dom, Integral dom, RealFrac prob) => Dist prob dom -> dom
getLastZero' Dist{..} | cdf min > 0 = min
                      | otherwise = search (min,max)
  where
    search (min,max) | min + 1 == max && cdf max <= thresh = max
                     | min + 1 == max && cdf min <= thresh = min
                     | min >= max && cdf max <= thresh = max
                     | cdf min <= thresh && cdf mid > thresh = search (min,mid)
                     | cdf mid <= thresh && cdf max > thresh = search (mid,max)
                     | otherwise = error $ "getLastZero' is broken"
      where
        thresh = 0.000001
        mid =  {- trace ("glz: " ++ show (toInteger min,toInteger m',toInteger max)) $ -}  m'
        m' = (min + max) `div` 2

-- | Get the index of the first 1 in a CDF's distribution, useful for
--   shrinking the domain of Dist when things look like a normal distribution
getFirstOne' :: (Ord dom, Integral dom, RealFrac prob) => Dist prob dom -> dom
getFirstOne' Dist{..}  | cdf max < 1 = max
                       | otherwise = search (min,max)
  where
    search (min,max) | min + 1 == max && cdf min >= thresh = min
                     | min + 1 == max && cdf max >= thresh = max
                     | min >= max && cdf min >= thresh = min
                     | cdf mid < thresh && cdf max >= thresh = search (mid,max)
                     | cdf min < thresh && cdf mid >= thresh = search (min,mid)
                     | otherwise = error "GetFirstOne' is Broken"
      where
        thresh = 0.999999
        mid = {- trace ("gfo: " ++ show (toInteger min,toInteger m',toInteger max)) $ -} m'
        m' = (min + max) `div` 2

-- | Trim the portions of the CDF that have shrunk to be basically 0 or 1
--   minimizing work for convolutions and similar operations that work with
--   the list of relevant values.
shrinkCDF :: forall prob dom .(Ord dom, Integral dom, RealFrac prob) => CDF prob dom -> CDF prob dom
shrinkCDF c = {- to . tf $ -} c'
  where
    c' = (c{min = getLastZero c, max = getFirstOne c} :: CDF prob dom)
    to = trace $ "oldC:" ++ printCDF c
    tf = trace $ "newC:" ++ printCDF c'


-- This sort of wrapping allows us to make sure things are well memoized, in
-- general the CDF function will be the one which gets wrapped in a memoize,
-- with the rest of the instance just backed by that as needed.
instance (Ord dom, Integral dom, RealFrac prob) => ToDist CDF prob dom where
  toDist = assembleDist . shrinkCDF
    where
      assembleDist CDF{..} = Dist {
          cdf  = boundCDF (min,max) cdf
        , pdf  = boundPDF (min,max) pdf
        , min  = min
        , max  = max
        , cLst = fromList (Z :. lLen) . map (toCD . cdf) $ lKeys
        , pLst = fromList (Z :. lLen) . map (toCD . pdf) $ lKeys
        }
        where
          lKeys = [min..max]
          lLen = length lKeys
          pdf :: dom -> prob
          pdf x = cdf x - cdf (pred x)
          toCD :: Real p => p -> Complex Double
          toCD =  (:+ 0) . fromRational . toRational

-- | Add sane bounds to the CDF so that weird functions don't end up doing
--   silly things.
boundCDF :: (Ord dom,Real prob) => (dom,dom) -> (dom -> prob) -> dom -> prob
boundCDF (min,max) cdf i
  | i < min   = 0
  | i >= max   = 1
  | otherwise = cdf i

-- | Add sane bounds to the PDF so that weird functions don't end up doing
--   silly things.
boundPDF :: (Ord dom,Real prob) => (dom,dom) -> (dom -> prob) -> dom -> prob
boundPDF (min,max) pdf i
  | i < min   = 0
  | i > max   = 0
  | otherwise = pdf i

-- | Right padding a list.
rPad :: Integer -> c -> [c] -> [c]
rPad !i !e !ls = ls ++ (replicate (fromInteger (toInteger i) - len) e)
  where len = length ls

-- | Left padding a list.
lPad :: Integer -> c -> [c] -> [c]
lPad !i !e !ls = (replicate (fromInteger (toInteger i) - len) e) ++ ls
  where len = length ls

-- ldConv :: [Complex Double] -> [Complex Double] -> [Complex Double]
-- convolve a cLst and pLst to get a cLst for their sum distribution
--
-- baically, a PDF convolved with a CDF is the CDF of the sums of the random
-- variables involved.
ldConv :: Array F DIM1 (Complex Double) -> Array F DIM1 (Complex Double) -> Array F DIM1 Double
ldConv !c !p = {- t -} o
  where
    t =  trace ("c':" ++ ppShow c') . trace ("p':" ++ ppShow p')  . trace ("o':" ++ ppShow (toList o))
    c' = toList c
    p' = toList p
    len :: Array F DIM1 (Complex Double) -> Int
    len a = let (Z :. l) = extent a in l
    cLen = len c
    pLen = len p
    -- The fft library we're using only works on lists that are a power of
    -- two long, so we take the smallest power of 2 strictly larger than the
    -- space we need.
    oLen =  fromInteger . bit $ 2 + log2 (toInteger $ cLen + (2 * pLen) - 2)
    olExt _ = ix1 oLen
    -- You need to pad the CDF with pLen '1's otherwise it convolves with the
    -- 0s that are around the CDF and gets you odd resules.
    -- cPad = fromList (Z :. (fromInteger oLen)) $! 0 : rPad (oLen - 1) 0 (rPad (pLen + cLen) 1 c)
    cPad = computeS $ A.traverse c olExt clGen
    clGen ol z@(Z :. i) | i == 0 = 0
                        | i > 0 && i <= cLen = {- trace (show (i,cLen,ol (ix1 0))) $ -} ol (ix1 $ i - 1)
                        | i > cLen && i <= (cLen + pLen) = 1 :+ 0
                        | otherwise = 0
    -- pPad = fromList (Z :. (fromInteger oLen)) $! rPad oLen 0 p
    pPad = computeS $ A.traverse p olExt plGen
    plGen ol (Z :. i) | i >= 0 && i < pLen = ol (ix1 i)
                      | otherwise = 0
    cFFT = fft cPad
    pFFT = fft pPad
    oFFT = computeS $ cFFT *^ pFFT
    o :: Array F DIM1 Double
    o = computeS $ A.traverse (ifft oFFT) newExt result
    oLen' = cLen + pLen - 1
    -- newExt = id
    result ol (Z :. i) = realPart $ ol (ix1 $ i + 1)
    newExt _ = ix1 oLen'
    -- result ol (Z :. ind) = realPart $ ol (ix1 $ oLen' - ind :: DIM1)

--main :: IO ()
--main = do
--  let cl = [1,1]
--      pl = [0.2,0.2,0.2,0.2,0.2]
--      ca = fromList (ix1 $ length cl) . map (\ x -> x :+ 0) $ cl
--      pa = fromList (ix1 $ length pl) . map (\ x -> x :+ 0) $ pl
--      o = ldConv ca pa
--      ol = zip @Int [0..] $ toList o
--  pPrint $ ol
--  let gen = (<*>) (1 `d` 3)
--  mapM_ (\ i -> putStrLn $ "output(" ++ show i ++ "):" ++ printDist (gen i :: Dist Double Integer)) [1..3]

instance (Ord d, Integral d, Memoizable d, RealFrac p) => Num (Dist p d) where

  (+) df@(Dist _ _ fMin fMax fcLst _) dg@(Dist _ _ gMin gMax _ gpLst)
    = toDist CDF{
      cdf = newFun
    , min = newMin
    , max = newMax
    }
    where
      newCL = ldConv fcLst gpLst
      newMin = fMin + gMin
      newMax = fMax + gMax
      newFun x | newInd x < 0 = 0
               | newInd x >= (let (Z :. x) = extent newCL in x) = 1
               | otherwise =  (P.max 0) . (P.min 1) . fromRational . toRational $ newCL ! (ix1 $ newInd x)
      newInd x = (fromIntegral $ fromIntegral x - newMin)


  (-) a b = a + (negate b)

  (*) = undefined

  negate Dist{..} = toDist CDF{
      cdf = (\ x -> 1 - (cdf $ negate x))
    , min = -max
    , max = -min
    }

  signum Dist{..} = toDist CDF{
      cdf = f
    , min = -1
    , max = 1
    }
    where
      f x | x < -1    = 0
          | x <  0    = cdf (pred 0)
          | x <  1    = cdf 0
          | otherwise = 1

  abs Dist{..} = undefined

  fromInteger i = toDist CDF{
      cdf = (\ x -> if x >= fromInteger i then 1 else 0)
    , min = fromInteger i
    , max = fromInteger i
    }

-- | This gets the highest power of 2 less than or equal to a given number
gpow2 :: Integer -> Integer
gpow2 = bit . log2

-- | this uses a scaled continues approximation of the distribution for rolling
--   multiple dice.
--
--   The formula is from  http://www.math.uah.edu/stat/special/IrwinHall.html
irwinHall  :: forall num dom prob. (Integral num, Bits num, Real dom, Memoizable dom, Fractional prob)
           => num -- Number of Dice
           -> num -- Sides on each Dice
           -> CDF prob dom
irwinHall !n !s = CDF{cdf = sEmbed,min = min,max = max}
  where
    n' :: Integer
    n' = fromIntegral n
    s' :: Integer
    s' = fromIntegral s
    min :: dom
    min = fromIntegral $ n
    max :: dom
    max = fromIntegral $ s * n + 2
    -- sanity wrapper
    sEmbed :: dom -> prob
    sEmbed i | i < min   = 0
             | i >= max   = 1
             | otherwise = embed i
    -- embed the range and divide the output
    embed :: dom -> prob
    embed = memoize (\ i -> fromRational (iw (tfun $ toRational i) n'))
    -- Transform the normal input into the range of the irwinHall distribution
    tfun :: Rational -> Rational
    tfun !i = ((toRational n') * (i - (toRational $ n') + 1)) / (toRational $ (s' * n') - n' + 1)
    -- Standard irwin hall CDF function
    iw :: Rational -> Integer -> Rational
    iw !x !n = (1 % 2) + ((1 % (2 * (factorial . fromInteger $ n))) * (sumTerm x n))
    sumTerm :: Rational -> Integer -> Rational
    sumTerm !x !n = sum $! map (sq x n) [0..n]
    -- All the stuff in the summation term
    sq :: Rational -> Integer -> Integer -> Rational
    sq !x !n !k = (toRational $! ((-1) ^ k) * (n `C.choose` k))
             * (signum $! x - fromInteger k)
             * ((x - fromInteger k) ^ n)

-- This just dives us the nicer "100 `d` 100" style syntax for CDFs and
-- some memoization to prevent huge amounts of overwork.
d :: (Integral dom, Memoizable dom, RealFrac prob)
           => Integer -- Number of Dice
           -> Integer -- Sides on each Dice
           -> Dist prob dom
d !n !s = toDist $ irwinHall n s

-- The maximum of some CDF and a constant.
dMax :: (Integral d,RealFrac p) => d -> Dist p d -> Dist p d
dMax !n Dist{..} = toDist CDF{
    cdf = (\x -> if x < n then 0 else cdf x)
  , min = P.max n min
  , max = P.max n max
  }

-- transform a CDF by multiplying the output by some constant, this just
-- assumes the original CDF is a step function.
--
-- Yes, this means the PDF will be weird and spiky, just deal with it.
dMul :: (Integral d,Real a,RealFrac p) => a -> Dist p d -> Dist p d
dMul !n Dist{..} = toDist CDF{
    cdf = cdf . floor . (\x -> toRational x / toRational n)
  , min = floor (toRational min * toRational n)
  , max = floor (toRational max * toRational n)
  }

-- Add a constant to a CDF
dPlus :: (Integral d,RealFrac p) => d -> Dist p d -> Dist p d
dPlus !n Dist{..} = toDist CDF{
    cdf = cdf . (\ x -> x - n)
  , min = min + n
  , max = max + n
  }

-- Given a specific fraction between 0 and 1 , will just run a binary search
-- on a distribution until it finds the point where the CDF goes over that
-- point
findPercentile :: (Integral d,Ord d) => p -> Dist p d -> d
findPercentile !t Dist{..} | t == 0 = min
                           | t == 1 = max
                           | otherwise = fpHelp (min,max)
  where
    fpHelp (min,max) | min == max = min
                     | (cdf min < t) && (cdf mid >= t) = fpHelp (min,mid - 1)
                     | (cdf mid < t) && (cdf max >= t) = fpHelp (mid + 1,max)
                     | (cdf min >= t) = min
                     | (cdf max <  t) = max
                     | otherwise = error "This should never happen"
      where
        mid = {- trace ("fp:" ++ show (toInteger min,toInteger m',toInteger max))-} m'
        m' = fromInteger $ (toInteger min + toInteger max) `div` 2


-- | Iterated convolution over some CDF in order to find the location we care
--   about.
--
--   Returns a nice memoized function that you should keep handy where possible
(<*>) :: (Integral d, Memoizable d, RealFrac p) => Dist p d -> Integer -> Dist p d
(<*>) c = memoConv
  where
    memoConv = memoize conv
    conv 1 = c
    conv 2 = c + c
    conv !i | i <= 0 = error "can't take 0 or fewer convolutions of CDF"
            | i == gpow2 i = let n = memoConv (i `div` 2) in n + n
            | otherwise    = memoConv (gpow2 i) + memoConv (i - gpow2 i)
-- | The number of research points one expects to get in a single day
--
--   n = # of Sealing Dice
--   t = Daily Sealing Roll Target
--   r = Cumulative Research target
--   c = Current research counter
--   a = number of days worth of porogress
--
--   params n t
--
--   This function takes the number of sealing dice you have, and the daily
--   target and gives you the distribution for expected increase in C
--
--   Expected progress for `a` days is `singleDaysProgress n t <*> a`
singleDaysProgress :: Integer -> Integer -> Dist Double Integer
singleDaysProgress = sdp
  where
    sdp !n !t = (1 / ((n' + (t'/50)) ** 0.65)) `dMul` (dMax 0 (dPlus (-t) (n `d` 100)))
      where
        n' = fromInteger n
        t' = fromInteger t

-- | Slightly more readable wrapper that pops out a nice memozed function that
--   we can pass to other things as needed
--
--   params = n t a
multipleDaysProgress :: Integer -> Integer -> Integer -> Dist Double Integer
multipleDaysProgress n t = (<*>) (singleDaysProgress n t)

-- The number of days needed to get a higher than X chance of completion given
-- a given n t and r. This does a binary search in the range of days that we're
-- looking at, but scales up with powers of two first.
--
-- x = percentage sucess change you want to find the correct set of days for.
--
-- params are x n t r
daysToComplete :: Double -> Integer -> Integer -> Integer -> Maybe Integer
daysToComplete x n t r = dta 1
  where
    -- | function that scales up by 2 each time, looking for a range, since
    --   all the relevant intermediate products are memoized, this is just
    --   doing work that would have to be done anyway.
    dta a | progress > x && a == 1 = Just 1
          | progress > x           = dtc (a `div` 2,a)
          | (a * 2) > maxDays      = dtb a
          | otherwise              = dta (a * 2)
      where
        progress = (1 - (cdf (multipleDaysProgress n t a :: Dist Double Integer) r))
    -- | This one just keeps us from going through a huge pile of intermediate
    --   results in order to find that it takes more than our maximum. I figure
    --   this is going to be a very common outcome when generating a diagram
    --   or table.
    dtb a | progress < x = Nothing
          | otherwise    = dtc (a,maxDays)
      where
        progress = (1 - (cdf (multipleDaysProgress n t maxDays :: Dist Double Integer) r))
    -- | This function does the binary search for the actual point of change,
    --   once we've got a range set up and should skip a lot of useless computing.
    dtc (min,max)
      | min == maxDays && progress < x = Nothing
      | min >= max = Just min
      | progress >= x = dtc (min,mid - 1)
      | progress <  x = dtc (mid,max)
      | otherwise = error "should never reach here"
      where
        mid = (min + 1 + max) `div` 2
        progress = (1 - (cdf (multipleDaysProgress n t mid :: Dist Double Integer) r))

-- 12 weeks is the limit we search, if a project takes more than 3 months
-- our thresholds are too high. We're not going to find a 6 month strech
-- basically ever.
maxDays = 7 * 12

-- The number of days needed to get a higher than X chance of completion given
-- a given n t and r. This does a binary search in the range of days that we're
-- looking at, but scales up with powers of two first.
--
-- but this time allowing you to cache more effectively
--
-- md = function that, when given the day, gives you the distribution for that
--      day.
-- x = percentage sucess change you want to find the correct set of days for.
-- r = target threshold you're looking to pass
--
-- params are md x r
--
--
daysToComplete' :: (Integer -> Dist Double Integer) -> Double -> Integer -> Maybe Integer
daysToComplete' !md !x !r = {-(trace $ "days: " ++ show (x,r))-} dta 1
  where
    -- | function that scales up by 2 each time, looking for a range, since
    --   all the relevant intermediate products are memoized, this is just
    --   doing work that would have to be done anyway.
    dta !a | progress > x && a == 1 = {- t $ -} Just 1
          | progress > x           = {- t $ -} dtc (a `div` 2,a)
          | (a * 2) >= maxDays     = {- t $ -} dtb a
          | otherwise              = {- t $ -} dta (a * 2)
      where
        progress = (1 - (cdf (md a :: Dist Double Integer) r))
        t = trace $ "dta: " ++ show (x,progress,a)
    -- | This one just keeps us from going through a huge pile of intermediate
    --   results in order to find that it takes more than our maximum. I figure
    --   this is going to be a very common outcome when generating a diagram
    --   or table.
    dtb !a | progress < x = {- t $ -} Nothing
          | otherwise    = {- t $ -} dtc (a,maxDays)
      where
        progress = (1 - (cdf (md maxDays :: Dist Double Integer) r))
        t = trace $ "dtb: " ++ show (x,progress,a)
    -- | This function does the binary search for the actual point of change,
    --   once we've got a range set up and should skip a lot of useless computing.
    dtc !(min,max)
      | min + 1 == max && progress > x = {- t $ -} Just mid
      | min + 1 == max && progress < x = {- t $ -} Just max
      | min == maxDays && progress < x = {- t $ -} Nothing
      | mid >= max && progress > x     = {- t $ -} Just mid
      | progress >= x                  = {- t $ -} dtc (min,mid)
      | progress <  x                  = {- t $ -} dtc (mid,max)
      | otherwise                      = {- t $ -} error "DaysToComplete is broken"
      where
        mid = (min + 1 + max) `div` 2
        progress = (1 - (cdf (md mid :: Dist Double Integer) r))
        progressmin = (1 - (cdf (md min :: Dist Double Integer) r))
        progressmax = (1 - (cdf (md max :: Dist Double Integer) r))
        t = trace $ "dtc: " ++ show ((min,progressmin),(mid,progress),(max,progressmax))

-- | The probability of success thresholds we're looking for when given a
--   sealing dice x daily target x number of days (research target -> prob)
psThresholds :: [Double]
psThresholds = [0,0.025..1]

-- | Datastructure for a probability of success threshold query , basically
--   just so we can derive nice Show and Read instances for this
data PS p d = PS {
      sealingDice :: !Integer
    , dailyTarget :: !Integer
    , numDays :: !Integer
    , probOfTarget :: ![(d,p)]
    } deriving (Show,Read,Generic,FromJSON,ToJSON)


-- | Type we're using for prettier JSON output
data PSJ p d = PSJ {
    numDays :: !Integer
  , dataPoints :: ![PSE p d]
  } deriving (Show,Read,Generic,FromJSON,ToJSON)

-- This is the type we're using to get prettier JSON output for the pairs of
-- researchTargets and Probility of sucess
data PSE p d = PSE {
    researchTarget :: !d
  , probabilityOfSuccess :: !p
  } deriving (Show,Read,Generic,FromJSON,ToJSON)


psToPSJ :: (Ord d,Ord p) => PS p d -> PSJ p d
psToPSJ !PS{..} = PSJ{
    numDays = numDays
  , dataPoints = map (\ (rt,ps) -> PSE rt ps)  probOfTarget
  }

-- | Given a bunch of information, generate a PS structure for a set of known
--   parameters.
calculatePS :: (Integer,Integer) -> Integer
            -> (Integer -> Dist Double Integer)
            -> PS Double Integer
calculatePS !(sealingDice,dailyTarget) !numDays !distGen
  = PS sealingDice dailyTarget numDays probOfTarget
  where
    -- The Distribution for the paticular day
    dayDist :: Dist Double Integer
    dayDist = distGen numDays
    getRT p = findPercentile p dayDist
    getPair p = (rt,1 - tp)
      where
        -- | Research Target
        rt = getRT p
        -- | True Percent
        tp = cdf (dayDist :: Dist Double Integer) rt
    probOfTarget = rmdups $ map getPair psThresholds

-- | Gets the minimum target in the PS
minTarget :: Ord d => PS p d -> d
minTarget = minimum . map fst . probOfTarget

-- | Gets the maximum target in the PS
maxTarget :: Ord d => PS p d -> d
maxTarget = maximum . map fst . probOfTarget

-- | Figure out an interesting set of research targets when given a list of
--   PS querys. first a bunch of things between the 0 and the minimum we
--   find, and then a whole pile of increments in the range that's more
--   interesting. This just gets us a full range of useful output.
getRTList :: (Show d, Show p, Ord d,Integral d) => [PS p d]-> [d]
getRTList !pl = {- t . -} rmdups $ [0,zDivs..min] ++ [min,min+inc..max] ++ [max]
  where
    t = trace ("foo:" ++ show (pl, min, max, inc, zInc))
    min  = minimum . map minTarget $ pl
    max  = maximum . map maxTarget $ pl
    divs = 40
    inc  = P.max 1 $ (max - min) `div` divs
    zDivs = 20
    zInc = P.max 1 $  min `div` zDivs

-- | Datastructure for DaysToComplete queries, this is just a convinient
--   way to get nice read and show instances for this stype of information.
--   That way others can work with it too.
data DC p d = DC {
    sealingDice :: !Integer
  , dailyTarget :: !Integer
  , researchTarget :: !Integer
  , probOfNumDays :: ![(Integer,p)]
  } deriving (Show,Read,Generic,FromJSON,ToJSON)


data DCJ p d = DCJ {
    researchTarget :: !Integer
  , dataPoints :: ![DCE p d]
  } deriving (Show,Read,Generic,FromJSON,ToJSON)

data DCE p d = DCE {
    numDays :: !Integer
  , probabilityOfSuccess :: !p
  }  deriving (Show,Read,Generic,FromJSON,ToJSON)

dcToDCJ :: (Ord d,Ord p) => DC p d -> DCJ p d
dcToDCJ !DC{..} = DCJ{
    researchTarget = researchTarget
  , dataPoints = map (\ (nd,pr) -> DCE nd pr)  probOfNumDays
  }

calculateDC :: (Integer,Integer) -> Integer
            -> (Integer -> Dist Double Integer)
            -> DC Double Integer
calculateDC !(sealingDice,dailyTarget) !researchTarget !distGen
  = DC sealingDice dailyTarget researchTarget probOfNumDays
  where
    getDays :: Double -> Maybe Integer
    getDays p = daysToComplete' distGen p researchTarget
    -- just get the actual probability for a particular day
    getPair p = (prob <$>) $! dayOf
      where
        dayOf = getDays p
        prob d = (d,1 - cdf (distGen d :: Dist Double Integer) researchTarget)
    -- Go through each day and get research thresholds for it
    probOfNumDays = rmdups . catMaybes . map getPair $ [0.001] ++ [0.025,0.05..0.975] ++ [0.999]
    -- -- Find the days to get 1/10th of 1% probability of success
    -- minDay :: Maybe Integer
    -- minDay = getDays 0.001
    -- -- Find the days to get 1/10th of 1% probability of failure
    -- maxDay :: Maybe Integer
    -- maxDay = Just . fromMaybe maxDays $ getDays 0.999
    -- -- list of days we're going to search
    -- allDays :: [Maybe Integer]
    -- allDays = map Just . fromMaybe [] $ (\ a b -> [a..b]) <$> minDay P.<*> maxDay
    -- -- just get the actual probability for a particular day
    -- getPair dayOf = prob <$> dayOf
    --   where
    --     prob d = (d,1 - cdf (distGen d :: Dist Double Integer) researchTarget)
    -- -- Go through each day and get research thresholds for it
    -- probOfNumDays = rmdups . catMaybes . map getPair $ allDays

-- | Get a list of interesting numbers of days to have researched
researchDays :: [Integer]
researchDays = [1..maxDays] -- rmdups $ [1..7] ++ [10,15..maxDays] ++ [maxDays]

data GStore p d = GStore {dice :: Map Integer (GS1 p d)}
  deriving (Show,Read,Generic,Eq,Ord,FromJSON,ToJSON)

data GS1 p d = GS1 {difficulty :: Map Integer (GS2 p d)}
  deriving (Show,Read,Generic,Eq,Ord,FromJSON,ToJSON)

data GS2 p d = GS2 {target :: Map d [(Integer,p)],days :: Map Integer [(d,p)]}
  deriving (Show,Read,Generic,Eq,Ord,FromJSON,ToJSON)

type IOStore = IORef (GStore Double Integer)

emptyGS :: GStore p d
emptyGS = GStore $ Map.empty

addPS :: GStore Double Integer -> PS Double Integer -> GStore Double Integer
addPS GStore{..} PS{..} = GStore $ Map.alter alt1 sealingDice dice
  where
    alt1 Nothing        = Just . GS1 $ Map.singleton dailyTarget (fromJust $ alt2 Nothing)
    alt1 (Just GS1{..}) = Just . GS1 $ Map.alter alt2 dailyTarget difficulty
    alt2 Nothing = Just $ GS2{
        target = Map.empty
      , days = Map.singleton numDays probOfTarget
      }
    alt2 (Just GS2{..}) = Just $ GS2 {
        target = target
      , days = Map.insert numDays probOfTarget days
    }

addDC :: GStore Double Integer -> DC Double Integer -> GStore Double Integer
addDC GStore{..} DC{..} = GStore $ Map.alter alt1 sealingDice dice
  where
    alt1 Nothing        = Just . GS1 $ Map.singleton dailyTarget (fromJust $ alt2 Nothing)
    alt1 (Just GS1{..}) = Just . GS1 $ Map.alter alt2 dailyTarget difficulty
    alt2 Nothing = Just $ GS2{
        target = Map.singleton researchTarget probOfNumDays
      , days = Map.empty
      }
    alt2 (Just GS2{..}) = Just $ GS2 {
        target = Map.insert researchTarget probOfNumDays target
      , days = days
    }

addPSs :: [PS Double Integer] -> GStore Double Integer -> GStore Double Integer
addPSs = flip $ foldl' addPS

addDCs :: [DC Double Integer] -> GStore Double Integer -> GStore Double Integer
addDCs = flip $ foldl' addDC

addPSDC :: ([PS Double Integer],[DC Double Integer]) -> GStore Double Integer -> GStore Double Integer
addPSDC (pss,dcs) = addPSs pss . addDCs dcs

-- | Given a number of sealing dice and a daily threshold, generate a number
--   of interesting DC and PS queries,
printPSDC :: Maybe IOStore -> (Integer,Integer) -> IO ([PS Double Integer],[DC Double Integer])
printPSDC gs !setPair@(numDice,dailyThresh) = do
  let !distGen = multipleDaysProgress numDice dailyThresh
  pss <- mapM (genPrintPS distGen) researchDays
  let !researchTargets = getRTList pss
  dcs <- mapM (genPrintDC distGen) researchTargets
  let psdc = (pss,dcs)
  sequence $ flip modifyIORef (addPSDC psdc) <$> gs
  return psdc
  where
    genPrintPS !distGen !rd = do
      let ps = calculatePS setPair rd distGen
      --print dc
      putStrLn $ "ps: " ++ show (setPair,rd)
      return ps
    genPrintDC !distGen !nd = do
      let dc = calculateDC setPair nd distGen
      -- when (probOfNumDays dc /= []) $ print dc
      putStrLn $ "dc: " ++ show (setPair,nd)
      return dc

writePSDC :: (Integer,Integer)
          -> ([PS Double Integer],[DC Double Integer])
          -> IO ()
writePSDC !pair@(sealingDice,dailyThresh) !(pss,dcs) = do
  createDirectoryIfMissing False dir
  BS.writeFile file $ encodePretty jsonBlob
  where
    dir = "out/"
    file = dir ++ "sealingCalcs" ++ show pair ++ ".json"
    jsonBlob = object [
        "sealingDice" .= sealingDice
      , "dailyReseachThreshold" .= dailyThresh
      , "Probability of Success Calculations" .= map psToPSJ pss
      , "Days to Completion Calculations" .= map dcToDCJ dcs
      ]

-- Given a number of dice figure out a number of interesting daily thresholds
--
-- param "number of sealing dice"
--
getDailyThresholds :: Integer -> [Integer]
getDailyThresholds !nd = rmdups $ zList ++ [ndMin] ++ pList ++ [ndMax]
  where
    dist = nd `d` 100
    -- With nDice the probability of getting fewer than nMin is basically 0
    ndMin = getLastZero' (dist :: Dist Double Integer)
    -- With nDice the probability of getting nore than nMax is basically 0
    ndMax = getFirstOne' (dist :: Dist Double Integer)
    -- number of daily thresholds we're going to be checking in the range
    -- [0..ndMin], where the probability of getting more is basically 100 %
    zDivs = 20
    -- increment in the z range
    zInc = P.max 1 $ ndMin `div` zDivs
    -- List of thresholds to check in the z range
    zList = [0,zInc..ndMin]
    -- for the p range, we're going to get numbers of dice that which have a
    -- p chance of failing outright and not progressing any research.
    pProbs = [0,1/40..1]
    pList = map (flip findPercentile dist) pProbs

-- For a given number of sealing dice, figure out a bunch of interesting
-- thresholds to test and then generate all the neccesary distributions
genForNumDice :: Maybe IOStore -> Integer -> IO ()
genForNumDice gs sealingDice = do
  let !thresholds = getDailyThresholds sealingDice
      !settingPairs = map (\ dt -> (sealingDice,dt)) thresholds
  mapM_ runPSDC settingPairs
  where
    runPSDC settingPair = printPSDC gs settingPair >>= writePSDC settingPair

-- Generate all the PS and DC data we want.
genAndWritePSDC :: IO ()
genAndWritePSDC = do
  gs <- newIORef emptyGS
  mapM_ (genForNumDice $ Just gs) [10..70]
  finalStore <- readIORef gs
  BS.writeFile "out/allData.json" $ encodePretty finalStore
  BS.writeFile "out/allData.min.json" $ encode finalStore



-- | Data type for the storage of plotdata for "sealing lvl -> (D,R -> T)"
--   plots
type EstTimeMap = Map Integer EstTimePlot
data EstTimePlot = EstTimePlot {
  -- Y axis
    diffs :: ![Integer]
  -- x axis
  , totals :: ![Integer]
  -- Plotdata
  , estDays :: ![[Integer]]
  , variance :: ![[Integer]]
  } deriving (Show,Read,Generic,Eq,Ord,FromJSON,ToJSON)

-- | For a given number of sealing dice, get the list of difficulties
--   we're looking for
getDiffs :: Integer -> [Integer]
getDiffs numDice = [0,zInc..ndMax]
  where
    dist = numDice `d` 100
    -- With nDice the probability of getting nore than nMax is basically 0
    ndMax = findPercentile 0.9 (dist :: Dist Double Integer)
    -- number of daily thresholds we're going to be checking in the range
    -- [0..ndMin], where the probability of getting more is basically 100 %
    zDivs = 200
    -- increment in the z range
    zInc = P.max 1 $ ndMax `div` zDivs

-- | For a given number of dice get the list of reasonable research targets
getTotals :: Integer -> [Integer]
getTotals numDice = rmdups $ [1] ++ [2,4..200] ++ [200, 200 + rInc..rMax]
  where
    dist = multipleDaysProgress numDice 0 maxDays
    rMax = findPercentile 0.6 (dist :: Dist Double Integer)
    rDivs = 200
    rInc = P.max 1 $ rMax `div` rDivs

getEstTimePlot :: Integer -> EstTimePlot
getEstTimePlot numDice = EstTimePlot{
    diffs = {- trace ("for diffs " ++ show diffs) -} diffs
  , totals = {- trace ("for totals " ++ show totals) -} totals
  , estDays = estDays
  , variance = variance
  }
  where
    diffs = getDiffs numDice
    totals = getTotals numDice
    -- get all rows
    (estDays,variance) = unzip $ map getSingDiff diffs
    -- Get the row for a single difficulty
    getSingDiff :: Integer -> ([Integer],[Integer])
    -- The trace is here so I can see progress, but it's an otherwise pure
    -- function, :V medium bad practice I suppose.
    getSingDiff diff = {- trace ("for difficulty " ++ show diff) $ -} (estList,varList)
      where
        distGen = multipleDaysProgress numDice diff
        (estList,varList) = unzip $ map tp totals
          where
            tp t = let e5 = ed 0.5 t in (e5,if (e5 == -1) then -1 else P.max (e5 - ed 0.05 t) (ed 0.95 t - e5))
        -- Number of days to some percentage with >max just set to -1
        ed p t = fromMaybe (-1) $ daysToComplete' distGen p t

-- Generate the full pile fo estimated time plot sas needed.
genAndWriteEstTimePlot :: IO ()
genAndWriteEstTimePlot = do
  etpL <- mapM (\ nd -> (nd,) <$> getSingleETP nd) [10,15..70]
  createDirectoryIfMissing False dir
  let ets = Map.fromList etpL
  BS.writeFile (dir ++ "estTimeData.json") $ encodePretty ets
  BS.writeFile (dir ++ "estTimeData.min.json") $ encode ets
  where
    dir = "out/"
    getSingleETP :: Integer -> IO (EstTimePlot)
    getSingleETP numDice = do
      putStrLn $ "Beginning generating ETP for Sealing Lvl" ++ (show numDice)
      let !etp = getEstTimePlot numDice
      print etp
      return etp

-- | The code that's actually run when we execute the program
main :: IO ()
main = genAndWriteEstTimePlot

-- So we've got the following variables :
--
--  -- | Research points these are what we accululate as we work.
--  type Points = Int
--
--  -- | Days of work on the project (1 is start, T is curent)
--  type Day = Int
--
--  numDice :: Int
--  numDice := Level of sealing skill / Number of Sealing Dice
--    - Always Known
--
--  diff :: Int
--  diff := Project Difficulty
--    - Hidden Parameter
--    - Have priors P(diff)
--
--  total :: Points
--  total := Total research points needed to complete project
--    - Hidden Parameter
--    - Have priors P(total)
--
--  date :: Day
--  date := Time Spent on specific project (days)
--    - Always known
--
--  roll :: Day -> Int
--  roll d := Sealing roll on day d
--  roll d = sample (asSeed d) $ n `d` 100
--    - Possibly visible?
--    - Can easily get P(roll|numDice,diff)
--
--  effort :: Day -> Int
--  effort d := Effort put towards sealing reseach on day d
--  effort d = max(0, roll t - diff)
--    - Possibly visible?
--    - Can easily get P(effort|numDice,diff)
--
--  inc :: Day -> Points
--  inc d := amount the project counter is incremented by on day d
--  inc d = (effort t) / (numDice - diff/50)^0.65
--    - Possibly visible?
--    - Can easily get P(inc|numDice,diff)
--
--  progress :: Day -> Points
--  progress d := total progress on research project by end-of-day d
--  progress d = sum [inc d' | d' <- [1..d]]
--    - Possibly visible?
--    - Can easily get P(progress|d,numDice,diff)
--
--  finished :: Day -> Bool
--  finished d := Is the project done by end-of-day d
--  finished d = progress d >= total
--    - Always Known
--    - Can easily get P(finished d|numDice,diff,total)
--
-- Bayes Law:
--
--  P(A|B) = P(A)* P(B|A)/P(B)
--
-- Case 1: We don't get any additional information.
--
--  Known:
--    - numDice
--    - date
--    - (finished d == false) `forall` 1 <= d <= date
--
--    - P(diff,total@0) = P(diff) * P(total)
--    - P(diff,total@x) =
--          P(diff,total@x-1)
--        * P(finished x|diff,total@x-1)
--        / P(finished x@x-1)
--
--    - P(finished d@n) = forall diff
--
--
--    - P(diff,total|d=0) = P(diff,total)
--    - P(diff,total|d=x) = P(diff,total|d=x-1,finished x = false)
--                        = P(diff,total|d=x-1) *
--                          (  P(finished x = false|d=x-1,diff,total)
--                           / P(finished x = false|d=x-1))
--    - P(finished 0) = 0
--    - P(finished x|d=n) = P(finished x|numDice,
--
--  (d = 0) = empty-set
--  (d = x) = d=x-1,finished x == false
--
--  Want:
--    - P(diff,total|d=date)
--
-- Proposal 1;
--
--  proxyRoll :: Day -> Int
--  proxyRoll d := Hidden die roll made for estimating time to completion
--  proxyRoll d = sample (asSeed d) $ n d 100
--    - Hidden Parameter
--    - Can easily get P(proxyRoll|numDice,diff)
--
--  proxyEffort :: Day -> Int
--  proxyEffort d := Estimated daily effort put towards sealing reseach on day d
--  proxyEffort d = max(0, proxyRoll t - diff)
--    - Hidden Parameter
--    - Can easily get P(proxyEffort|numDice,diff)
--
--  proxyInc :: Day -> Points
--  proxyInc d := Estimated amount the project counter is incremented by on day d
--  proxyInc d = (proxyEffort t) / (numDice - diff/50)^0.65
--    - Possibly visible?
--    - Can easily get P(proxyInc|numDice,diff)
--
--  estimated :: Day -> Either Day Infinity
--  estimated d := Estimated time to project completion using proxy roll
--  estimated d = (total - finished d) / (proxyInc d)
--    - Known
-- We can calculate
-- We always know:
--
--  - N = Number of sealing die
--  - T = Time spent on project
--  - S = Is the project complete or not?
--
--
-- We want to predict:
--
--  - D = Project Difficulty
--  - R = Research Threshold
--
-- We might also have access to:
--
--  - L := Each day's roll for Max(0, Nd100 - D)
--    - Only unknown variable is D.
--    - Cannot provide information on R
--    - Is a pretty easy distribution to work with in order to figure out D
--  - C := Each day's addition to the progress counter
--    - Only dependent on D
--    - Cannot provide informatio on R
--    - Can
--
-- Key questions:
--
--  - How does choice of D & R affect time to complete a seal?
--  - How does my ability to complete a project change as my level changes?
--  - How
--
--
-- Notation for plots:
-- (Fixed Variables) -> (Inependent Variables) -> (Dependent Variables)
--
--
--

--- Leftover code from various tests of main :V
----let pair = (10,888) in printPSDC pair >>= writePSDC pair
  -- let cl = [1]
  --     pl = [0.2,0.2,0.2,0.2,0.2]
  --     ca = fromList (ix1 $ length cl) . map (\ x -> x :+ 0) $ cl
  --     pa = fromList (ix1 $ length pl) . map (\ x -> x :+ 0) $ pl
  --     o = ldConv ca pa
  --     ol = zip @Int [0..] $ toList o
  -- pPrint $ ol
  -- let gen = (<*>) (1 `d` 3)
  -- mapM_ (\ i -> putStrLn $ "output(" ++ show i ++ "):" ++ printDist (gen i :: Dist Double Integer)) [80]
  -- let dayGen = (multipleDaysProgress 10 2)
  -- print $ calculateDC (10,2) 4732 dayGen
  -- mapM_ (\ x -> print (x,cdf (dayGen x :: Dist Double Integer) 4732)) [32..64]
  -- let gen = (<*>) (1 `d` 10)
  -- mapM_ (\ i -> putStrLn $ "output(" ++ show i ++ "):" ++ printDist (gen i :: Dist Double Integer)) [1..3]

  --- print $ min (singleDaysProgress 20 1000 :: Dist Double Integer)
  -- print $ max (multipleDaysProg:w
  -- ress 20 1000 :: Dist Double Integer)
  -- print @[(Integer,Double)] $ map (\x -> (x,cdf (singleDaysProgress 20 1000 :: Dist Double Integer) x)) [-5..95]
  --print @[(Integer,Double)] $ map (\x -> (x,cdf (multipleDaysProgress 20 1000 2 :: Dist Double Integer) x)) [-5,-3..200]
--   where
--    c = multipleDaysProgress 70 100 20
--    getData :: [T Double Integer]
--    getData = do
--      sd <- [10,15..60]
--      dt <- 1 : [20,40..80] ++ [0,100..6000]
--      nd <- 1 : [8,16..80]
--      ct <- [1..19] ++ [20,40..100] ++ [200,400..5000] ++ [5500,6000..10000]
--      let p = 1 - cdf (multipleDaysProgress sd dt nd :: Dist Double Integer) ct
--      return $ T sd dt nd ct p


