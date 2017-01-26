

So I want to do a quick analysis of the current sealing tool. 

TODO :: 

 > {-# LANGUAGE DuplicateRecordFields,RecordWildCards,TemplateHaskell #-}

> {-# LANGUAGE RecordWildCards,TemplateHaskell #-}

> {-# LANGUAGE FlexibleInstances,TypeApplications #-}



> module Main where

We're only going to be working with rational number so let's just use the 
existing implementation.   

> import Data.Ratio  
> import Data.Bits
> import Crypto.Number.Basic (log2)
> import qualified Math.Combinatorics.Exact.Binomial as C
> import Math.Combinatorics.Exact.Factorial

> import Numeric.Probability.Random hiding (print) 
> import qualified Numeric.Probability.Random as Rand
> import Numeric.Probability.Object
> import Numeric.Probability.Simulation

> import qualified Numeric.Probability.Distribution as Dist

Because many of our functions are doing to be called repeatedly and are 
recursive, memoizing our functions will save us a lot of time. 

> import Data.Function.Memoize
> import Foreign.C.Types


We need bounded integers for memoization but we want something nice and large
that can cover the full range of 

> instance Bounded (Rational) where 
>   maxBound = 2 ^ 64 % 1 
>   minBound = -2 ^ 64 % 1 

> instance Memoizable (Rational) where memoize = memoizeFinite

The type of Probability Distribution Functions over an integral parameter 
We assume that `f` is a PDF such that `f x == 0` for all `x < min || x > max`
and that the sum of all values in that range is basically 1 (floating point errors :C )

> data PDF = PDF {pfun :: Integer -> Rational, pmin :: Integer, pmax :: Integer}

 > deriveMemoizable ''PDF

The type of Cumulative Distribution Funtions over an integral parameter
We assume that `f` is a CDF such that `x < min -> f x == 0`, `x > max -> f x == 1`,
that the function is monotonically increasing and bounded between 0 and 1

> data CDF = CDF {cfun :: Integer -> Rational, cmin :: Integer, cmax :: Integer}

 > deriveMemoizable ''CDF


var d100 = {fun: x => (x > 100 || x < 1) ? 0 : 1/100, min: 1, max: 100}

> -- | The PDF for a uniform die with n sides. 
> die :: Integer -> PDF 
> die n = PDF { pfun = df, pmin = 1, pmax = n }
>   where
>     df :: Integer -> Rational
>     df x | x >= 1 && x <= n = 1 % n
>          | otherwise        = 0 

> d100 :: PDF 
> d100 = die 100 


// Converts a PDF to a CDF by summing over elements 
// toCDF :: boundedPDF -> boundedCDF 
var toCDF = ({fun: f, min: fMin, max: fMax}) => {
  
  // A memoized function that 
  var cdf = memoize((x) => {
    // Short circuit around the out of bounds cases
    if (x < fMin) { return 0; } 
    else if (x>fMax) { return 1; } 
    else { return f(x) + cdf(x - 1); }
  });
  
  // 'prime' the function by calculating every value :V
  // because javascript is a shitty programming language 
  // that won't just let me use recursion which would be
  // much more efficient, if a bit heavy on the stack. 
  //
  // TODO :: Test whether you can rewrite the CDF function
  // as something that's tail call recursive and let an 
  // optimization remove the stack thrashing. Alternately
  // just manually inplement memoization in a way that 
  // lets you find the uncalculated potion and just capture
  // the solution in a for loop. 
  for(var i = fMin; i <= fMax; i++) {cdf(i)};
  
  // Pair function with bounds before returning. 
  return {fun: cdf, min: fMin, max: fMax}
}

> toCDF :: PDF -> CDF 
> toCDF PDF{..} = CDF {cfun = mcdf
>                     ,cmin = pmin
>                     ,cmax = pmax}
>   where
>     mcdf :: Integer -> Rational
>     mcdf = memoize cdf 
>     cdf :: Integer -> Rational
>     cdf x | x < pmin = 0 
>           | x > pmax = 1
>           | otherwise = pfun x + mcdf (x - 1)
> 

> toPDF :: CDF -> PDF 
> toPDF CDF{..} = PDF {pfun = mpdf
>                     ,pmin = cmin
>                     ,pmax = cmax}
>   where
>     mpdf :: Integer -> Rational
>     mpdf = memoize pdf 
>     pdf :: Integer -> Rational
>     pdf x | x < cmin = 0 
>           | x > cmax = 0
>           | otherwise = cfun x - cfun (x - 1)
>

// The convolution of two PDF for two independent random variables is the PDF of the sum
// of those same random variables. 
// convolve :: boundedPDF -> boundedPDF -> boundedPDF
var convolve = ({fun: f, min: fMin, max: fMax},{fun: g, min: gMin, max: gMax}) => { return {
    fun: memoize((x) => {
      var i = 0; 
      var tMin = max(fMin,x - gMax);
      var tMax = min(fMax,x - gMin);
      for(var t = tMin;t <= tMax;t++){
        i += f(t) * g(x - t)
      }
      return i; 
    })
  , min: (fMin + gMin)
  , max: (fMax + gMax) 
}}

> convolve :: PDF -> PDF -> PDF 
> convolve (PDF f fMin fMax) (PDF g gMin gMax) = PDF mo (fMin + gMin) (fMax + gMax) 
>   where
>     mo :: Integer -> Rational
>     mo = memoize o 
>     o :: Integer -> Rational
>     o x = sum $ map (\ t -> f t * g (x - t)) [max fMin (x - gMax)..min fMax (x - gMin)]

// This function gets you the greatest power of 2 that's less than the input, it's undefined 
// if the input is less than 1. 
//
// gpow2 :: Integer -> Integer
var gpow2 = x => 1 << Math.floor(Math.log2(x));

> gpow2 :: Integer -> Integer 
> gpow2 = bit . log2
 
// The iterated convolution of a PDF for a random variable is the random variable for the 
// sum of N independent random variables. For example iterConv(50,d100) is the PDF for the
// sum of 50 d100s. 
// 
// iterConv :: Integer -> boundedPDF -> BoundedPDF
var iterConv = (n,pdf) => {
  const lconv = memoize((n,pdf) => {
    if (n < 1) { return undefined; }
    else if (n == 1) { return pdf; }
    else if (n == 2) { return convolve(pdf,pdf)}
    // Like exponentiation we can nest iterated convolution 
    // iterConv(a,iterConv(b,pdf)) == iterConv(a * b,pdf)
    else if (n == gpow2(n)) {return iterConv(2,iterConv(n/2,pdf))}
    // We can do this because iterated convolution is distributive over convolution
    // in the same way exponentiation is distributive over multiplcation i.e.
    // forall a,b. iterConv(a + b,pdf) == conv(iterConv(a,pdf),iterConv(b,pdf))
    // We use powers of two here because it's convinient and should lead to 
    // maximal reuse of information.
    else { 
      var p1 = iterConv(gpow2(n),pdf);
      var p2 = iterConv(n - gpow2(n),pdf); 
      return convolve(p1,p2);
    }
  })
  
  // same priming as before 
  for(var p = 1;p <= 1;p++){
    lconv(1 << p,pdf); 
  }
  
  return lconv(n,pdf);
};

> iterConv :: Integer -> PDF -> PDF 
> iterConv n p@(PDF f fMin fMax) = mic n
>   where
>     mic = memoize ic
>     ic n | n == 1       = p 
>          | n == 2       = p `convolve` p
>          | n == gpow2 n = (\ p -> convolve p p) $ mic (n `div` 2) 
>          | otherwise    = (mic $ gpow2 n) `convolve` (mic $ n - gpow2 n)

> toCFloat :: Rational -> CFloat 
> toCFloat = fromRational . toRational

https://en.wikipedia.org/wiki/Irwin%E2%80%93Hall_distribution

--> irwinHall :: Integer -- Number of Dice 
-->           -> Integer -- Sides on each Dice
-->           -> PDF 
--> irwinHall n s = PDF san n (s * n) 
-->   where
-->     -- sanitywrapper 
-->     san i | i < n || i > (s * n) = 0
-->           | otherwise = emb i 
-->     memb = memoize emb 
-->     -- embed the range and divide the output 
-->     emb :: Integer -> Rational 
-->     emb i = (iw (tfun i) n) / (fromInteger $ s) 
-->     -- Transform the normal input into the range of the irwinHall distribution
-->     tfun :: Integer -> Rational 
-->     tfun i = (i - n) % (s - 1)
-->     -- Standard irwin hall function
-->     iw :: Rational -> Integer -> Rational
-->     iw x n   = (1 % (2 * (factorial $ fromInteger (n - 1)))) * (sum $ map (sq x n) [0..n])
-->     -- All the stuff in the summation term 
-->     sq :: Rational -> Integer -> Integer -> Rational
-->     sq x n k = (fromInteger $ ((-1) ^ k) * (n `choose` k)) 
-->              * (sign $ x - (fromInteger k)) 
-->              * ((x - (fromInteger k)) `ratPow` (n - 1))
-->     -- Unwrap and wrap a rational so you can take a power of it 
-->     ratPow :: Rational -> Integer -> Rational 
-->     ratPow b e = (numerator b ^ e) % (denominator b ^ e)
-->     -- The standard sign function 
-->     sign x | x < 0  = -1
-->            | x > 0  = 1
-->            | x == 0 = 0


same as previous but using the CDF function instead to get a better estimate
of actual probability, taken from http://www.math.uah.edu/stat/special/IrwinHall.html

> irwinHall  :: Integer -- Number of Dice 
>            -> Integer -- Sides on each Dice
>            -> CDF 
> irwinHall  n s = CDF emb n (s * n) 
>   where
>     -- sanitywrapper 
>     san i | i < n || i > (s * n) = 0
>           | otherwise = emb i 
>     memb = memoize emb 
>     -- embed the range and divide the output 
>     emb :: Integer -> Rational 
>     emb i = (iw (tfun i) n) 
>     -- Transform the normal input into the range of the irwinHall distribution
>     tfun :: Integer -> Rational 
>     tfun i = (n * (i - n + 1)) % (s*n - n + 1) 
>     -- Standard irwin hall CDF function
>     iw :: Rational -> Integer -> Rational
>     iw x n   = (1 % 2) + 
>       ((1 % (2 * (factorial $ fromInteger n))) * (sum $ map (sq x n) [0..n]))
>     -- All the stuff in the summation term 
>     sq :: Rational -> Integer -> Integer -> Rational
>     sq x n k = (fromInteger $ ((-1) ^ k) * (n `C.choose` k)) 
>              * (sign $ x - (fromInteger k)) 
>              * ((x - (fromInteger k)) `ratPow` n)
>     -- Unwrap and wrap a rational so you can take a power of it 
>     ratPow :: Rational -> Integer -> Rational 
>     ratPow b e = (numerator b ^ e) % (denominator b ^ e)
>     -- The standard sign function 
>     sign x | x < 0  = -1
>            | x > 0  = 1
>            | x == 0 = 0


> d :: Integer -> Integer -> CDF 
> d = irwinHall 




-- > plusC :: PDF -> Integer -> PDF 
-- > plusC PDF{..} i = PDF (((+) $ fromInteger i) . pfun) (pmin + i) (pmax + i) 
-- 
-- > minusC :: PDF -> Integer -> PDF 
-- > minusC p i = plusC p (-i)
-- 
-- > maxC :: PDF -> Integer -> PDF 
-- > maxC p@PDF{..} i | i >= pmin && i <= pmax = PDF nf i pmax
-- >                  | i > pmax               = PDF cf i i
-- >                  | otherwise              = p 
-- >   where 
-- >     cf x | x == i = 1
-- >          | otherwise = 0 
-- >     nf x | x == i    = cfun (toCDF p) i 
-- >          | x < i     = 0 
-- >          | otherwise = pfun x 
-- 
-- > timesC :: PDF -> Rational -> PDF 
-- > timesC p c = PDF pf rmin rmax 
-- >   where
-- >     (CDF cfun cmin cmax) = toCDF p 
-- >     rmin = floor (fromInteger cmin * c)
-- >     rmax = ceiling (fromInteger cmax * c) 
-- >     pf x | x < rmin = 0 
-- >          | x > rmin = 0 
-- >          | otherwise = (cfun (base + 1) - cfun base) / c 
-- >       where base = floor (fromInteger x * c)
-- 
-- > type Dist = T
-- 
-- just a thing to generate summed die distributions 
-- 
-- > d :: Integer -> Integer -> Dist Integer 
-- > d n s = fromFrequencies $ freqs 
-- >   where PDF fun min max = irwinHall n s
-- >         freqs = map (\ i -> (i, fromRational $ fun i)) [min..max+1] 
-- 
-- 
-- > d' = d 
-- 
-- the daily progress for sealing 
-- 
-- > progress :: Integer -> Integer -> Dist Integer
-- > progress n t =  do 
-- >   roll <- n `d'` 100
-- >   let n' = toRational n 
-- >       t' = toRational t
-- >       roll' = toRational roll
-- >   return . floor $ (max 0 (roll' - t')) / (n' + (t' / 50))
-- 
-- > progress' = memoize progress
-- 
-- simulate progress and return how many days till success occours 
-- 
-- > research :: Integer -> Integer -> Integer -> Dist (Maybe Integer) 
-- > research = rp 0 0
-- >   where 
-- >     maxDays = 60
-- >     rp :: Integer -> Integer -> Integer -> Integer -> Integer -> Dist (Maybe Integer)
-- >     rp c a n r t 
-- >       | a >  maxDays = return Nothing 
-- >       | c >= r       = return $ Just a 
-- >       | otherwise    = do
-- >          c' <- (progress' n t)
-- >          rp (c + c') (a + 1) n r t

> main :: IO ()
> main = print "test"


>  --print $ map (\ i -> -1 ^ i) [0..5] 
>  --putStr . unlines $ map (show . exfun) [45]
>  -- print $ sum ( map ((\ (_,_,f) -> f) . exfun) [0..5003])
>  -- where
>  --   exfun i = (i,cf) -- (i,lf,cf,df)
>  --     where 
>  --       lf = toCFloat . pfun longForm $ i
>  --       cf = toCFloat . pfun closedForm $ i
>  --       df = cf - lf
>  --   sides = 100
>  --   dice = 50
>  --   longForm = iterConv dice (die sides)
>  --   closedForm = toPDF $ irwinHall' dice sides 
>    









// map(convolve(PDFd100,PDFd100)['fun'],map((x) => x * 50,range(0,25)))

iterConv(4,d100)
