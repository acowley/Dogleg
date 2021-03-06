{-# LANGUAGE ScopedTypeVariables, MultiWayIf #-}
-- |Powell's "dogleg" minimization strategy. An overview of the algorithm may 
-- be found at <http://math.fullerton.edu/mathews/n2003/PowellMethodMod.html>.
module Numeric.Dogleg (SearchParams(..), defaultParams, optimize, 
                       optimizeBatch, optimizeM, optimizeBatchM) where
import Control.Applicative
import Control.Monad (foldM)
import Data.Functor.Identity
import Data.Traversable (Traversable)
import Data.Vector ((!))
import qualified Data.Vector as V
import Linear hiding (basis)

-- |Parameters that control the search procedure.
data SearchParams a = 
  SearchParams { maxIter    :: Int
               -- ^ Maximum number of iterations to perform.
               , noChange   :: a
               -- ^ Cease iterating when the minimum value has changed
               -- by less than this amount.
               , stepSize   :: a
               -- ^ Step size for uniform sampling on the first
               -- iteration.
               , numSamples :: Int
               -- ^ How many uniformly distributed samples separated
               -- by 'stepSize' to try for each linear probe.
               , stepShrink :: a 
               -- ^ Scale factor 'stepSize' is multiplied by on each
               -- iteration.
               , dropBestBasis :: Bool
               -- ^ Drop the most effective basis vector on each
               -- iteration. Given that a new basis vector is added on
               -- each iteration, this preserves the total number of
               -- basis vectors used for each taxi-cab step.
               , useGolden :: Bool
               -- ^ Perform a golden section search for optimal
               -- parameters after the uniform sampling probe. If
               -- 'False', just provide the minimal parameter found in
               -- the uniformly spaced probe.
               }

-- |Default 'SearchParams' suitable for searching parameter space
-- whose components are taken from the range [-1,1].
defaultParams :: Floating a => SearchParams a
defaultParams = SearchParams 4 0.0001 0.2 11 0.5 True True

-- |@optimize searchParams initialGuess basis valid eval@ finds a
-- minimal value of the function @eval@ starting at coordinate
-- @initialGuess@. The search makes use of a @basis@ of the vector
-- space of which @initialGuess@ is an element, and a validity
-- predicate, @valid@, that may be used to bound the search. The
-- @searchParams@ field controls the iterative aspects of the search.
optimize :: (Enum a, Floating a, Num b, Ord b, RealFrac a, Show (t a), Show a,
             Show b, Applicative t, Traversable t, Metric t, Epsilon a)
         => SearchParams a -> t a -> (t a -> Bool) -> (t a -> b) -> (t a, b)
optimize sp params ok eval = runIdentity $ 
                             optimizeM sp params ok (Identity . eval)

-- |Similar to @optimize@, but the user-supplied evaluation function
-- is given parameters to evaluate in batches. This enables the caller
-- to make use of parallelism where appropriate.
optimizeBatch :: (Enum a, Floating a, Num b, Ord b, RealFrac a, Show (t a),
                  Show a, Show b, Applicative t, Traversable t, Metric t,
                  Epsilon a)
              => SearchParams a -> t a -> (t a -> Bool) -> ([t a] -> [b])
              -> (t a, b)
optimizeBatch sp params ok eval = runIdentity $ 
                                  optimizeBatchM sp params ok (Identity . eval)

-- |@optimizeM searchParams initialGuess basis valid eval@ finds a
-- minimal value of the monadic function @eval@ starting at coordinate
-- @initialGuess@. The search makes use of a @basis@ of the vector
-- space of which @initialGuess@ is an element, and a validity
-- predicate, @valid@, that may be used to reject some candidate
-- parameters. The @searchParams@ field controls the iterative aspects
-- of the search.
optimizeM :: (Enum a, Floating a, Monad m, Functor m, Num b, Ord b,
              RealFrac a, Show (t a), Show a, Show b, Applicative t,
              Traversable t, Metric t, Epsilon a)
          => SearchParams a -> t a -> (t a -> Bool) -> (t a -> m b)
          -> m (t a, b)
optimizeM sp params ok eval = optimizeBatchM sp params ok (mapM eval)

-- |Similar to @optimizeM@, but the user-supplied evaluation function
-- is given parameters to evaluate in batches. This enables the caller
-- to make use of parallelism or concurrency where appropriate.
optimizeBatchM :: (Enum a, Floating a, Monad m, Functor m, Num b, Ord b,
                   RealFrac a, Show (t a), Show a, Show b, Applicative t,
                   Traversable t, Metric t, Epsilon a)
               => SearchParams a -> t a -> (t a -> Bool) -> ([t a] -> m [b])
               -> m (t a, b)
optimizeBatchM sp params ok eval = go 0 (stepSize sp) params (basisFor params)
  where go i s p b | i == maxIter sp = error $ "Optimization needs to run "++
                                               "for at least one iteration!"
                   | otherwise = do (e, p',b') <- opt s p b
                                    if qd p' p < noChange sp 
                                       || i == maxIter sp - 1
                                    then return (p', e)
                                    else go (i+1) (s * stepShrink sp) p' b'
        opt = optimizeM' ok eval sp

-- | @updateBasis basis gains goodDir@ updates @basis@ by dropping the
-- vector with lowest @gain@ and replacing it with @goodDir@.
updateBasis :: (Floating a, Ord t, Epsilon a, Metric f, Show (f a)) =>
               SearchParams a -> [f a] -> [t] -> f a -> [f a]
updateBasis sp basis gains goodDir = 
  if dropBestBasis sp 
  then let (_,i) = maximum $ zip gains [0..]
       in take i basis ++ goodDir:drop (i+1) basis
  else basis

-- Strict pair
data P a b = P !a !b
psnd :: P a b -> b
psnd (P _ y) = y

optimizeM' :: forall t a b m. 
              (Show (t a), Ord b, Num b, Metric t, Epsilon a, Applicative t, 
              RealFrac a, Floating a, Show a, Show b, Functor m, Monad m) =>
            (t a -> Bool) -> ([t a] -> m [b]) -> SearchParams a -> a -> t a -> 
            [t a] -> m (b, t a, [t a])
optimizeM' ok eval sp bigStepSize params basis = 
  do -- taxi cab method
     P e0 (P p' revGains) <- foldM (minLinear . psnd)
                                   (P 0 (P params []))
                                   basis
     let goodDir = normalize $ p' ^-^ params
     if nearZero $ quadrance goodDir
     then return (e0, p', basis)
     else do P e (P p'' _) <- minLinear (P p' []) goodDir -- Powell
             return (e, p'', updateBasis sp basis (reverse revGains) goodDir)
  where -- Define how many steps of what size we'll take
        smallStepSize = bigStepSize * 0.1
        half = numSamples sp `quot` 2
        -- Convert a natural number index to a zero-mean step
        takeStep :: Int -> a
        takeStep = (bigStepSize*) . fromIntegral . subtract half
        -- Perform a linear search from parameters @p@ along basis
        -- vector @b@. Returns the computed cost, a new set of
        -- parameters, and conses the improvement gleaned from the
        -- search to the @gains@ list.
        minLinear :: P (t a) [b] -> t a -> m (P b (P (t a) [b]))
        minLinear (P p gains) b = 
          let mkP = (p ^+^) . ( b ^*) -- Convert step to parameter vector
              schwartz x = (mkP x, x) -- Pair a step with a parameter

              -- Compute various parameters, @ps@, to probe that all
              -- satisfy the constraint predicate @ok@. Each probe
              -- coordinate is paired with its associated step.
              (ps,inds) = V.unzip . V.filter (ok . fst) $ 
                          V.generate (numSamples sp) (schwartz . takeStep)
          in do ss <- V.fromList <$> eval (V.toList ps)
                let Just i0 = V.elemIndex 0 inds
                    startingCost = ss ! i0
                    i = V.minIndex ss
                if | V.null ps || i == i0 -> 
                     return (P startingCost (P p (0:gains)))
                   | useGolden sp && i > 0 && i < (V.length ss - 1) ->
                     do x <- linearSearchM (inds ! (i-1))
                                           (inds ! i)
                                           (inds ! (i+1))
                                           smallStepSize
                                           (eval . map mkP)
                        [bestCost] <- eval [mkP x]
                        let dc = startingCost - bestCost
                        return $ P bestCost (P (mkP x) (dc : gains))
                   | otherwise -> let c = ss ! i
                                      dc = startingCost - c
                                  in return $ P c (P (ps ! i) (dc : gains))

-- Golden section search
linearSearchM :: (Floating a, RealFrac a, Show b, Show a, Ord b, 
                  Functor m, Monad m)
              => a -> a -> a -> a -> ([a] -> m [b]) -> m a
linearSearchM left center right minStep f =
  do memo <- let n = 1 + ceiling ((right-left) / minStep)
                 toStep x = fromIntegral x * minStep + left
             in V.fromList <$> f (map toStep [0..n-1::Int])
     let f' x = memo ! (round $ (x - left) / minStep)
         goldenCheck a b c = let i = snd . minimum $ zip (map f' [a,b,c]) [0..]
                             in if i == 1 then golden a b c else [a,b,c] !! i
         golden a b c = let x = if c - b > b - a
                                then b + resphi * (c - b)
                                else b - resphi * (b - a)
                        in if abs (c - a) < tau -- * (abs b + abs x)
                           then (c + a) / 2
                           else if f' x < f' b
                                then if c - b > b - a
                                     then goldenCheck b x c
                                     else goldenCheck a x b
                                else if c - b > b - a
                                     then goldenCheck a b x
                                     else goldenCheck x b c
         resphi = 2 - (1 + sqrt 5) / 2
         tau = minStep * 3
     return $ goldenCheck left center right
