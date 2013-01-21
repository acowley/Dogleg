{-# LANGUAGE ScopedTypeVariables, MultiWayIf #-}
-- |Powell's "dogleg" minimization strategy. An overview of the algorithm may 
-- be found at <http://math.fullerton.edu/mathews/n2003/PowellMethodMod.html>.
module Numeric.Dogleg (SearchParams(..), defaultParams, 
                       optimize, optimizeM) where
import Prelude hiding (length, filter, null, unzip, mapM)
import Control.Applicative
import Control.Monad (foldM)
import Data.List (foldl')
import Data.Maybe (fromJust)
import Data.Traversable (Traversable)
import Data.Vector (generate, minIndex, (!), length, mapM,
                    filter, null, unzip, elemIndex, generateM)
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
               , dropWorstBasis :: Bool
               -- ^ Drop the least effective basis vector on each
               -- iteration. Given that a new basis vector is added on
               -- each iteration, this preserves the total number of
               -- basis vectors used for each taxi-cab step.
               , useGolden :: Bool
               -- ^ Perform a golden section search for optimal
               -- parameters after the uniform sampling probe. If
               -- 'False, just provide the minimal parameter found in
               -- the uniformly spaced probe.
               }

-- |Default 'SearchParams' suitable for searching parameter space
-- whose components are taken from the range [-1,1].
defaultParams :: Floating a => SearchParams a
defaultParams = SearchParams 4 0.01 0.2 11 0.5 True True

-- |@optimize searchParams initialGuess basis valid eval@ finds a
-- minimal value of the function @eval@ starting at coordinate
-- @initialGuess@. The search makes use of a @basis@ of the vector
-- space of which @initialGuess@ is an element, and a validity
-- predicate, @valid@, that may be used to bound the search. The
-- @searchParams@ field controls the iterative aspects of the search.
optimize :: (Show (t a), Metric t, Applicative t, Ord b, Num b, Traversable t, 
             Enum a, Epsilon a, RealFrac a, Floating a, Show a, Show b) =>
            SearchParams a -> t a -> (t a -> Bool) -> (t a -> b) -> t a
optimize sp params ok eval = go 0 (stepSize sp) params (basisFor params)
  where go i s p b | i == maxIter sp = p
                   | otherwise = let (p',b') = opt s p b
                                 in if qd p' p < noChange sp
                                    then p'
                                    else go (i+1) (s * stepShrink sp) p' b'
        opt = optimize' ok eval sp

-- |@optimizeM searchParams initialGuess basis valid eval@ finds a
-- minimal value of the monadic function @eval@ starting at coordinate
-- @initialGuess@. The search makes use of a @basis@ of the vector
-- space of which @initialGuess@ is an element, and a validity
-- predicate, @valid@, that may be used to reject some candidate
-- parameters. The @searchParams@ field controls the iterative aspects
-- of the search.
optimizeM :: (Show (t a), Metric t, Applicative t, Ord b, Num b, Traversable t, 
              Enum a, Epsilon a, RealFrac a, Floating a, Show a, Show b, 
              Monad m) =>
            SearchParams a -> t a -> (t a -> Bool) -> (t a -> m b) -> m (t a)
optimizeM sp params ok eval = go 0 (stepSize sp) params (basisFor params)
  where go i s p b | i == maxIter sp = return p
                   | otherwise = do (p',b') <- opt s p b
                                    if qd p' p < noChange sp
                                    then return p'
                                    else go (i+1) (s * stepShrink sp) p' b'
        opt = optimizeM' ok eval sp

-- | @updateBasis basis gains goodDir@ updates @basis@ by dropping the
-- vector with lowest @gain@ and replacing it with @goodDir@.
updateBasis :: (Floating a, Ord t, Epsilon a, Metric f, Show (f a)) =>
               SearchParams a -> [f a] -> [t] -> f a -> [f a]
updateBasis sp basis gains goodDir = 
  if dropWorstBasis sp 
  then take i basis ++ goodDir:drop (i+1) basis
  else goodDir : basis
  where (_, i) = minimum $ zip gains [0..]
 
-- |@optimize' valid f n useGolden stepSize initialGuess basis@ finds
-- a locally optimal set of parameters satisfying the @valid@
-- predicate for function @f@ starting from @initialGuess@. @n@
-- uniformly spaced samples -- spaced @stepSize@ apart -- are used to
-- initialize a golden section minimization. Optimal parameters and an
-- updated basis are returned.
optimize' :: forall t a b. (Show (t a), Ord b, Num b, Metric t, Epsilon a, Applicative t, 
              RealFrac a, Floating a, Show a, Show b) =>
            (t a -> Bool) -> (t a -> b) -> SearchParams a -> a -> t a -> [t a] -> (t a, [t a])
optimize' ok eval sp bigStepSize params basis = 
  let (p', revGains) = foldl' minLinear (params,[]) basis -- taxi cab method
      goodDir = normalize $ p' ^-^ params
      (p'',_) = minLinear (p',[]) goodDir -- Powell
  in (p'', updateBasis sp basis (reverse revGains) goodDir)
  where -- Define how many steps of what size we'll take
        smallStepSize = bigStepSize * 0.1
        half = numSamples sp `quot` 2
        -- Convert a natural number index to a zero-mean step
        takeStep :: Int -> a
        takeStep = (bigStepSize*) . fromIntegral . subtract half
        -- Perform a linear search from parameters @p@ along basis
        -- vector @b@. Returns a new set of parameters and conses the
        -- improvement gleaned from the search to the @gains@ list.
        minLinear :: (t a, [b]) -> t a -> (t a, [b])
        minLinear (p,gains) b = 
          let mkP = (p ^+^) . ( b ^*) -- Convert step to parameter vector
              schwartz x = (mkP x, x) -- Pair a step with a parameter

              -- Compute various parameters, @ps@, to probe that all
              -- satisfy the constraint predicate @ok@. Each probe
              -- coordinate is paired with its associated step.
              (ps,inds) = unzip . filter (ok . fst) $ 
                          generate (numSamples sp) (schwartz . takeStep)
              ss = eval <$> ps
              startingCost = ss ! (fromJust $ elemIndex 0 inds)
              i = minIndex ss
          in case () of
               _ | null ps -> (p, 0:gains)
               _ | useGolden sp && i > 0 && i < (length ss - 1) ->
                   let x = linearSearch (inds ! (i-1))
                                        (inds ! i)
                                        (inds ! (i+1))
                                        smallStepSize
                                        (eval . mkP)
                   in (mkP x, (startingCost - eval (mkP x)) : gains)
               _ | otherwise -> (ps ! i, (startingCost - (ss ! i)) : gains)

-- Golden section search
linearSearch :: (Floating a, RealFrac a, Show b, Show a, Ord b) => 
                a -> a -> a -> a -> (a -> b) -> a
linearSearch left center right minStep f = goldenCheck left center right
  where memo = generate (1 + ceiling ((right - left) / minStep))
                        (f . (left+) . (minStep*) . fromIntegral)
        f' x = memo ! (round $ (x - left) / minStep)
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

optimizeM' :: forall t a b m. 
              (Show (t a), Ord b, Num b, Metric t, Epsilon a, Applicative t, 
              RealFrac a, Floating a, Show a, Show b, Monad m) =>
            (t a -> Bool) -> (t a -> m b) -> SearchParams a -> a -> t a -> 
            [t a] -> m (t a, [t a])
optimizeM' ok eval sp bigStepSize params basis = 
  do (p', revGains) <- foldM minLinear (params,[]) basis -- taxi cab method
     let goodDir = normalize $ p' ^-^ params
     (p'',_) <- minLinear (p',[]) goodDir -- Powell
     return $ (p'', updateBasis sp basis (reverse revGains) goodDir)
  where -- Define how many steps of what size we'll take
        smallStepSize = bigStepSize * 0.1
        half = numSamples sp `quot` 2
        -- Convert a natural number index to a zero-mean step
        takeStep :: Int -> a
        takeStep = (bigStepSize*) . fromIntegral . subtract half
        -- Perform a linear search from parameters @p@ along basis
        -- vector @b@. Returns a new set of parameters and conses the
        -- improvement gleaned from the search to the @gains@ list.
        minLinear :: (t a, [b]) -> t a -> m (t a, [b])
        minLinear (p,gains) b = 
          let mkP = (p ^+^) . ( b ^*) -- Convert step to parameter vector
              schwartz x = (mkP x, x) -- Pair a step with a parameter

              -- Compute various parameters, @ps@, to probe that all
              -- satisfy the constraint predicate @ok@. Each probe
              -- coordinate is paired with its associated step.
              (ps,inds) = unzip . filter (ok . fst) $ 
                          generate (numSamples sp) (schwartz . takeStep)
          in do ss <- mapM eval ps
                let startingCost = ss ! (fromJust $ elemIndex 0 inds)
                    i = minIndex ss
                if | null ps -> return (p, 0:gains)
                   | useGolden sp && i > 0 && i < (length ss - 1) ->
                     do x <- linearSearchM (inds ! (i-1))
                                           (inds ! i)
                                           (inds ! (i+1))
                                           smallStepSize
                                           (eval . mkP)
                        bestCost <- eval (mkP x)
                        return (mkP x, (startingCost - bestCost) : gains)
                   | otherwise -> return (ps ! i, (startingCost - (ss ! i)) : gains)

-- Golden section search
linearSearchM :: (Floating a, RealFrac a, Show b, Show a, Ord b, Monad m) => 
                 a -> a -> a -> a -> (a -> m b) -> m a
linearSearchM left center right minStep f =
  do memo <- generateM (1 + ceiling ((right - left) / minStep))
                       (f . (left+) . (minStep*) . fromIntegral)
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
