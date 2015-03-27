{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Combinators where

import Data.Monoid
import Control.Applicative
import Numeric

import Control.Broccoli.Eval


maybeE :: (a -> Maybe b) -> E a -> E b
maybeE f e = justE (fmap f e)

filterE :: (a -> Bool) -> E a -> E a
filterE p e = justE (fmap (\x -> if p x then Just x else Nothing) e)

voidE :: E a -> E ()
voidE e = () <$ e

eitherE :: E a -> E b -> E (Either a b)
eitherE e1 e2 = (Left <$> e1) <> (Right <$> e2)

-- | Like 'snapshot' but ignores the original event's payload.
snapshot_ :: X a -> E b -> E a
snapshot_ = snapshot const


-- | Slow down a signal by a factor. A factor less than one is a speed-up.
dilate :: Double -> X a -> X a
dilate 0 _ = error "dilate zero"
dilate rate x = timeWarp (/rate) (*rate) x


-- | Sum over events using an initial state and a state transition function.
mealy :: s -> (a -> s -> s) -> E a -> X s
mealy s0 trans e = out where
  out = trap s0 e'
  e' = snapshot f out e
  f s x = trans x s

-- | > accum s0 = mealy s0 ($)
accum :: s -> E (s -> s) -> X s
accum s0 = mealy s0 ($)

-- | An event that occurs once at the beginning of the simulation.
boot :: E ()
boot = occurs [(0, ())]

-- | At most the first occurrence.
once :: E a -> E a
once e = justE out where
  out = snapshot ($) cons e
  cons = trap Just (const Nothing <$ e)

-- | Filter out events when the @Bool@ signal is @False@.
whenE :: X Bool -> E a -> E a
whenE x e = justE (snapshot f x e) where
  f b v = if b then Just v else Nothing

-- | Periodic event with a specified period in seconds.
pulse :: Double -> E ()
pulse 0 = error "pulse zero"
pulse period = occurs (map (\i -> (i*(abs period), ())) [0..])

multiplex :: [X a] -> X [a]
multiplex [] = pure []
multiplex (x:xs) = liftA2 (:) x (multiplex xs)

-- | Noisy signal in the range @[0, 1)@.
noise :: X Double
noise = f <$> time where
  b = 123456789
  f t = fract (cos(23.14069263277926 * t + 2.665144142690225) * b)
  fract x = abs (snd (properFraction x :: (Integer,Double)))

-- | Pairs occurrence @n-1@ with occurrence @n@. Nothing happens on the first
-- occurrence.
pairE :: E a -> E (a,a)
pairE e = justE (snapshot f mem e) where
  f Nothing _ = Nothing
  f (Just x) y = Just (x,y)
  mem = trap Nothing (Just <$> e)

-- | During a simulation print out occurrences of the event as they happen.
-- Only for debugging.
debugE :: (a -> String) -> E a -> E a
debugE toString e = DebugE toString e

-- | During a simulation print out values of a signal at the specified sample
-- rate. Only for debugging.
debugX :: Int -> (a -> String) -> X a -> X a
debugX 0 _ _ = error "debugX: sample rate zero"
debugX sr toString x = liftA2 const x dummy where
  dummy = trap (atZero x) (debugE toString sampler)
  sampler = snapshot_ x (pulse period)
  period = srToPeriod sr

-- | Format time like the debuggers and testbenches.
showTime :: Time -> String
showTime t = showFFloat (Just 5) t ""


