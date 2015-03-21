{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Combinators where

import Data.Monoid
import Data.Maybe
import Data.Ord
import Data.List
import Control.Applicative
import Control.Comonad

import Control.Broccoli.Eval


-- | A signal that remembers the most recent occurrence of an event.
-- Takes a value to output prior to any events.
trap :: a -> E a -> X a
trap = TrapX

-- | Filter out events with the value of Nothing.
justE :: E (Maybe a) -> E a
justE = JustE

-- | Filter out events using a Maybe function.
maybeE :: (a -> Maybe b) -> E a -> E b
maybeE f e = justE (fmap f e)

-- | Filter out events using a Bool function.
filterE :: (a -> Bool) -> E a -> E a
filterE p e = justE (fmap (\x -> if p x then Just x else Nothing) e)

-- | Forget the values associated with the events.
voidE :: E a -> E ()
voidE e = () <$ e

-- | Merge two events into one.
eitherE :: E a -> E b -> E (Either a b)
eitherE e1 e2 = (Left <$> e1) <> (Right <$> e2)

-- | An event which gets the value of a signal when another event occurs.
snapshot :: (a -> b -> c) -> X a -> E b -> E c
snapshot = SnapshotE 

-- | Like 'snapshot' but ignores the original event's payload.
snapshot_ :: X a -> E b -> E a
snapshot_ = snapshot const

-- | Slow down a signal by a factor. A factor less than one is a speed-up.
dilate :: Double -> X a -> X a
dilate 0 x = error "dilate zero would be infinitely fast"
dilate rate x = timeWarp (*rate) (/rate) x

multiplex :: [X a] -> X [a]
multiplex = MultiX

-- | Occurs when something interesting happens between two successive events.
edge :: (a -> a -> Maybe b) -> E a -> E b
edge diff e = maybeE (uncurry diff) (accum1e e)

-- | Sum over events using an initial state and a state transition function.
mealy :: s -> (a -> s -> s) -> E a -> X s
mealy s0 trans e = out where
  out = trap s0 e'
  e' = snapshot f out e
  f s x = trans x s

-- | > accum s0 = mealy s0 ($)
accum :: s -> E (s -> s) -> X s
accum s0 = mealy s0 ($)

-- | Delay occurrences of an event.
delayE :: Double -> E a -> E a
delayE dt e = DelayE (fmap (,dt) e)

-- | Like 'delayE' but the amount of delay is determined on a per-event basis.
delayE' :: E (a, Double) -> E a
delayE' = DelayE

-- | An event that occurs once at the beginning of the simulation.
boot :: E ()
boot = occurs [(0, ())]

-- | At most the first occurrence.
once :: E a -> E a
once e = justE out where
  out = snapshot ($) cons e
  cons = trap Just (const Nothing <$ e)

-- | Filter out events when the Bool signal is False.
whenE :: X Bool -> E a -> E a
whenE x e = justE (snapshot f x e) where
  f b v = if b then Just v else Nothing

accum1e :: E a -> E (a,a)
accum1e e = justE (snapshot f mem e) where
  f Nothing _ = Nothing
  f (Just x) y = Just (x,y)
  mem = trap Nothing (Just <$> e)

-- | Periodic event with a specified period in seconds.
pulse :: Double -> E ()
pulse period = occurs (map (\i -> (i*period, ())) [0..])
