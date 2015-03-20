{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Combinators where

import Data.Monoid
import Data.Maybe
import Data.Ord
import Data.List
import Control.Applicative

import Control.Broccoli.Types
import Control.Broccoli.Eval


-- | A signal that remembers the most recent occurrence of an event.
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

-- | Same as 'unionE' but on events that might have a different type.
mergeE :: E a -> E b -> E (Either a b)
mergeE e1 e2 = (Left <$> e1) <> (Right <$> e2)

-- | Undo a 'mergeE'.
splitE :: E (Either a b) -> (E a, E b)
splitE e = (justE e1, justE e2) where
  e1 = fmap (either Just (const Nothing)) e
  e2 = fmap (either (const Nothing) Just) e

-- | An event which gets the value of a signal when another event occurs.
snapshot :: E a -> X b -> E (a,b)
snapshot e sig = SnapshotE e sig

-- | Like 'snapshot' but ignores the original event's payload.
snapshot_ :: E a -> X b -> E b
snapshot_ e sig = fmap snd (snapshot e sig)

-- | Time warp a signal.
timeWarp :: (Time -> Time) -> X a -> X a
timeWarp f = TimeWarpX f id

-- | Like 'timeWarp' but works with events. The inverse of the warp function
-- must exist and be provided.
timeWarp' :: (Time -> Time) -> (Time -> Time) -> X a -> X a
timeWarp' = TimeWarpX

-- | Slow down a signal by a factor.
dilate :: Double -> X a -> X a
dilate rate sig = timeWarp' (*rate) (/rate) sig

-- | Shift a signal forward in time.
timeShift :: Double -> X a -> X a
timeShift delta sig = timeWarp' (subtract delta) (+ delta) sig
 
-- | From many signals, one.
multiplex :: [X a] -> X [a]
multiplex = MultiX

-- | An event that occurs on "edges" detected in a signal. The signal will
-- be rasterized if necessary for this to make sense.
edge :: (a -> a -> Maybe b) -> X a -> E b
edge diff sig = (justE . fmap (uncurry diff) . Accum1E v0) e where
  v0 = sampleX sig 0
  e = fromMaybe (snapshot_ RasterE sig) (unX sig)

-- | Sum over events using an initial state and a state transition function.
accum :: s -> (a -> s -> s) -> E a -> X s
accum s0 trans e = out where
  out = trap s0 e'
  e' = fmap f (snapshot e out)
  f (x,s) = trans x s

-- | Delay occurrences of an event.
delayE :: Double -> E a -> E a
delayE dt e = DelayE (fmap (,dt) e)

-- | Like 'delayE' but the amount of delay is determined on a per-event basis.
delayE' :: E (a, Double) -> E a
delayE' = DelayE

-- | An event with occurrences explicitly listed.
occurs :: [(Time, a)] -> E a
occurs = ConstantE . sortBy (comparing fst)

-- | Rasterize a signal.
rasterize :: X a -> X a
rasterize sig = (trap (sampleX sig 0) . snapshot_ RasterE) sig

-- | Signal carrying the time since start of simulation in seconds.
time :: X Time
time = TimeX

-- | An event that occurs once at the beginning of the simulation.
once :: a -> E a
once x = occurs [(0, x)]

-- | > (y - dt) / dt
deriv :: Fractional a => X a -> X a
deriv sig = f <$> sig <*> timeWarp' (subtract dt) (+dt) sig where
  dt = 0.001
  f y1 y0 = (y1 - y0) / (realToFrac dt)

-- | Print out occurrences of events as they happen. Only for debugging.
debugE :: (a -> String) -> E a -> E a
debugE toString e = undefined

-- | Print out transitions in a signal as they happen, rasterizing if
-- necessary. Only for debugging.
debugX :: Eq a => ((a,a) -> String) -> X a -> X a
debugX toString sig = undefined
