{-# LANGUAGE TupleSections #-}
module Control.Broccoli.Combinators where

import Data.Monoid
import Data.Maybe
import Data.Ord
import Data.List
import Control.Applicative
import Control.Comonad

import Control.Broccoli.Types
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

-- | Time warp a signal.
timeWarp :: (Time -> Time) -> X a -> X a
timeWarp f = TimeWarpX f id

-- | Like 'timeWarp' but works with events. The inverse of the warp function
-- must exist and be provided.
timeWarp' :: (Time -> Time) -> (Time -> Time) -> X a -> X a
timeWarp' = TimeWarpX

-- | Slow down a signal by a factor. A factor less than one is a speed-up.
dilate :: Double -> X a -> X a
dilate 0 x = error "dilate zero would be infinitely fast"
dilate rate x = timeWarp' (*rate) (/rate) x

-- | Shift a signal forward in time. A negative shift shifts back in time.
timeShift :: Double -> X a -> X a
timeShift delta sig = timeWarp' (subtract delta) (+ delta) sig
 
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

-- | An event with occurrences explicitly listed.
occurs :: [(Time, a)] -> E a
occurs = ConstantE . sortBy (comparing fst)

-- | Continually emit snapshots of a signal at a regular interval.
raster :: X a -> E a
raster x = snapshot_ x RasterE

-- | > rasterize s = trap (atZero s) (raster s)
rasterize :: X a -> X a
rasterize s = trap (atZero s) (raster s)

-- | Signal carrying the time since start of simulation in seconds.
time :: X Time
time = TimeX

-- | An event that occurs once at the beginning of the simulation.
boot :: E ()
boot = occurs [(0, ())]

-- | At most the first occurrence.
once :: E a -> E a
once e = justE out where
  out = snapshot ($) cons e
  cons = trap Just (const Nothing <$ e)

-- | > dx / dt
derivative :: Fractional a => X a -> X a
derivative = extend f where
  f s = let dx = at s 0 - at s (-dt') in dx / dt
  dt' = 0.001
  dt = realToFrac dt'

-- | Integrate a numeric signal using an initial value. The event
-- will reset the sum.
integral :: Fractional a => a -> E a -> X a -> X a
integral v0 reset x = mealy v0 f stream where
  stream = eitherE reset (accum1e (snapshot (,) time (raster x)))
  f (Left v) _ = v
  f (Right ((t0,y0),(t1,y1))) s = s + (y1-y0)/(r2f (t1-t0))
  r2f = realToFrac

-- | Filter out events when the Bool signal is False.
whenE :: X Bool -> E a -> E a
whenE x e = justE (snapshot f x e) where
  f b v = if b then Just v else Nothing

accum1e :: E a -> E (a,a)
accum1e e = justE (snapshot f mem e) where
  f Nothing _ = Nothing
  f (Just x) y = Just (x,y)
  mem = trap Nothing (Just <$> e)

-- | Print out occurrences of events as they happen. Only for debugging.
debugE :: (a -> String) -> E a -> E a
debugE toString e = undefined

-- | Print out values of a signal at arbitrary times. Only for debugging.
debugX :: Eq a => (a -> String) -> X a -> X a
debugX toString sig = undefined
