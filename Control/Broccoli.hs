{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli (
  X,
  E,
  Output,
  newX,
  newE,
  snapshot,
  snapshot_,
  filterE,
  justE,
  maybeE,
  edge,
  accumulate,
  out,
  runProgram,
  debugX,
  debugE
) where

import Control.Applicative
import Data.Functor
import Data.Monoid
import Control.Monad
import Data.Unamb
import Data.IORef
import Control.Concurrent
import Control.Concurrent.STM
import Data.Function
import System.IO.Unsafe

-- | A value of type a that varies.
data X a where
  PureX :: a -> X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  PortX :: TVar a -> X a

-- | An event that carries values of type a when it occurs.
data E a where
  NeverE    :: E a
  FmapE     :: forall a b . (b -> a) -> E b -> E a
  MappendE  :: E a -> E a -> E a
  ProductE  :: (b -> c -> a) -> E b -> E c -> E a
  SnapshotE :: E b -> X a -> E a
  PortE     :: TChan a -> E a
  JustE     :: E (Maybe a) -> E a

-- | An IO action which will react to events.
newtype Output = Output (IO ())

instance Functor X where
  fmap f x = FmapX f x

instance Applicative X where
  pure x = PureX x
  f <*> x = ApplX f x

instance Functor E where
  fmap f e = FmapE f e

instance Monoid (E a) where
  mempty = NeverE
  mappend e1 e2 = MappendE e1 e2

dupE :: E a -> IO (E a)
dupE e = case e of
  NeverE -> return NeverE
  FmapE f e' -> do
    e'' <- dupE e'
    return (FmapE f e'')
  MappendE e1 e2 -> do
    e1' <- dupE e1
    e2' <- dupE e2
    return (MappendE e1' e2')
  PortE ch -> do
    ch' <- atomically (dupTChan ch)
    return (PortE ch')
  ProductE f e1 e2 -> do
    e1' <- dupE e1
    e2' <- dupE e2
    return (ProductE f e1' e2')
  SnapshotE e' x -> do
    e'' <- dupE e'
    return (SnapshotE e'' x)
  JustE e' -> do
    e'' <- dupE e'
    return (JustE e'')

readE :: E a -> IO a
readE e = case e of
  NeverE -> hang
  PortE ch -> atomically (readTChan ch)
  MappendE e1 e2 -> race (readE e1) (readE e2)
  FmapE f e' -> f <$> readE e'
  ProductE f e1 e2 -> do
    x <- readE e1
    y <- readE e2
    return (f x y)
  SnapshotE e' x -> do
    readE e'
    atomically (readX x)
  JustE e' -> fix $ \loop -> do
    m <- readE e'
    case m of
      Nothing -> loop
      Just x  -> return x

readX :: X a -> STM a
readX x = case x of
  PureX v -> return v
  FmapX f xx -> f <$> readX xx
  ApplX ff xx -> do
    f <- readX ff
    x <- readX xx
    return (f x)
  PortX tv -> readTVar tv

hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang

forkOut :: Output -> IO ()
forkOut (Output io) = do
  forkIO io
  return ()

waitE :: E a -> IO a
waitE e0 = do
  e <- dupE e0
  readE e

---

-- | Create a new signal with an initial value. Get back an IO action to
-- change the value of the signal. This is the only way the signal will
-- change.
newX :: a -> IO (a -> IO (), X a)
newX v0 = do
  tv <- newTVarIO v0
  return
    ( \x -> atomically (writeTVar tv x)
    , PortX tv )

-- | Create a new event and the associated IO action to trigger the event.
newE :: IO (a -> IO (), E a)
newE = do
  ch <- newBroadcastTChanIO
  return
    ( \x -> atomically (writeTChan ch x)
    , PortE ch )

-- | An event which gets the value of a signal when another event occurs.
snapshot :: E a -> X b -> E (a,b)
snapshot e x = ProductE (,) e (SnapshotE e x)

-- | Like snapshot but ignores the original event's payload.
snapshot_ :: E a -> X b -> E b
snapshot_ e x = SnapshotE e x

-- | Filter out events with the value of Nothing.
justE :: E (Maybe a) -> E a
justE = JustE

-- | Filter out events using a Maybe function.
maybeE :: (a -> Maybe b) -> E a -> E b
maybeE f e = justE (f <$> e)

-- | Filter out events using a Bool function.
filterE :: (a -> Bool) -> E a -> E a
filterE p e = maybeE (\x -> if p x then Just x else Nothing) e

-- | Events will occur when an "edge" is detected in a signal. The detection
-- algorithm checks the two values before and after a discrete change in
-- the signal.
edge :: X a -> (a -> a -> Maybe b) -> E b
edge x diff = PortE ch where
  ch = unsafePerformIO $ do
    out <- newBroadcastTChanIO
    forkIO $ do
      v0 <- atomically (readX x)
      ref <- newIORef v0
      forever $ do
        v <- readIORef ref
        (d, v') <- atomically $ do
          v' <- readX x
          case diff v v' of
            Just d  -> return (d, v')
            Nothing -> retry
        writeIORef ref v'
        atomically (writeTChan out d)
    return out

runEvent :: E a -> (a -> IO ()) -> IO ()
runEvent e0 act = do
  e <- dupE e0
  forever (readE e >>= act)

-- 
accumulate :: E a -> s -> (a -> s -> s) -> X s
accumulate e0 s0 trans = PortX tv where
  tv = unsafePerformIO $ do
    state <- newTVarIO s0
    forkIO $ do
      e <- dupE e0
      forever $ do
        x <- readE e
        atomically $ do
          s <- readTVar state
          let s' = trans x s
          writeTVar state s'
    return state

-- A handler for events.
out :: E a -> (a -> IO ()) -> Output
out e0 act = Output (runEvent e0 act)

-- Prints the values of a signal as they change.
debugX :: (Eq a, Show a) => X a -> Output
debugX x = Output $ do
  v0 <- atomically (readX x)
  print v0
  let diff a b = if a == b then Nothing else Just b
  runEvent (edge x diff) print

-- Prints the values of events as they occur.
debugE :: (Show a) => E a -> Output
debugE e = out e print

-- Run a set of Outputs and stop when the event occurs. The IO action will
-- be executed after the system is setup. This can be used to trigger a
-- "boot" event.
runProgram :: IO () -> E () -> [Output] -> IO ()
runProgram notifyBoot stop outs = do
  forM_ outs forkOut
  threadDelay 5000
  notifyBoot
  waitE stop
