-- | Small experimental library for interactive functional programs.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli (
  X,
  E,
  never,
  snapshot,
  snapshot_,
  accumulate,
  edge,
  justE,
  maybeE,
  filterE,
  Setup,
  runProgram,
  newX,
  newE,
  input,
  output,
  debugX,
  debugE,
  (<||>)
) where

import Control.Applicative
import Data.Functor
import Data.Monoid
import Control.Monad
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
  PortX :: MVar [ThreadId] -> TVar a -> X a

-- | An event that carries values of type a when it occurs.
data E a where
  NeverE    :: E a
  FmapE     :: forall a b . (b -> a) -> E b -> E a
  MappendE  :: E a -> E a -> E a
  ProductE  :: (b -> c -> a) -> E b -> E c -> E a
  SnapshotE :: E b -> X a -> E a
  JustE     :: E (Maybe a) -> E a
  PortE     :: MVar [ThreadId] -> TChan a -> E a

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

-- | A monad for hooking up inputs and outputs to a program.
data Setup a = Setup (MVar [ThreadId] -> IO a)

instance Monad Setup where
  return x = Setup (\_ -> return x)
  (Setup r) >>= f = Setup r' where
    r' mv = do
      x <- r mv
      let Setup r'' = f x
      r'' mv

instance Applicative Setup where
  pure = return
  (<*>) = ap

instance Functor Setup where
  fmap f (Setup io) = Setup (\mv -> f <$> io mv)

setupIO :: IO a -> Setup a
setupIO io = Setup (\_ -> io)

getThreads :: Setup (MVar [ThreadId])
getThreads = Setup (\mv -> return mv)

getThreadsE :: E a -> Maybe (MVar [ThreadId])
getThreadsE e = case e of
  NeverE -> Nothing
  FmapE _ e' -> getThreadsE e'
  MappendE e1 e2 -> getFirst $ First (getThreadsE e1) <> First (getThreadsE e2)
  ProductE _ e1 e2 -> getFirst $ First (getThreadsE e1) <> First (getThreadsE e2)
  SnapshotE e' x -> getFirst $ First (getThreadsE e') <> First (getThreadsX x)
  JustE e' -> getThreadsE e'
  PortE mv _ -> Just mv

getThreadsX :: X a -> Maybe (MVar [ThreadId])
getThreadsX x = case x of
  PureX _ -> Nothing
  FmapX _ x' -> getThreadsX x'
  ApplX x1 x2 -> getFirst $ First (getThreadsX x1) <> First (getThreadsX x2)
  PortX mv _ -> Just mv

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
  PortE mv ch -> do
    ch' <- atomically (dupTChan ch)
    return (PortE mv ch')

data Promise a = Promise { force :: IO a }

instance Functor Promise where
  fmap f p = f <$> Promise (force p)

instance Applicative Promise where
  pure x = Promise (return x)
  ff <*> xx = Promise $ do
    f <- force ff
    x <- force xx
    return (f x)

readE :: E a -> STM (Maybe a)
readE e = case e of
  NeverE -> return Nothing
  MappendE e1 e2 -> do
    mx <- readE e1
    case mx of
      Nothing -> do
        my <- readE e2
        case my of
          Nothing -> return Nothing
          Just y -> return (Just y)
      Just x -> return (Just x)
  FmapE f e' -> (fmap . fmap) f (readE e')
  ProductE f e1 e2 -> do
    mx <- readE e1
    my <- readE e2
    case (mx,my) of
      (Just x, Just y) -> return (Just (f x y))
      _ -> return Nothing
  SnapshotE e' x -> do
    m_ <- readE e'
    case m_ of
      Nothing -> return Nothing
      Just _ -> Just <$> readX x
  JustE e' -> do
    mx <- readE e'
    case mx of
      Nothing -> return Nothing
      Just Nothing  -> return Nothing
      Just (Just x) -> return (Just x)
  PortE _ ch -> do
    emp <- isEmptyTChan ch
    if emp
      then return Nothing
      else Just <$> readTChan ch

readX :: X a -> STM a
readX x = case x of
  PureX v -> return v
  FmapX f xx -> f <$> readX xx
  ApplX ff xx -> do
    f <- readX ff
    x <- readX xx
    return (f x)
  PortX _ tv -> readTVar tv

hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang

waitE :: E a -> IO a
waitE e0 = do
  e <- dupE e0
  readEIO e

readEIO :: E a -> IO a
readEIO e = atomically $ do
  mx <- readE e
  case mx of
    Nothing -> retry
    Just x -> return x

---

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

-- | An event that never happens.
never :: E a
never = mempty

-- | Sum over events using an initial state and a state transition function.
accumulate :: E a -> s -> (a -> s -> s) -> X s
accumulate e0 s0 trans = case getThreadsE e0 of
  Nothing -> pure s0
  Just mv -> PortX mv tv where
    tv = unsafePerformIO $ do
      state <- newTVarIO s0
      threadId <- forkIO $ do
        e <- dupE e0
        forever $ do
          atomically $ do
            mx <- readE e
            case mx of
              Nothing -> retry
              Just x -> do
                s <- readTVar state
                let s' = trans x s
                writeTVar state s'
      modifyMVar_ mv (return . (threadId:))
      return state

-- | An event that occurs when an edge is detected in a signal. The edge test
-- is applied to values before and after a discrete transition in the signal.
-- The test should return Nothing when the two values are the same.
edge :: X a -> (a -> a -> Maybe b) -> E b
edge x diff = case getThreadsX x of
  Nothing -> never
  Just mv -> PortE mv ch where
    ch = unsafePerformIO $ do
      out <- newBroadcastTChanIO
      threadId <- forkIO $ do
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
      modifyMVar_ mv (return . (threadId:))
      return out


-- | Creates a new event and an IO action to trigger it.
newE :: Setup (E a, a -> IO ())
newE = do
  mv <- getThreads
  bch <- setupIO newBroadcastTChanIO
  return (PortE mv bch, \x -> do
    (atomically . writeTChan bch) x
    )

-- | Creates a new signal and an IO action to update it. The argument is
-- the initial value of the signal.
newX :: a -> Setup (X a, a -> IO ())
newX v = do
  mv <- getThreads
  tv <- setupIO (newTVarIO v)
  return (PortX mv tv, atomically . writeTVar tv)

-- | Spawn a thread to execute an action for each event occurrence.
output :: E a -> (a -> IO ()) -> Setup ()
output e0 act = do
  mv <- getThreads
  setupIO $ do
    e <- dupE e0
    tid <- (forkIO . forever) (readEIO e >>= act)
    modifyMVar_ mv (return . (tid:))
    return ()

-- | Spawn an input thread to generate source signals and events.
input :: IO () -> Setup ()
input handler = do
  mv <- getThreads
  setupIO $ do
    tid <- forkIO handler
    modifyMVar_ mv (return . (tid:))
    return ()

-- | Run the setup action to create input and output threads. The returned IO
-- action will be executed when setup is complete. runProgram blocks until
-- the returned event occurs, at which time it kills all the threads and
-- returns.
runProgram :: Setup (IO (), E ()) -> IO ()
runProgram (Setup setup) = do
  mv <- newMVar []
  (boot, exit) <- setup mv
  --threadDelay 5000
  boot
  waitE exit
  withMVar mv (mapM killThread)
  return ()

-- | Print out events as they occur. Only for debugging purposes.
debugE :: Show a => E a -> E a
debugE e = unsafePerformIO $ do
  e' <- dupE e
  (forkIO . forever) (readEIO e' >>= print)
  return e

-- | Print out transitions in a signal. Only for debugging purposes.
debugX :: (Eq a, Show a) => X a -> X a
debugX x =
  let diff a b = if a == b then Nothing else Just (a,b) in
  let e = edge x diff in
  unsafePerformIO $ do
    forkIO $ do
      e' <- dupE e
      forever (readEIO e' >>= print)
    return x

-- | Same as <> but on events that might have a different type.
(<||>) :: E a -> E b -> E (Either a b)
e1 <||> e2 = (Left <$> e1) <> (Right <$> e2)

