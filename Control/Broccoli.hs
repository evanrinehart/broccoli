-- | Small experimental library for interactive functional programs.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli (
  X,
  E,

  -- * Event and signal combinators
  never,
  unionE,
  (<>),
  (-|-),
  voidE,
  snapshot,
  snapshot_,
  accum,
  edge,
  trap,
  justE,
  maybeE,
  filterE,
  rasterize,

  -- * Setup IO interface
  Setup,
  Time,
  Boot,
  runProgram,
  newX,
  newE,
  input,
  output,

  -- * Debug
  debugX,
  debugE,
) where

import Control.Applicative
import Data.Monoid
import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.STM
import System.IO.Unsafe
import Data.Time

-- | @X a@ represents time signals with values of type @a@.
-- 
-- > X a = Time -> a
data X a where
  PureX :: a -> X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  MappendX :: Monoid a => X a -> X a -> X a
  TimeX :: a ~ Time => Context -> X a
  PortX :: Context -> TVar (a,Time) -> X a

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(Time, a)]
data E a where
  NeverE    :: E a
  FmapE     :: forall a b . (b -> a) -> E b -> E a
  MappendE  :: E a -> E a -> E a
  SnapshotE :: a ~ (b,c) => E b -> X c -> E a
  JustE     :: E (Maybe a) -> E a
  --DelayedE  :: E a -> Int -> E a
  PortE     :: Context -> TChan (a, Time) -> E a

instance Functor X where
  fmap f x = FmapX f x

instance Applicative X where
  pure x = PureX x
  f <*> x = ApplX f x

instance Monoid a => Monoid (X a) where
  mempty = pure mempty
  mappend = MappendX

instance Functor E where
  fmap f e = FmapE f e

-- | mempty = 'never', mappend = 'unionE'
instance Monoid (E a) where
  mempty = never
  mappend = unionE

-- | A monad for hooking up inputs and outputs to a program.
data Setup a = Setup (Context -> IO a)

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

-- | Time is measured from the beginning of a simulation in seconds.
type Time = Double

-- | The boot event occurs once at the beginning of a simulation.
type Boot = ()

data Context = Context
  { cxThreads :: MVar [ThreadId]
  , cxEpoch   :: UTCTime }

setupIO :: IO a -> Setup a
setupIO io = Setup (\_ -> io)

getContext :: Setup Context
getContext = Setup (\cx -> return cx)

containsTimeX :: X a -> Bool
containsTimeX x = case x of
  PureX _ -> False
  FmapX _ x' -> containsTimeX x'
  ApplX x1 x2 -> containsTimeX x1 || containsTimeX x2
  MappendX x1 x2 -> containsTimeX x1 || containsTimeX x2
  TimeX _ -> True
  PortX _ _ -> False

getContextX :: X a -> Maybe Context
getContextX x = case x of
  PureX _ -> Nothing
  FmapX _ x' -> getContextX x'
  ApplX x1 x2 -> getFirst $ First (getContextX x1) <> First (getContextX x2)
  MappendX x1 x2 -> getFirst $ First (getContextX x1) <> First (getContextX x2)
  TimeX cx -> Just cx
  PortX cx _ -> Just cx

getContextE :: E a -> Maybe Context
getContextE e = case e of
  NeverE -> Nothing
  FmapE _ e' -> getContextE e'
  MappendE e1 e2 -> getFirst $ First (getContextE e1) <> First (getContextE e2)
  SnapshotE e' x -> getFirst $ First (getContextE e') <> First (getContextX x)
  JustE e' -> getContextE e'
  PortE cx _ -> Just cx

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

data EventResult a =
  TryLater |
  DropThis |
  NotNowNotEver |
  --Delayed a Int |
  Normal a Double
    deriving Show

readE :: E a -> STM (EventResult a)
readE e = case e of
  NeverE -> return NotNowNotEver
  MappendE e1 e2 -> do
    mx <- readE e1
    case mx of
      TryLater -> readE e2
      ok -> return ok
  FmapE f e' -> do
    mx <- readE e'
    case mx of
      Normal x t -> return (Normal (f x) t)
      TryLater -> return TryLater
      DropThis -> return DropThis
      NotNowNotEver -> return NotNowNotEver
  SnapshotE e' x -> do
    ma <- readE e'
    case ma of
      Normal a t -> do
        (b, _) <- readX t x
        return (Normal (a,b) t)
      TryLater -> return TryLater
      DropThis -> return DropThis
      NotNowNotEver -> return NotNowNotEver
  JustE e' -> do
    mx <- readE e'
    case mx of
      Normal Nothing _ -> return DropThis
      Normal (Just x) t -> return (Normal x t)
      TryLater -> return TryLater
      DropThis -> return DropThis
      NotNowNotEver -> return NotNowNotEver
  PortE _ ch -> do
    emp <- isEmptyTChan ch
    if emp
      then return TryLater
      else do
        (v, t) <- readTChan ch
        return (Normal v t)

readX :: Double -> X a -> STM (a, Time)
readX time sig = case sig of
  PureX v -> return (v, 0)
  FmapX f xx -> do
    (x, t) <- readX time xx
    return (f x, t)
  ApplX ff xx -> do
    (f,t1) <- readX time ff
    (x,t2) <- readX time xx
    return (f x, max t1 t2)
  MappendX xx1 xx2 -> do
    (x1, t1) <- readX time xx1
    (x2, t2) <- readX time xx2
    return (x1 <> x2, max t1 t2)
  TimeX _ -> return (time, time)
  PortX _ tv -> readTVar tv

waitE :: E a -> IO a
waitE e0 = do
  e <- dupE e0
  (x, _) <- readEIO e
  return x

readEIO :: E a -> IO (a, Time)
readEIO e = do
  result <- atomically $ do
    mx <- readE e
    case mx of
      TryLater -> retry
      other -> return other
  case result of
    TryLater -> error "impossible"
    Normal a t -> return (a, t)
    DropThis -> readEIO e
    NotNowNotEver -> hang

hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang
---

-- | An event which gets the value of a signal when another event occurs.
snapshot :: E a -> X b -> E (a,b)
snapshot e x = SnapshotE e x

-- | Like snapshot but ignores the original event's payload.
snapshot_ :: E a -> X b -> E b
snapshot_ e x = snd <$> snapshot e x

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
never = NeverE

-- | All the occurrences from two events together. Same as '<>'.
unionE :: E a -> E a -> E a
unionE = MappendE

-- | Same as 'unionE' but on events that might have a different type.
(-|-) :: E a -> E b -> E (Either a b)
e1 -|- e2 = (Left <$> e1) <> (Right <$> e2)

-- | Forget the values associated with the events.
voidE :: E a -> E ()
voidE e = () <$ e

-- | Sum over events using an initial state and a state transition function.
accum :: s -> (a -> s -> s) -> E a -> X s
accum s0 trans e0 = case getContextE e0 of
  Nothing -> pure s0
  Just cx -> PortX cx tv where
    tv = unsafePerformIO $ do
      state <- newTVarIO (s0, 0)
      threadId <- forkIO $ do
        e <- dupE e0
        forever $ do
          atomically $ do
            mx <- readE e
            case mx of
              TryLater -> retry
              DropThis -> return ()
              Normal x t -> do
                (s,_) <- readTVar state
                let s' = trans x s
                writeTVar state (s',t)
              NotNowNotEver -> error "impossible (2)"
      modifyMVar_ (cxThreads cx) (return . (threadId:))
      return state

-- | A signal that remembers the most recent occurrence of an event.
trap :: a -> E a -> X a
trap x0 = accum x0 (\x _ -> x)

-- | An event that occurs when an edge is detected in a signal. When a signal
-- changes discretely the edge test is evaluated on the values immediately
-- before and after a change. 
edge :: (a -> a -> Maybe b) -> X a -> E b
edge diff x = case getContextX x of
  Nothing -> never
  Just cx -> PortE cx ch where
    ch = unsafePerformIO $ do
      out <- newBroadcastTChanIO
      threadId <- forkIO $ do
        (v0,_) <- atomically (readX 0 x)
        ref <- newIORef v0
        if containsTimeX x
          then error "edge can't grok a continuously changing signal"
{-
          then forever $ do
            now <- chron (cxEpoch cx)
            v <- readIORef ref
            (v', _) <- atomically (readX now x)
            case diff v v' of
              Just d  -> do
                writeIORef ref v'
                atomically (writeTChan out (d,now))
              Nothing -> return ()
-}
          else forever $ do
            v <- readIORef ref
            (d, v', t) <- atomically $ do
              (v', t) <- readX undefined x
              case diff v v' of
                Just d  -> return (d, v', t)
                Nothing -> retry
            writeIORef ref v'
            atomically (writeTChan out (d, t))
      modifyMVar_ (cxThreads cx) (return . (threadId:))
      return out

-- | Rasterize a signal.
rasterize :: X a -> X a
rasterize x = case getContextX x of
  Nothing -> FmapX id x
  Just cx -> PortX cx tv where
    tv = unsafePerformIO $ do
      breadbasket <- newEmptyMVar
      threadId <- forkIO $ do
        v0 <- atomically (readX 0 x)
        out <- newTVarIO v0
        putMVar breadbasket out
        forever $ do
          now <- chron (cxEpoch cx)
          atomically $ do
            vt <- readX now x
            writeTVar out vt
          threadDelay 10000
      modifyMVar_ (cxThreads cx) (return . (threadId:))
      out <- readMVar breadbasket
      return out

chron :: UTCTime -> IO Double
chron epoch = do
  now <- getCurrentTime
  let time = diffUTCTime now epoch
  return (realToFrac time)

newInternalBoot :: Context -> IO (E (), IO ())
newInternalBoot cx = do
  bch <- newBroadcastTChanIO
  return
    ( PortE cx bch
    , atomically (writeTChan bch ((), 0)) )

-- | Creates a new input signal with an initial value. Use 'input' to feed
-- data to the signal during the simulation.
newX :: a -> Setup (X a, a -> IO ())
newX v = do
  cx <- getContext
  let epoch = cxEpoch cx
  tv <- setupIO (newTVarIO (v,0))
  return
    ( PortX cx tv
    , \x -> do
        now <- chron epoch
        atomically (writeTVar tv (x,now)))

-- | Creates a new input event and a command to trigger it.  Use 'input' to
-- to provide external stimulus during the simulation.
newE :: Setup (E a, a -> IO ())
newE = do
  cx <- getContext
  let epoch = cxEpoch cx
  bch <- setupIO newBroadcastTChanIO
  return
    ( PortE cx bch
    , \x -> do
        now <- chron epoch
        atomically (writeTChan bch (x,now)))



-- | Setup a thread to react to events. The callback will be provided with
-- the time of the event which is measured in seconds since the start of
-- the simulation.
output :: (Time -> a -> IO ()) -> E a -> Setup ()
output act e0 = do
  cx <- getContext
  setupIO $ do
    e <- dupE e0
    tid <- forkIO . forever $ do
      (x, t) <- readEIO e
      act t x
    modifyMVar_ (cxThreads cx) (return . (tid:))
    return ()

-- | A thread to generate source signals and events will be started
-- when setup is complete.
input :: IO () -> Setup ()
input handler = do
  cx <- getContext
  setupIO $ do
    tid <- forkIO handler
    modifyMVar_ (cxThreads cx) (return . (tid:))
    return ()

-- | Runs a program defined by the setup computation. The simulation ends
-- if the returned event occurs.
runProgram :: (E Boot -> X Time -> Setup (E ())) -> IO ()
runProgram setup = do
  mv <- newMVar []
  epoch <- getCurrentTime
  let cx = Context mv epoch
  let time = TimeX cx
  (onBoot, boot) <- newInternalBoot cx
  let Setup act = setup onBoot time
  exit <- act cx
  --threadDelay 5000
  boot
  waitE exit
  _ <- withMVar mv (mapM killThread)
  return ()

-- | Print out events as they occur. Only for debugging purposes.
debugE :: (a -> String) -> E a -> E a
debugE toString e = unsafePerformIO $ do
  e' <- dupE e
  _ <- forkIO . forever $ do
    (x, _) <- readEIO e'
    putStrLn (toString x)
  return e

-- | Print out transitions in a signal. Only for debugging purposes.
debugX :: Eq a => ((a, a) -> String) -> X a -> X a
debugX toString sig =
  let diff a b = if a == b then Nothing else Just (a,b) in
  let e = edge diff sig in
  unsafePerformIO $ do
    _ <- forkIO $ do
      e' <- dupE e
      forever $ do
        (x, _) <- readEIO e'
        putStrLn (toString x)
    return sig

