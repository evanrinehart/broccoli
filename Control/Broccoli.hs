-- | Small experimental library for interactive functional programs.

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
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
  multiplex,
  delayE,
  delayX,
  dilate,
  timeWarp,
  timeWarp',
  delayE',
  rasterize,

  -- * Setup IO interface
  Setup,
  Time,
  DeltaT,
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
import Control.Monad (forever, ap, msum)
import Data.IORef
import Control.Concurrent
import Control.Concurrent.STM
import System.IO.Unsafe
import Data.Time
import Data.Sequence
import Data.Foldable (toList)
import Data.List (intercalate)

--import Debug.Trace
--import Unsafe.Coerce

-- | @X a@ represents time signals with values of type @a@.
-- 
-- > X a = Time -> a
data X a where
  PureX :: a -> X a
  TimeX :: X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  MappendX :: Monoid a => X a -> X a -> X a
  MultiX :: forall a b . a ~ [b] => [X b] -> X a
  PortX :: forall a b . a
        -> Either (X b) (E b)
        -> UID
        -> IVar (TVar (a,Time))
        -> IO [ThreadId]
        -> X a

-- | @E a@ represents events with values of type @a@.
-- 
-- > E a = [(a, Time)]
data E a where
  ConstantE :: [(a, Time)] -> E a
  FmapE     :: forall a b . (b -> a) -> E b -> E a
  MappendE  :: E a -> E a -> E a
  SnapshotE :: a ~ (b,c) => E b -> X c -> E a
  JustE     :: E (Maybe a) -> E a
  PortE     :: forall a b . Either (X b) (E b)
            -> UID
            -> IVar (ER a)
            -> (UTCTime -> IO (ER a))
            -> Int
            -> E a
  InputE :: UID -> IVar (ER a) -> (UTCTime -> IO ()) -> Int -> E a

-- you have steps in running a program
-- 1. replicate program 
-- 2. activate sources
-- 3. result should be IO (a, Time)

-- runtime event source
data ER a = ER
  { nextOcc    :: Time -> STM (Maybe (a, Time))
  , nextOcc'   :: Time -> STM (Maybe (a, Time))
  , allBefore  :: Time -> STM [(a, Time)]
  , allBefore' :: Time -> STM [(a, Time)] }

nullER :: ER a
nullER = ER
  { nextOcc _ = return Nothing
  , nextOcc _ = return Nothing
  , allBefore _ = return []
  , allBefore' _ = return [] }

type Activate a = UTCTime -> IO (ER a)

runE :: (Time -> a -> IO ()) -> E a -> IO ()
runE act e = do
  now <- getCurrentTime
  er <- activateE now e
  tref <- newIORef 0
  forever $ do
    t <- readIORef tref
    (x, t') <- waitE t er
    writeIORef tref t'
    act t' x

inputE :: (TChan a -> IO ()) -> E a
inputE work = InputE uid activate where
  uid = unsafePerformIO newUID
  eriv = unsafePerformIO newIVar
  activate epoch = do
    -- create a broad cast tchan
    -- create an empty database of event occs
    -- setup the ER to query and modify this database
    newBroadcastTChan 
    writeIVar eriv nullER

-- activate sources
-- replicate components, counting expected worker population
-- when numbers add up, fork input threads

-- leads to wanting more information about a running program
-- which is what i tried to do today anyway, set up component test bench :(
-- (also to fix the backward time warp)


activateE :: UTCTime -> E a -> IO (ER a)

waitE :: Time -> ER a -> IO (a, Time)
waitE t er = atomically $ do
  mr <- nextOcc er t
  case mr of
    Nothing -> retry
    Just xt -> return xt

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

type Time = Double

type DeltaT = Double

-- | The boot event occurs once at the beginning of a simulation.
type Boot = ()

data Context = Context
  { cxThreads :: MVar [ThreadId]
  , cxEpoch   :: UTCTime
  , cxDefer   :: Time -> IO () -> IO ()
  }

setupIO :: IO a -> Setup a
setupIO io = Setup (\_ -> io)

getContext :: Setup Context
getContext = Setup (\cx -> return cx)

getContextX :: X a -> Maybe Context
getContextX x = case x of
  PureX _ -> Nothing
  FmapX _ x' -> getContextX x'
  ApplX x1 x2 -> getFirst $ First (getContextX x1) <> First (getContextX x2)
  MappendX x1 x2 -> getFirst $ First (getContextX x1) <> First (getContextX x2)
  TimeX cx _ -> Just cx
  PortX _ cx _ -> Just cx
  MultiX xs -> msum (map getContextX xs)

getContextE :: E a -> Maybe Context
getContextE e = case e of
  NeverE -> Nothing
  FmapE _ e' -> getContextE e'
  MappendE e1 e2 -> getFirst $ First (getContextE e1) <> First (getContextE e2)
  SnapshotE e' x -> getFirst $ First (getContextE e') <> First (getContextX x)
  JustE e' -> getContextE e'
  PortE cx _ -> Just cx
  SingleE cx _ -> Just cx

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
  SingleE cx mv -> do
    x <- atomically (readTMVar mv)
    mv' <- newTMVarIO x
    return (SingleE cx mv')

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
  Normal a Double
    deriving Show

readE :: E a -> STM (EventResult a)
readE e = case e of
  NeverE -> return NotNowNotEver
  MappendE e1 e2 -> do
    mx <- readE e1
    case mx of
      TryLater -> do
        my <- readE e2
        case my of
          NotNowNotEver -> return TryLater
          other -> return other
      NotNowNotEver -> readE e2
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
  SingleE _ mv -> do
    attempt <- tryTakeTMVar mv
    case attempt of
      Nothing -> return NotNowNotEver
      Just v -> return (Normal v 0)

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
  TimeX _ tmap -> return (tmap time, tmap time)
  PortX _ _ tv -> readTVar tv
  MultiX xs -> do
    pairs <- mapM (readX time) xs
    let maxT = maximum (map snd pairs)
    return (map fst pairs, maxT)

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

showEventResult :: EventResult a -> String
showEventResult r = case r of
  TryLater -> "TryLater"
  Normal _ t -> "Normal ? " ++ show t
  DropThis -> "DropThis"
  NotNowNotEver -> "NotNowNotEver"

hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang

unsafeNewPortX :: Context -> a -> (TVar (a, Time) -> IO ()) -> X a
unsafeNewPortX cx v0 workLoop = PortX v0 cx tv where
  tv = unsafePerformIO $ do
    out <- newTVarIO (v0, 0)
    threadId <- forkIO (workLoop out)
    modifyMVar_ (cxThreads cx) (return . (threadId:))
    return out

unsafeNewPortE :: Context -> (TChan (a, Time) -> IO ()) -> E a
unsafeNewPortE cx workLoop = PortE cx ch where
  ch = unsafePerformIO $ do
    out <- newBroadcastTChanIO
    threadId <- forkIO (workLoop out)
    modifyMVar_ (cxThreads cx) (return . (threadId:))
    return out

---

-- | An event which gets the value of a signal when another event occurs.
snapshot :: E a -> X b -> E (a,b)
snapshot e x = SnapshotE e x

-- | Like 'snapshot' but ignores the original event's payload.
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

-- | Value of a signal at time zero.
initialValue :: X a -> a
initialValue sig = case sig of
  PureX v -> v
  TimeX _ tmap -> tmap 0
  PortX v0 _ _ -> v0
  FmapX f x -> f (initialValue x)
  ApplX ff xx -> (initialValue ff) (initialValue xx)
  MappendX x1 x2 -> mappend (initialValue x1) (initialValue x2)
  MultiX xs -> map initialValue xs

-- | Sum over events using an initial state and a state transition function.
accum :: s -> (a -> s -> s) -> E a -> X s
accum s0 trans e0 = case getContextE e0 of
  Nothing -> pure s0
  Just cx -> unsafeNewPortX cx s0 $ \tv -> do
    e <- dupE e0
    forever $ do
      atomically $ do
        mx <- readE e
        case mx of
          TryLater -> retry
          DropThis -> return ()
          Normal x t -> do
            (s,_) <- readTVar tv
            let s' = trans x s
            writeTVar tv (s',t)
          NotNowNotEver -> error "impossible (2)"

-- | A signal that remembers the most recent occurrence of an event.
trap :: a -> E a -> X a
trap x0 = accum x0 (\x _ -> x)

-- | An event that occurs on "edges" detected in a signal. The signal will
-- be rasterized if necessary for this to make sense.
edge :: (a -> a -> Maybe b) -> X a -> E b
edge diff sig = case getContextX sig of
  Nothing -> never
  Just cx -> unsafeNewPortE cx $ \out -> do
    let x = rasterize sig -- implicit rasterization ...
    ref <- newIORef (initialValue sig)
    forever $ do
      v <- readIORef ref
      (d, v', t) <- atomically $ do
        -- signal was rasterized so we don't need to fabricate any time here
        (v', t) <- readX undefined x
        case diff v v' of
          Just d  -> return (d, v', t)
          Nothing -> retry
      writeIORef ref v'
      atomically (writeTChan out (d, t))

showSignal :: X a -> String
showSignal sig = case sig of
  PureX _ -> "Pure ?"
  TimeX _ _ -> "TimeX ? ?"
  PortX _ _ _ -> "PortX ? ? ?"
  FmapX _ x -> "FmapX ? (" ++ showSignal x ++ ")"
  ApplX ff xx -> "ApplX ("++showSignal ff++") ("++showSignal xx++")"
  MappendX x1 x2 -> "Mappend ("++showSignal x1++") ("++showSignal x2++")"
  MultiX xs -> "MultiX ["++intercalate "," (map showSignal xs)++"]"

-- | Rasterize a signal. If there are several edge tests on a continuous
-- signal then it's better to explicitly rasterize before.
rasterize :: X a -> X a
rasterize sig = case getContextX sig of
  Nothing -> sig
  Just cx -> case containsTimeX sig of
    False -> sig
    True -> unsafeNewPortX cx (initialValue sig) $ \tv -> do
      let period = 0.01
      counterRef <- newIORef 0
      forever $ do
        counter <- readIORef counterRef
        let target = counter * period
        atomically (readX target sig >>= writeTVar tv)
        now <- chron (cxEpoch cx)
        let newTarget = (counter+1) * period
        writeIORef counterRef (counter+1)
        let ms = ceiling ((newTarget - now) * million)
        threadDelay ms

containsTimeX :: X a -> Bool
containsTimeX x = case x of
  PureX _ -> False
  FmapX _ x' -> containsTimeX x'
  ApplX x1 x2 -> containsTimeX x1 || containsTimeX x2
  MappendX x1 x2 -> containsTimeX x1 || containsTimeX x2
  TimeX _ _ -> True
  PortX _ _ _ -> False
  MultiX xs -> or (map containsTimeX xs)

-- | From many signals, one.
multiplex :: [X a] -> X [a]
multiplex sigs = MultiX sigs

-- | Like 'delayE' but the amount of delay is determined on a per-event basis.
delayE' :: E (a, DeltaT) -> E a
delayE' src = case getContextE src of
  Nothing -> never
  Just cx -> unsafeNewPortE cx $ \out -> do
    e <- dupE src
    forever $ do
      ((v,dt), t) <- readEIO e
      let t' = t + max dt 0
      let io = atomically (writeTChan out (v, t'))
      cxDefer cx t' io

-- | Delay occurrences of an event.
delayE :: DeltaT -> E a -> E a
delayE delta e = delayE' (fmap (,delta) e)

-- | Shift a signal ahead in time.
delayX :: DeltaT -> X a -> X a
delayX delta = timeWarp' (subtract delta) (+delta)

-- | Slow down a signal by a factor.
dilate :: Double -> X a -> X a
dilate rate = timeWarp' (/rate) (*rate)

-- | Time warp a signal.
timeWarp :: (Time -> Time) -> X a -> X a
timeWarp g sig = case sig of
  PureX _ -> sig
  TimeX cx f -> TimeX cx (f . g)
  PortX _ _ _ -> error "timeWarp: Can't handle events. Try timeWarp'."
  FmapX f x -> FmapX f (timeWarp g x)
  ApplX ff xx -> ApplX (timeWarp g ff) (timeWarp g xx)
  MappendX x1 x2 -> MappendX (timeWarp g x1) (timeWarp g x2)
  MultiX xs -> MultiX (map (timeWarp g) xs)

-- | Like 'timeWarp' but works with events. The inverse of the warp function
-- must exist and be provided.
timeWarp' :: (Time -> Time)
          -> (Time -> Time) -- ^ inverse of warp
          -> X a
          -> X a
timeWarp' g ginv sig = case sig of
  PureX _ -> sig
  TimeX cx f -> TimeX cx (f . g)
  PortX v0 cx tv -> warpPortX v0 cx tv ginv
  FmapX f x -> FmapX f (timeWarp' g ginv x)
  ApplX ff xx -> ApplX (timeWarp' g ginv ff) (timeWarp' g ginv xx)
  MappendX x1 x2 -> MappendX (timeWarp' g ginv x1) (timeWarp' g ginv x2)
  MultiX xs -> MultiX (map (timeWarp' g ginv) xs)

-- | Creates a new input signal with an initial value. Use 'input' to feed
-- data to the signal during the simulation.
newX :: a -> Setup (X a, a -> IO ())
newX v = do
  cx <- getContext
  let epoch = cxEpoch cx
  tv <- setupIO (newTVarIO (v,0))
  return
    ( PortX v cx tv
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
-- if the returned event occurs. The provided time signal is in units
-- of seconds with zero at the beginning of the simulation.
runProgram :: (E Boot -> X Time -> Setup (E ())) -> IO ()
runProgram setup = do
  mv <- newMVar []
  epoch <- getCurrentTime
  defer <- newScheduler epoch mv
  let cx = Context mv epoch defer
  let time = TimeX cx id
  onBoot <- SingleE cx <$> newTMVarIO ()
  let Setup act = setup onBoot time
  exit <- act cx
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

-- | Print out transitions in a signal, rasterizing if necessary. Only for debugging purposes.
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

chron :: UTCTime -> IO Double
chron epoch = do
  now <- getCurrentTime
  let time = diffUTCTime now epoch
  return (realToFrac time)

-- move changes in a signal to the future
warpPortX :: a -> Context -> TVar (a, Time) -> (Time -> Time) -> X a
warpPortX v0 cx srcTV ginv = unsafeNewPortX cx v0 $ \tv -> do
  latest <- newIORef 0
  forever $ do
    t <- readIORef latest
    (v,t') <- atomically $ do
      (v, t') <- readTVar srcTV
      if t' > t then return (v,t') else retry
    writeIORef latest t'
    let t'' = ginv t'
    let io = atomically (writeTVar tv (v,t''))
    -- at this point we can decide to drop events that were mapped into the past
    -- or to map them to the current time
    cxDefer cx (max t'' t') io

newScheduler :: UTCTime -> MVar [ThreadId] -> IO (Time -> IO () -> IO ())
newScheduler epoch threads = do
  seqMv <- newMVar Data.Sequence.empty
  wake <- newChan
  tid <- forkIO (dispatcher epoch wake seqMv)
  modifyMVar_ threads (return . (tid:))
  return $ \targetT io -> modifyMVar_ seqMv $ \queue -> do
    let (seqL, seqR) = spanl (\(t, _) -> t <= targetT) queue
    let seq' = seqL >< ((targetT, io) <| seqR)
    writeChan wake ()
    return seq'

dispatcher :: UTCTime -> Chan () -> MVar (Seq (Time, IO ())) -> IO ()
dispatcher epoch wake mv = forever $ do
  now <- chron epoch
  nextWake <- modifyMVar mv $ \queue -> do
    let (seqL, seqR) = spanl (\(t, _) -> t <= now) queue
    mapM_ snd (toList seqL)
    case viewl seqR of
      EmptyL -> return (seqR, Nothing)
      (t', _) :< _ -> return (seqR, Just t')
  case nextWake of
    Nothing -> readChan wake
    Just tNext -> do
      let ms = ceiling (min (tNext - now) 10 * million)
      cancel <- cancellableThread (threadDelay ms >> writeChan wake ())
      readChan wake
      cancel

million :: Double
million = toEnum (10^(6::Int))

cancellableThread :: IO () -> IO (IO ())
cancellableThread io = do
  mv <- newEmptyMVar
  tid <- forkIO $ do
    io
    _ <- tryTakeMVar mv
    return ()
  putMVar mv tid
  return $ do
    mtarget <- tryTakeMVar mv
    case mtarget of
      Nothing -> return ()
      Just target -> killThread target

sampleX :: X a -> Time -> a
sampleX sig t = case sig of
  PureX v -> v
  TimeX _ tmap -> tmap t
  PortX _ _ _ -> error "sampleX expects time-only signals"
  FmapX f x -> f (sampleX x t)
  ApplX ff xx -> (sampleX ff t) (sampleX xx t)
  MappendX x1 x2 -> mappend (sampleX x1 t) (sampleX x2 t)
  MultiX xs -> map (flip sampleX t) xs

-- write once variable -- reading before writing blocks until written
data IVar a = IVar (TVar (Maybe a))

newIVar :: IO (IVar a)
newIVar = do
  tv <- newTVarIO Nothing
  return (IVar tv)

readIVarIO :: IVar a -> IO a
readIVarIO iv = atomically (readIVar iv)

readIVar :: IVar a -> STM a
readIVar (IVar tv) = 
  mx <- readTVar tv
  case mx of
    Nothing -> retry
    Just x -> return x

writeIVar :: IVar a -> a -> STM ()
writeIVar (IVar tv) x = do
  mx <- readTVar tv
  case mx of
    Nothing -> writeTVar tv x
    Just _ -> error "tried to write an IVar twice"

writeIVarIO :: IVar a -> a -> IO ()
writeIVarIO iv x = atomically (writeIVar iv x)

dupIVar :: IVar a -> STM (IVar a)
dupIVar (IVar tv) = do
  prev <- readTVar tv
  tv' <- newTVar prev
  return (IVar tv')

isBlankIVar :: IVar a -> STM Bool
isBlankIVar (IVar tv) = do
  mx <- readTVar tv
  case mx of
    Nothing -> True
    Just _ -> False


type UID = Integer
newUID :: IO UID
newUID = randomRIO (0, 2^128-1)
