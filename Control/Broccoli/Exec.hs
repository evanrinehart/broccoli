{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Control.Broccoli.Exec where

import Control.Applicative
import Control.Concurrent
import Data.IORef
import Control.Monad
import Data.Time
import System.Mem.StableName
--import Data.Map (Map)
--import qualified Data.Map as M
import Control.Exception
import Numeric
import System.IO
import Data.Maybe
import Data.List
import Data.Ord
import Data.Function
import Control.Concurrent.STM

import GHC.Prim (Any)
import Unsafe.Coerce

import Control.Broccoli.Eval
import Control.Broccoli.Combinators

-- Take a program and execute it in real time with real inputs.

-- The justification for why this ought to work goes here.
-- Once justification is determined.

data Context = Context
  { cxDeferIO :: [Trigger] -> IO ()
  , cxDeferredHookups :: IORef [IO ()]
  , cxDebuggers :: IORef [NodeName]
  , cxVisitedVars :: IORef [(NodeName, Any)]  -- Any = IORef (Time -> a)
  , cxFlushRef :: IORef [(Int, IO ())]
  , cxGenerator :: IORef Int
  }

type EdgeSet = [Int]

-- execute effects to setup runtime handlers
magicE :: Context
       -> E a
       -> (Time -> Time)
       -> (Time -> Time)
       -> EdgeSet
       -> ([a] -> Time -> IO ())
       -> IO ()
magicE cx e0 w wi es k = case e0 of
  ConstantE os -> do
    srcOrd <- takeSrcOrd cx
    let os' = case warp w of
                Forward  -> os
                Backward -> error "no time reversal"
    let f chunk = Trigger t' srcOrd es io where
                    t' = wi t
                    io = k vs t'
                    t = fst (head chunk)
                    vs = map snd chunk
    cxDeferIO cx . map f . groupBy (on (==) fst) $ os'
  FmapE f e -> magicE cx e w wi es (\vs t -> k (map f vs) t)
  JustE e -> magicE cx e w wi es $ \mvs t -> case catMaybes mvs of
    [] -> return ()
    vs -> k vs t
  UnionE e1 e2 -> do
    magicE cx e1 w wi [] k
    magicE cx e2 w wi es k
  DelayE e -> addToList (cxDeferredHookups cx) (magicDelayE cx e w wi es k)
  SnapshotE bias cons x e -> do
    ref <- newMagicVar cx bias x w wi
    magicE cx e w wi es $ \vs t -> do
      g <- readIORef ref
      k (map (cons (g t)) vs) t
  InputE hookup -> do
    srcOrd <- takeSrcOrd cx
    hookup srcOrd es wi k
  EdgeE x -> do
    let g0 = primPhase x
    ref <- newIORef g0
    edgeId <- newEdgeId (cxGenerator cx)
    magicX cx x w wi (edgeId:es) $ \g' t -> do
      deferFlush (cxFlushRef cx) edgeId $ do
        g <- readIORef ref
        writeIORef ref g'
        k [(g t, g' t)] t
  DebugE toString e -> do
    let ref = cxDebuggers cx
    name <- getNodeNameE e0
    saw <- readIORef ref
    if not (name `elem` saw)
      then do
        addToList ref name
        magicE cx e w wi es $ \vs t -> do
          forM_ vs $ \v -> do
            hPutStrLn stderr (unwords [showFFloat (Just 5) t "", toString v])
          k vs t
      else do
        magicE cx e w wi es (\vs t -> k vs t)

magicDelayE :: Context
            -> E (a, Double)
            -> (Time -> Time)
            -> (Time -> Time)
            -> EdgeSet
            -> ([a] -> Time -> IO ())
            -> IO ()
magicDelayE cx e w wi es k = do
  srcOrd <- takeSrcOrd cx
  magicE cx e w wi es $ \delayVs t -> do
    -- groups :: [[(Time, a)]]
    let groups = groupBy (on (==) fst)
               . sortBy (comparing fst)
               . map (\(v, dt) -> (t + dt, v))
               $ delayVs
    forM_ groups $ \chunk -> do -- vs :: [(Time, a)]
      let t' = fst (head chunk)
      let vs = map snd chunk
      cxDeferIO cx [Trigger t' srcOrd es (k vs t')]

magicX :: Context
       -> X a
       -> (Time -> Time)
       -> (Time -> Time)
       -> EdgeSet
       -> ((Time -> a) -> Time -> IO ())
       -> IO ()
magicX cx arg w wi es k = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX f x -> magicX cx x w wi es (\g t -> k (f . g) t)
  ApplX ff xx -> do
    let f0 = primPhase ff
    let x0 = primPhase xx
    ffref <- newIORef f0
    xxref <- newIORef x0
    magicX cx ff w wi [] $ \g t -> do
      writeIORef ffref g
      h <- readIORef xxref
      k (g <*> h) t
    magicX cx xx w wi es $ \g t -> do
      writeIORef xxref g
      h <- readIORef ffref
      k (h <*> g) t
  TrapX _ e -> case warp w of
    Forward  -> magicE cx e w wi es (\vs t -> k (const (last vs)) t)
    Backward -> error "simulation doesn't support time reversal"
{-
    Backward -> do
      let t' = wi 0
      let os = reverse . takeWhile ((<= t') . fst) $ occs e
      historyRef <- newIORef os
      valueRef <- newIORef (fromMaybe prim (snd <$> listToMaybe os))
      magicE cx e w wi $ \_ t -> do
        vPrev <- readIORef valueRef
        modifyIORef historyRef (drop 1)
        os' <- readIORef historyRef
        writeIORef valueRef (fromMaybe prim (snd <$> listToMaybe os'))
        case os' of
          [] -> k (patch (const prim) vPrev (w t)) t
          (_,v):_ -> k (patch (const v) vPrev (w t)) t
-}
  TimeWarpX u ui x -> magicX cx x (u . w) (wi . ui) es $ \g t -> do
    k (g . u) t

patch :: (Time -> a) -> a -> Time -> (Time -> a)
patch f v0 cutoff t | t == cutoff = v0
                    | otherwise = f t

newMagicVar :: forall a . Context
            -> Bias
            -> X a
            -> (Time -> Time)
            -> (Time -> Time)
            -> IO (IORef (Time -> a))
newMagicVar cx bias x w wi = do
  uid <- getNodeNameX x
  saw <- readIORef (cxVisitedVars cx)
  case lookup uid saw of
    Nothing -> do
      let phase = primPhase x
      ref <- newIORef phase
      --modifyIORef (cxVisitedVars cx) (M.insert uid (unsafeCoerce ref :: Any))
      modifyIORef (cxVisitedVars cx) ((uid, unsafeCoerce ref :: Any):)
      let hookup = magicX cx x w wi [] (\g _ -> writeIORef ref g)
      case bias of
        NowMinus -> addToList (cxDeferredHookups cx) hookup
        Now -> hookup
      return ref
    Just var -> return (unsafeCoerce var :: IORef (Time -> a))

addToList :: IORef [a] -> a -> IO ()
addToList ref x = modifyIORef ref (++[x])

listIsEmpty :: IORef [a] -> IO Bool
listIsEmpty ref = null <$> readIORef ref

whileM :: IO Bool -> IO a -> IO ()
whileM test action = do
  b <- test
  if b then action >> whileM test action else return ()

-- | Run a program in real time with a source of external input and an
-- output handler. The computation never terminates.
simulate :: (E a -> E b) -> IO a -> (Time -> b -> IO ()) -> IO ()
simulate prog getIn doOut = do
  thisThreadId <- myThreadId
  epochMv <- newEmptyMVar
  ref4 <- newIORef []
  (deferIO, dispThread) <- newScheduler epochMv thisThreadId ref4
  ref1 <- newIORef []
  ref2 <- newIORef []
  ref3 <- newIORef []
  genRef <- newIORef 0
  let cx = Context deferIO ref1 ref2 ref3 ref4 genRef
  inputHandlersRef <- newIORef []
  let inE = InputE
            (\so es wi hd -> addToList inputHandlersRef (so,es,wi,hd))
  let e = prog inE
  loopCheckE e [] [] ["output"]
  magicE cx e id id [] (\vs t -> mapM_ (doOut t) vs)
  repeatedlyExecuteDeferredHookups cx
  hds <- readIORef inputHandlersRef
  epoch <- getCurrentTime
  putMVar epochMv epoch
  flip finally (killThread dispThread) $ forever $ do
    v <- getIn
    t <- getSimulationTime epoch
    forM_ hds $ \(so,es,wi,hd) -> do
      let t' = wi t
      case compare t' t of
        EQ -> hd [v] t -- this is wrong because its not synced with dispatch
        LT -> hPutStrLn stderr "Warning: acausal input ignored"
        GT -> cxDeferIO cx [Trigger t' so es (hd [v] t')]


repeatedlyExecuteDeferredHookups :: Context -> IO ()
repeatedlyExecuteDeferredHookups cx = do
  let ref = cxDeferredHookups cx
  whileM (not <$> listIsEmpty ref) $ do
    ios <- readIORef ref
    writeIORef ref []
    sequence ios


-- | Simulate an event and print out the occurrences as they happen.
testE :: (a -> String) -> E a -> IO ()
testE toString e = simulate (const e) hang f where
  f t v = putStrLn (showFFloat (Just 5) t " " ++ toString v)

-- | Simulate a signal and print out values at the specified sample rate.
testX :: Int -> (a -> String) -> X a -> IO ()
testX 0 _ _ = error "testX: sample rate zero"
testX sr toString x = testE toString (snapshot' const x (pulse (srToPeriod sr)))

-- | Does nothing and never completes with any result. Useful as a dummy
-- input.
hang :: IO a
hang = do
  threadDelay (100 * 10^(6::Int))
  hang



-- The simulator relies on GHC stable names for observable sharing.

getNodeNameX :: X a -> IO NodeName
getNodeNameX x = do
  sn <- x `seq` makeStableName x
  return (fromStableName sn)

getNodeNameE :: E a -> IO NodeName
getNodeNameE e = do
  sn <- e `seq` makeStableName e
  return (fromStableName sn)

data NodeName = NodeName (StableName Any) deriving (Eq)

instance Show NodeName where
  show (NodeName sn) = show (hashStableName sn)

fromStableName :: StableName a -> NodeName
fromStableName sn = NodeName (unsafeCoerce sn)



-- A loop check to run before execution. This doesn't detect all loops, only
-- ones that would cause a freeze-up during initialization. Some loops are
-- ok.

crap :: [String] -> IO ()
crap path = fail msg where
  msg = "loop detected " ++ show (reverse path)

loopCheckE :: E a -> [NodeName] -> [NodeName] -> [String] -> IO ()
loopCheckE arg jumps curs path = case arg of
  ConstantE _ -> return ()
  FmapE _ e -> do
    i <- getNodeNameE arg
    let path' = ("fmapE("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e jumps (i:curs) path'
  JustE e -> do
    i <- getNodeNameE arg
    let path' = ("justE("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e jumps (i:curs) path'
  UnionE e1 e2 -> do
    i <- getNodeNameE arg
    let path' = ("unionE("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e1 jumps (i:curs) path'
    loopCheckE e2 jumps (i:curs) path'
  DelayE e -> do
    i <- getNodeNameE arg
    let path' = ("delayE("++show i++")") : path
    when (i `elem` curs) (crap path')
    j <- getNodeNameE e
    if j `elem` jumps
      then return ()
      else loopCheckE e (j:jumps) [] path'
  SnapshotE _ _ x e -> do
    i <- getNodeNameE arg
    let path' = ("snapshot("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e jumps (i:curs) path'
    j <- getNodeNameX x
    if j `elem` jumps
      then return ()
      else loopCheckX x (j:jumps) [] path'
  InputE _ -> return ()
  EdgeE x -> do
    i <- getNodeNameE arg
    let path' = ("edge("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckX x jumps (i:curs) path'
  DebugE _ e -> do
    i <- getNodeNameE arg
    let path' = ("debugE("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e jumps (i:curs) path'
  
loopCheckX :: X a -> [NodeName] -> [NodeName] -> [String] -> IO ()
loopCheckX arg jumps curs path = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX _ x -> do
    i <- getNodeNameX arg
    let path' = ("fmapX("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckX x jumps (i:curs) path'
  ApplX ff xx -> do
    i <- getNodeNameX arg
    let path' = ("<*>("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckX ff jumps (i:curs) path'
    loopCheckX xx jumps (i:curs) path'
  TrapX _ e -> do
    i <- getNodeNameX arg
    let path' = ("trap("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckE e jumps (i:curs) path'
  TimeWarpX _ _ x -> do
    i <- getNodeNameX arg
    let path' = ("timeWarp("++show i++")") : path
    when (i `elem` curs) (crap path')
    loopCheckX x jumps (i:curs) path'



-- The edge detector reacts to updates of a piecewise constant signal by
-- emitting an event containing the value at t- and the value at t+. More
-- precisely, if events occuring at the same time would cause the signal to
-- update more than once in the same t, only the initial value and the final
-- value will be reported in the event. And there will only be one event at t.

newEdgeId :: IORef Int -> IO Int
newEdgeId ref = do
  n <- readIORef ref
  modifyIORef ref succ
  return n

deferFlush :: IORef [(Int, IO ())] -> Int -> IO () -> IO ()
deferFlush ref flid action = modifyIORef ref deferRec where
  deferRec [] = [(flid, action)]
  deferRec ((flid',io):fls) | flid' == flid = (flid,action) : fls
                            | otherwise = (flid',io) : deferRec fls

cxFlush :: Int -> IORef [(Int, IO ())] -> IO ()
cxFlush i ref = do
  (set1, set2) <- partition ((== i) . fst) <$> readIORef ref
  writeIORef ref set2
  case set1 of
    [] -> return ()
    [(_, io)] -> io
    _ -> error "intermediate cxFlush invariant failed"

-- The dispatcher is a thread which sleeps until one of the conditions:
-- 1. a scheduled IO action must be executed
-- 2. an external agent wants something executed now

newScheduler :: MVar UTCTime
             -> ThreadId
             -> IORef [(Int, IO ())]
             -> IO ([Trigger] -> IO (), ThreadId)
newScheduler epochMv parentThread flushRef = do
  --tv <- newTVarIO M.empty
  tv <- newTVarIO []
  wake <- newTChanIO
  tid <- forkFinally (dispatcher epochMv tv wake flushRef) $ \ r -> case r of
    Left e -> throwTo parentThread e
    Right _ -> return ()
  return (schedule tv wake, tid)

schedule :: TVar [Trigger] -> TChan () -> [Trigger] -> IO ()
schedule tv wake timeActions = do
  atomically $ do
    q <- readTVar tv
    --let q' = M.alter (insertAction action) target q
    let q' = merge (comparing trigTime) q timeActions
    writeTVar tv q'
    writeTChan wake ()


dispatcher :: MVar UTCTime
           -> TVar [Trigger]
           -> TChan ()
           -> IORef [(Int, IO ())]
           -> IO ()
dispatcher epochMv tv wake flushRef = do
  epoch <- takeMVar epochMv
  forever $ do
    now <- getSimulationTime epoch
    (nextWake, variousIO) <- atomically $ do
      q <- readTVar tv
      let (lte, gt) = span ((<= now) . trigTime) q
      --let (lt, eq, gt) = M.splitLookup now q
      --let currents = fromMaybe [] eq
      writeTVar tv gt
      --return
        --( fmap (fst . fst) (M.minViewWithKey gt)
        --, concatMap snd (M.assocs lt) ++ currents )
      return (fmap trigTime (listToMaybe gt), lte)
    forM_ (groupBy (on (==) trigTime) variousIO) $ \sameTimeIOs -> do
      mapM trigIO sameTimeIOs
      testIs <- map fst <$> readIORef flushRef
      forM_ testIs (\i -> cxFlush i flushRef)
      -- fix this shit
    case nextWake of
      Nothing -> atomically (readTChan wake)
      Just tNext -> do
        let ms = ceiling (min (tNext - now) 10 * million)
        cancel <- cancellableThread $ do
          threadDelay ms
          atomically (writeTChan wake ())
        atomically (readTChan wake)
        cancel

million :: Double
million = 1e6

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


getSimulationTime :: UTCTime -> IO Double
getSimulationTime epoch = do
  now <- getCurrentTime
  let t = diffUTCTime now epoch
  return (realToFrac t)



data Trigger = Trigger
  { trigTime :: Time
  , trigOrd :: Int
  , trigEdges :: [Int]
  , trigIO :: IO () }

instance Show Trigger where
  show (Trigger a b c _) = unwords ["Trigger", show a, show b, show c, "_"]


takeSrcOrd :: Context -> IO Int
takeSrcOrd cx = do
  let ref = cxGenerator cx
  n <- readIORef ref
  writeIORef ref (n+1)
  return n
