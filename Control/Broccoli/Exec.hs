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

import GHC.Prim (Any)
import Unsafe.Coerce

import Control.Broccoli.Eval
import Control.Broccoli.Dispatch
import Control.Broccoli.Combinators

-- Take a program and execute it in real time with real inputs.

-- The justification for why this ought to work goes here.

data Context = Context
  { cxDeferIO :: [(Time, IO ())] -> IO ()
  , cxDeferredHookups :: IORef [IO ()]
  , cxDebuggers :: IORef [NodeName]
  , cxVisitedVars :: IORef [(NodeName, Any)]  -- Any = IORef (Time -> a)
  }

-- execute effects to setup runtime handler
magicE :: Context
       -> E a
       -> (Time -> Time)
       -> (Time -> Time)
       -> (a -> Time -> IO ())
       -> IO ()
magicE cx e0 w wi k = case e0 of
  ConstantE os -> case warp w of
    Forward  -> cxDeferIO cx (map (\(t,x) -> ((wi t), k x (wi t))) os)
    Backward -> cxDeferIO cx (map (\(t,x) -> ((wi t), k x (wi t))) (reverse os))
  FmapE f e -> magicE cx e w wi (\x t -> k (f x) t)
  JustE e -> magicE cx e w wi $ \x t -> case x of
    Nothing -> return ()
    Just y -> k y t
  UnionE e1 e2 -> do
    magicE cx e1 w wi k
    magicE cx e2 w wi k
  DelayE e -> addToList (cxDeferredHookups cx) (magicDelayE cx e w wi k)
  SnapshotE bias cons x e -> do
    ref <- newMagicVar cx bias x w wi
    magicE cx e w wi $ \v t -> do
      g <- readIORef ref
      k (cons (g t) v) t
  InputE hookup -> hookup wi k
  EdgeE x -> do
    let g0 = primPhase x
    ref <- newIORef g0
    magicX cx x w wi $ \g' t -> do
      g <- readIORef ref
      writeIORef ref g'
      k (g t, g' t) t
  DebugE toString e -> do
    let ref = cxDebuggers cx
    name <- getNodeNameE e0
    saw <- readIORef ref
    if not (name `elem` saw)
      then do
        addToList ref name
        magicE cx e w wi $ \v t -> do
          hPutStrLn stderr (unwords [showFFloat (Just 5) t "", toString v])
          k v t
      else do
        magicE cx e w wi (\v t -> k v t)

magicDelayE :: Context
            -> E (a, Double)
            -> (Time -> Time)
            -> (Time -> Time)
            -> (a -> Time -> IO ())
            -> IO ()
magicDelayE cx e w wi k = magicE cx e w wi $ \(x,dt) t -> do
  let t' = t + dt
  cxDeferIO cx [(t', k x t')]

magicX :: Context
       -> X a
       -> (Time -> Time)
       -> (Time -> Time)
       -> ((Time -> a) -> Time -> IO ())
       -> IO ()
magicX cx arg w wi k = case arg of
  PureX _ -> return ()
  TimeX -> return ()
  FmapX f x -> magicX cx x w wi (\g t -> k (f . g) t)
  ApplX ff xx -> do
    let f0 = primPhase ff
    let x0 = primPhase xx
    ffref <- newIORef f0
    xxref <- newIORef x0
    magicX cx ff w wi $ \g t -> do
      writeIORef ffref g
      h <- readIORef xxref
      k (g <*> h) t
    magicX cx xx w wi $ \g t -> do
      writeIORef xxref g
      h <- readIORef ffref
      k (h <*> g) t
  TrapX prim e -> case warp w of
    Forward  -> magicE cx e w wi (\x t -> k (const x) t)
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
  TimeWarpX tmap tmapInv x -> magicX cx x (tmap . w) (wi . tmapInv) $ \g t -> do
    k (g . tmap) t

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
      let hookup = magicX cx x w wi (\g _ -> writeIORef ref g)
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
whileM check action = do
  b <- check
  if b then action >> whileM check action else return ()

-- | Run a program in real time with a source of external input and an
-- output handler. The computation never terminates.
simulate :: (E a -> E b) -> IO a -> (Time -> b -> IO ()) -> IO ()
simulate prog getIn doOut = do
  epochMv <- newEmptyMVar
  (deferIO, dispThread) <- newScheduler epochMv
  ref1 <- newIORef []
  ref2 <- newIORef []
  ref3 <- newIORef []
  let cx = Context deferIO ref1 ref2 ref3
  inputHandlersRef <- newIORef []
  let inE = InputE (\wi hd -> do addToList inputHandlersRef (hd,wi))
  let e = prog inE
  loopCheckE e [] [] ["output"]
  magicE cx e id id (flip doOut)
  repeatedlyExecuteDeferredHookups cx
  hds <- readIORef inputHandlersRef
  epoch <- getCurrentTime
  putMVar epochMv epoch
  flip finally (killThread dispThread) $ forever $ do
    v <- getIn
    t <- getSimulationTime epoch
    forM_ hds $ \(hd,wi) -> do
      let t' = wi t
      case compare t' t of
        EQ -> hd v t
        LT -> hPutStrLn stderr "Warning: acausal input ignored"
        GT -> cxDeferIO cx [(t', hd v t')]


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
