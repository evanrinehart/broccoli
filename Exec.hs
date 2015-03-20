module Exec where

import Prog
import Eval
import IVar

-- take a program and execute it in real time with real inputs

newtype Setup a = Setup (Context -> IO a)

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

type Handler a = a -> Time -> IO ()

data Context = Context
  { cxDeferIO :: Time -> IO () -> IO
  , cxDeferredHookups :: IORef [IO ()]
  , cxVisitedVars :: IORef [Int]
  , cxThreads :: IORef [ThreadId]
  , cxLock :: MVar ()
  , cxEpochIv :: IVar UTCTime }

newContext :: IO Context
newContext = do
  epochIv <- newIVar
  (deferIO, tid) <- newScheduler epochIv
  visitedRef <- newIORef []
  threadsRef <- newIORef [tid]
  lockMv <- newMVar ()
  hookupsRef <- newIORef []
  return (Context deferIO hookupsRef visitedRef threadsRef lockMv epochIv)

runTest :: (a -> Time -> IO ()) -> E a -> IO ()
runTest action e = do
  cx <- newContext
  -- traverse e, scheduling constant events
  -- deferring hookups to delays and timewarps
  -- attaching actions to delays, timewarps, inputs, constants
  -- record snapshot variable node names to avoid more than one of each var
  --
  -- when done, execute deferred hookups, clearing the list in case
  -- more hookups are deferred in the process.
  -- repeat until no more deferred hookups appear.
  --
  -- write the current time to the epoch ivar
  hang -- finally cleanup
  

{-
data E a where
  ConstantE :: [(Time, a)] -> E a
  FmapE :: forall a b . (b -> a) -> E b -> E a
  JustE :: E (Maybe a) -> E a
  UnionE :: E a -> E a -> E a
  DelayE :: E (a, Double) -> E a
  SnapshotE :: forall a b c . a ~ (b,c) => E b -> X c -> E a
  InputE :: IORef [Handler a] -> E a
  Accum1E :: forall a b . a ~ (b,b) => b -> E b -> E a
  RasterE :: a ~ () => E a

data X a where
  PureX :: a -> X a
  TimeX :: a ~ Time => X a
  FmapX :: forall a b . (b -> a) -> X b -> X a
  ApplX :: forall a b . X (b -> a) -> X b -> X a
  TrapX :: a -> E a -> X a
  TimeWarpX :: (Time -> Time) -> (Time -> Time) -> X a -> X a
  InputX :: a -> IORef [Handler a] -> X a
-}

-- to run this thing, you need to traverse the program in a Setup monad.
-- this monad can do several things.
-- 1. save the fact that a snapshot variable has been created ... hmmrmm.
-- dont create it again and dont traverse its branch twice.
-- 2. defer setup of dispatchers that you encounter. (delay, timewarp)

magicE :: E a -> (a -> IO ()) -> IO ()
magicE e0 k = case e0 of
  ConstantE [] -> return ()
  ConstantE evs -> do
    uid <- getNodeName e0
    -- spawn dispatcher, provide callback
    return ()
  FmapE f e -> magicE e (\(x,t) -> k (f x, t))
  JustE e -> magicE e $ \(x,t) -> case x of
    Nothing -> return ()
    Just y -> (k y, t)
  UnionE e1 e2 -> do
    magicE e1 k
    magicE e2 k
  SnapshotE e sig iv -> do
    mref <- getVar sig
    ref <- case mref of
      Nothing -> do
        v0 <- initialValue sig
        newIORef v0
      Just ref -> return ref
    magicE e $ \(x,t) -> do
      g <- readTVar v
      k (x, y)
    magicX sig (\(g, _) -> writeIORef ref g)
  Mem1 x0 e -> do
    ref <- newIORef x0
    magicE e $ \(x',t) -> do
      x <- readIORef ref
      let ans = ((x, x'), t)
      writeIORef ref x'
      k ans
  DelayE e -> do
    -- spawn dispatcher, provide callback
  InputE ref = do
    ks <- readIORef ref
    writeIORef ref (ks ++ [k])





