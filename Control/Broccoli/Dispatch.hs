module Control.Broccoli.Dispatch where

import Control.Monad
import Control.Concurrent
import Control.Concurrent.STM
import Data.Map (Map)
import qualified Data.Map as M
import Data.Time
import Data.Maybe
import Data.Ord

import Control.Broccoli.Eval
import Control.Broccoli.IVar


-- so there is one static dispatcher. its like got a [(Time, IO ())]
-- when you encounter a ConstantE you schedule all the events with all the
-- others your events go after any scheduled at the current time.
-- the type of the value being dispatched is hidden by partial application.
-- so the static dispatcher object is Time -> [IO ()]
--
-- since we are also going to want to schedule similar actions for the future
-- during the simulation, might as well merge this thing with the dynamic
-- dispatcher.
--
-- ===
--
-- 1. triggers from input
-- 2. triggers from constant events (possibly infinite)
-- 3. triggers from delays and timewarps
--
-- the map implementation doesnt work with infinite lists, so we should have
-- one dispatcher for "real time" events and another which has all the
-- possibly infinite constant events merged. the infinite list is then
-- incrementally "pre-dispatched" periodically into the real dispatcher.
-- 
-- but for new we can just put everything in the same infinite list.

newScheduler :: IVar UTCTime -> IO ([(Time, IO ())] -> IO (), ThreadId)
newScheduler epochIv = do
  --tv <- newTVarIO M.empty
  tv <- newTVarIO []
  wake <- newTChanIO
  tid <- forkIO (dispatcher epochIv tv wake)
  return (schedule tv wake, tid)

schedule :: TVar [(Time, IO ())] -> TChan () -> [(Time, IO ())] -> IO ()
schedule tv wake timeActions = do
  atomically $ do
    q <- readTVar tv
    --let q' = M.alter (insertAction action) target q
    let q' = merge (comparing fst) q timeActions
    writeTVar tv q'
    writeTChan wake ()

-- we want new events at the same time to go last
--insertAction :: a -> Maybe [a] -> Maybe [a]
--insertAction x Nothing = Just [x]
--insertAction x (Just xs) = Just (xs ++ [x])

-- the dispatcher is responsive for execute the effects of
-- 1. constant event occurrence lists
-- 2. events that happen in real time
-- 3. events that were scheduled into the future by something
-- 4. the rasterizer (if anything uses it)
-- everything except raster actions happen in the order they are specified
-- in the program, if they happen to occur at the same time. raster effects
-- happen after all those, in the order rasterizers were specified in the
-- program.
dispatcher :: IVar UTCTime
           -> TVar [(Time, IO ())] -- -> TVar (Map Time [IO ()])
           -> TChan ()
           -> IO ()
dispatcher epochIv tv wake = do
  epoch <- readIVarIO epochIv
  forever $ do
    now <- getSimulationTime epoch
    (nextWake, ios) <- atomically $ do
      q <- readTVar tv
      let (lte, gt) = span ((<= now) . fst) q
      --let (lt, eq, gt) = M.splitLookup now q
      --let currents = fromMaybe [] eq
      writeTVar tv gt
      --return
        --( fmap (fst . fst) (M.minViewWithKey gt)
        --, concatMap snd (M.assocs lt) ++ currents )
      return (fmap fst (listToMaybe gt), map snd lte)
    sequence_ ios
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


getSimulationTime :: UTCTime -> IO Double
getSimulationTime epoch = do
  now <- getCurrentTime
  let t = diffUTCTime now epoch
  return (realToFrac t)

