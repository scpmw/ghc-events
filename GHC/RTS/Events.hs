{-# LANGUAGE CPP,BangPatterns,PatternGuards #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}
{-
 - Author: Donnie Jones, Simon Marlow
 - Events.hs
 -   Parser functions for GHC RTS EventLog framework.
 -}
 
module GHC.RTS.Events (
       -- * The event log types                       
       EventLog(..),
       EventType(..),
       Event(..),
       EventTypeSpecificInfo(..),
       ThreadStopStatus(..),
       Header(..),
       Data(..),
       CapsetType(..),
       Timestamp,
       ThreadId,

       -- * Reading and writing event logs
       readEventLogFromFile,
       writeEventLogToFile,

       -- * Utilities
       CapEvent(..), sortEvents, groupEvents, sortGroups,
       buildEventTypeMap,

       -- * Printing
       showEventTypeSpecificInfo, showThreadStopStatus,
       ppEventLog, ppEventType, ppEvent
  ) where

{- Libraries. -}
import Data.Word (Word16, Word32, Word64, Word8)
import Data.Attoparsec as P
import Control.Monad
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Binary (Binary, put)
import Data.Binary.Put
import Control.Monad.Reader
import qualified Data.ByteString.Lazy as L
import qualified Data.ByteString as S
import Data.Char
import Data.Function
import Data.List
import Data.Either
import Data.Maybe
import Text.Printf
import Data.Array
import Numeric (showHex)

import Data.Bits

import System.IO

#define EVENTLOG_CONSTANTS_ONLY
#include "EventLogFormat.h"

{- Type synonyms. -}

-- EventType.
type EventTypeNum = Word16
type EventTypeDescLen = Word32
type EventTypeDesc = String
type EventTypeSize = Word16
-- Event.
type Timestamp = Word64
type ThreadId = Word32
type CapNo = Word16
type Marker = Word32

sz_cap, sz_time, sz_tid, sz_old_tid, sz_capset, sz_capset_type :: EventTypeSize
sz_cap  = 2
sz_time = 8
sz_tid  = 4
sz_old_tid  = 8 -- GHC 6.12 was using 8 for ThreadID when declaring the size
                -- of events, but was actually using 32 bits for ThreadIDs
sz_capset = 4
sz_capset_type = 2

{-
 - Data type delcarations to build the GHC RTS data format,
 - which is a (header, data) pair.
 -
 - Header contains EventTypes.
 - Data contains Events.
 -}
data EventLog =
  EventLog {
    header :: Header,
    dat    :: Data
  } deriving Show

newtype Header = Header {
     eventTypes :: [EventType]
  } deriving (Show, Eq)

data Data = Data {
     events :: [Event]
  } deriving Show

data EventType =
  EventType {
    num  :: EventTypeNum,
    desc :: EventTypeDesc,
    size :: Maybe EventTypeSize -- ^ 'Nothing' indicates variable size
  } deriving (Show, Eq)

data Event = 
  Event {
    time :: {-# UNPACK #-}!Timestamp,
    spec :: EventTypeSpecificInfo
  } deriving Show

data EventTypeSpecificInfo
  = Startup            { n_caps :: Int
                       }
  | EventBlock         { end_time     :: Timestamp, 
                         cap          :: Int, 
                         block_events :: [Event]
                       }
  | CreateThread       { thread :: {-# UNPACK #-}!ThreadId
                       }
  | RunThread          { thread :: {-# UNPACK #-}!ThreadId 
                       }
  | StopThread         { thread :: {-# UNPACK #-}!ThreadId,
                         status :: ThreadStopStatus
                       }
  | ThreadRunnable     { thread :: {-# UNPACK #-}!ThreadId
                       }
  | MigrateThread      { thread :: {-# UNPACK #-}!ThreadId,
                         newCap :: {-# UNPACK #-}!Int
                       }
  | RunSpark           { thread :: {-# UNPACK #-}!ThreadId
                       }
  | StealSpark         { thread :: {-# UNPACK #-}!ThreadId,
                         victimCap :: {-# UNPACK #-}!Int
                       }
  | CreateSparkThread  { sparkThread :: {-# UNPACK #-}!ThreadId
                       }
  | WakeupThread       { thread :: {-# UNPACK #-}!ThreadId, 
                         otherCap :: {-# UNPACK #-}!Int
                       }
  | Shutdown           { }
  | RequestSeqGC       { }
  | RequestParGC       { }
  | StartGC            { }
  | GCWork             { }
  | GCIdle             { }
  | GCDone             { }
  | EndGC              { }
  | CapsetCreate       { capset     :: {-# UNPACK #-}!Word32
                       , capsetType :: CapsetType
                       }
  | CapsetDelete       { capset :: {-# UNPACK #-}!Word32
                       }
  | CapsetAssignCap    { capset :: {-# UNPACK #-}!Word32
                       , cap    :: {-# UNPACK #-}!Int
                       }
  | CapsetRemoveCap    { capset :: {-# UNPACK #-}!Word32
                       , cap    :: {-# UNPACK #-}!Int
                       }
  | RtsIdentifier      { capset :: {-# UNPACK #-}!Word32
                       , rtsident :: String
                       }
  | ProgramArgs        { capset :: {-# UNPACK #-}!Word32
                       , args   :: [String]
                       }
  | ProgramEnv         { capset :: {-# UNPACK #-}!Word32
                       , env    :: [String]
                       }
  | OsProcessPid       { capset :: {-# UNPACK #-}!Word32
                       , pid    :: {-# UNPACK #-}!Word32
                       }
  | OsProcessParentPid { capset :: {-# UNPACK #-}!Word32
                       , ppid   :: {-# UNPACK #-}!Word32
                       }
  | Message            { msg :: String }
  | UserMessage        { msg :: String }
  | HpcModule          { modName :: String, modCount :: Word32, modHash :: Word32, modBase :: Word32 }
  | TickDump           { cap :: {-# UNPACK #-}!Int,
                         dump :: [(Word32, Word32)] }
  | InstrPtrSample     { cap :: {-# UNPACK #-}!Int,
                         ips :: [Word32] }
  | Blackhole          { ip :: Word32 }
  | UnknownEvent       { ref  :: {-# UNPACK #-}!EventTypeNum }
  | ErrorEvent         { errorMsg :: String }

  deriving Show


--sync with ghc/includes/Constants.h
data ThreadStopStatus
 = NoStatus
 | HeapOverflow
 | StackOverflow
 | ThreadYielding
 | ThreadBlocked
 | ThreadFinished
 | ForeignCall
 | BlockedOnMVar
 | BlockedOnBlackHole
 | BlockedOnRead
 | BlockedOnWrite
 | BlockedOnDelay
 | BlockedOnSTM
 | BlockedOnDoProc
 | BlockedOnCCall
 | BlockedOnCCall_NoUnblockExc
 | BlockedOnMsgThrowTo
 | ThreadMigrating
 | BlockedOnMsgGlobalise
 | BlockedOnBlackHoleOwnedBy {-# UNPACK #-}!ThreadId
 deriving (Show)

mkStat :: Int -> ThreadStopStatus
mkStat n = case n of
 0  ->  NoStatus
 1  ->  HeapOverflow
 2  ->  StackOverflow
 3  ->  ThreadYielding
 4  ->  ThreadBlocked
 5  ->  ThreadFinished
 6  ->  ForeignCall
 7  ->  BlockedOnMVar
 8  ->  BlockedOnBlackHole
 9  ->  BlockedOnRead
 10 ->  BlockedOnWrite
 11 ->  BlockedOnDelay
 12 ->  BlockedOnSTM
 13 ->  BlockedOnDoProc
 14 ->  BlockedOnCCall
 15 ->  BlockedOnCCall_NoUnblockExc
 16 ->  BlockedOnMsgThrowTo
 17 ->  ThreadMigrating
 18 ->  BlockedOnMsgGlobalise
 _  ->  error "mkStat"

maxStat :: Int
maxStat = 18

data CapsetType
 = CapsetCustom
 | CapsetOsProcess
 | CapsetClockDomain
 | CapsetUnknown
 deriving Show

mkCapsetType :: Word16 -> CapsetType
mkCapsetType n = case n of
 1 -> CapsetCustom
 2 -> CapsetOsProcess
 3 -> CapsetClockDomain
 _ -> CapsetUnknown

-- reader/Get monad that passes around the event types
type GetEvents a = ReaderT EventParsers Parser a

newtype EventParsers = EventParsers (Array Int (Maybe EventType, GetEvents EventTypeSpecificInfo))

type GetHeader a = Parser a

class Parseable a where
  getH :: Parser a

instance Parseable Word8 where
  getH = anyWord8
instance Parseable Word16 where
  getH = do b1 <- anyWord8
            b2 <- anyWord8
            return ((fromIntegral b1 `shift` 8) .|.
                    (fromIntegral b2))
instance Parseable Word32 where
  getH = do b1 <- anyWord8
            b2 <- anyWord8
            b3 <- anyWord8
            b4 <- anyWord8
            return ((fromIntegral b1 `shift` 24) .|.
                    (fromIntegral b2 `shift` 16) .|.
                    (fromIntegral b3 `shift` 8) .|.
                    (fromIntegral b4))
instance Parseable Word64 where
  getH = do b1 <- anyWord8
            b2 <- anyWord8
            b3 <- anyWord8
            b4 <- anyWord8
            b5 <- anyWord8
            b6 <- anyWord8
            b7 <- anyWord8
            b8 <- anyWord8
            return ((fromIntegral b1 `shift` 56) .|.
                    (fromIntegral b2 `shift` 48) .|.
                    (fromIntegral b3 `shift` 40) .|.
                    (fromIntegral b4 `shift` 32) .|.
                    (fromIntegral b5 `shift` 24) .|.
                    (fromIntegral b6 `shift` 16) .|.
                    (fromIntegral b7 `shift` 8) .|.
                    (fromIntegral b8))

getE :: Parseable a => GetEvents a
getE = lift getH
{-# INLINE getE #-}

------------------------------------------------------------------------------
-- Binary instances

getEventType :: GetHeader EventType
getEventType = do
           etNum <- getH
           s <- getH :: GetHeader EventTypeSize
           let etSize = if s == 0xffff then Nothing else Just s
           -- 0xffff indicates variable-sized event
           etDescLen <- getH :: GetHeader EventTypeDescLen
           etDesc <- fmap (map (chr . fromIntegral) . S.unpack) $ P.take (fromIntegral etDescLen) 
           etExtraLen <- getH :: GetHeader Word32
           _ <- P.take (fromIntegral etExtraLen)
           ete <- getH :: GetHeader Marker
           when (ete /= EVENT_ET_END) $
              fail ("Event Type end marker not found.")
           return (EventType etNum etDesc etSize)

getHeader :: GetHeader Header
getHeader = do
           hdrb <- getH :: GetHeader Marker
           when (hdrb /= EVENT_HEADER_BEGIN) $
                fail "Header begin marker not found"
           hetm <- getH :: GetHeader Marker
           when (hetm /= EVENT_HET_BEGIN) $ 
                fail "Header Event Type begin marker not found"
           ets <- getEventTypes
           emark <- getH :: GetHeader Marker
           when (emark /= EVENT_HEADER_END) $
                fail "Header end marker not found"
           return (Header ets)
     where
       getEventTypes :: GetHeader [EventType]
       getEventTypes = do
           m <- getH :: GetHeader Marker
           case () of
            _ | m == EVENT_ET_BEGIN -> do
                   et <- getEventType
                   nextET <- getEventTypes
                   return (et : nextET)
              | m == EVENT_HET_END ->
                   return []
              | otherwise ->
                   fail "Malformed list of Event Types in header"

getEvent :: GetEvents Event
getEvent = do
  EventParsers parsers <- ask
  etRef <- getE :: GetEvents EventTypeNum
  guard $ inRange (bounds parsers) (fromIntegral etRef)
  !ts   <- getE
  spec <- snd $ parsers ! fromIntegral etRef
  return (Event ts spec)

-- Our event log format allows new fields to be added to events over
-- time.  This means that our parser must be able to handle:
--
--  * old versions of an event, with fewer fields than expected,
--  * new versions of an event, with more fields than expected
--
-- The event log file declares the size for each event type, so we can
-- select the correct parser for the event type based on its size.  We
-- do this once after parsing the header: given the EventTypes, we build 
-- an array of event parsers indexed by event type.
--
-- For each event type, we may have multiple parsers for different
-- versions of the event, indexed by size.  These are listed in the
-- eventTypeParsers list below.  For the given log file we select the
-- parser for the most recent version (largest size less than the size
-- declared in the header).  If this is a newer version of the event
-- than we understand, there may be extra bytes that we have to read
-- and discard in the parser for this event type.
--
-- Summary:
--   if size is smaller that we expect:
--     parse the earier version, or ignore the event
--   if size is just right:
--     parse it
--   if size is too big:
--     parse the bits we understand and discard the rest

mkEventTypeParsers :: IntMap EventType
                   -> Array Int (Maybe EventType, GetEvents EventTypeSpecificInfo)
mkEventTypeParsers etypes
 = accumArray (flip const) undefined (0, max_event_num)
    ([ (num, (Nothing, undeclared_etype num)) | num <- [0..max_event_num] ] ++
     [ (num, (Just etype, parser num etype)) | (num, etype) <- M.toList etypes ])
  where
    max_event_num = maximum (M.keys etypes)
    undeclared_etype num = fail ("undeclared event type: " ++ show num)

    parser num etype =
         let
             possible = case Map.lookup (desc etype) eventTypeParsers of
               Nothing -> []
               Just ps -> ps
             mb_et_size = size etype
         in
         case mb_et_size of
           Nothing -> case Map.lookup (desc etype) variableEventTypeParsers of
                        Nothing -> noEventTypeParser num mb_et_size
                        Just p  -> p

           -- special case for GHC 6.12 EVENT_STOP_THREAD.  GHC 6.12
           -- was mis-reporting the event sizes (ThreadIds were
           -- counted as 8 instead of 4), and when we expanded the
           -- EVENT_STOP_THREAD to include an extra field, the new
           -- size is the same as that reported by 6.12, so we can't
           -- tell them apart by size.  Hence the special case here
           -- checks the size of the EVENT_CREATE_THREAD event to see
           -- whether we should be parsing the 6.12 STOP_THREAD or the
           -- 7.2 STOP_THREAD.  If the CREATE_THREAD extended in the
           -- future this might go wrong.

           Just et_size
             | et_size == sz_old_tid + 2,
               num == EVENT_STOP_THREAD,
                Just et <- M.lookup EVENT_CREATE_THREAD etypes,
                size et == Just sz_old_tid ->
                do  -- (thread, status)
                  t <- getE
                  s <- getE :: GetEvents Word16
                  let stat = fromIntegral s
                  return StopThread{thread=t, status = if stat > maxBound
                                                          then NoStatus
                                                          else mkStat stat}

           Just et_size ->
             case [ (sz,p) | (sz,p) <- possible, sz <= et_size ] of
               [] -> noEventTypeParser num mb_et_size
               ps -> let (sz, best) = maximumBy (compare `on` fst) ps
                     in  if sz == et_size
                            then best
                            else do r <- best
                                    _ <- lift $ P.take (fromIntegral (et_size - sz))
                                    return r


eventTypeParsers :: Map String [(EventTypeSize, GetEvents EventTypeSpecificInfo)]
eventTypeParsers = foldl (\t (k, v) -> Map.insertWith' (++) k [v] t) Map.empty [
 ("Startup",
  (sz_cap, do -- (n_caps)
      c <- getE :: GetEvents CapNo
      return Startup{ n_caps = fromIntegral c }
   )),

 ("Block marker",
  (4 + sz_time + sz_cap, do -- (size, end_time, cap)
      block_size <- getE :: GetEvents Word32
      end_time <- getE :: GetEvents Timestamp
      c <- getE :: GetEvents CapNo
      block <- lift $ P.take $ fromIntegral block_size - 24
      e <- ask
      let parseEvents = flip runReaderT e $ getEvents end_time []
      return $! case parseOnly parseEvents block of
        Left err  -> ErrorEvent $ "Faulty event block: " ++ err
        Right evs -> EventBlock { end_time = end_time,
                                  cap = fromIntegral c,
                                  block_events = evs }
   )),

 ("Create thread",
  (sz_tid, do  -- (thread)
      t <- getE
      return CreateThread{thread=t}
   )),

 ("Run thread",
  (sz_tid, do  --  (thread)
      t <- getE
      return RunThread{thread=t}
   )),

 ("Stop thread",
  (sz_tid + 2, do  -- (thread, status)
      t <- getE
      s <- getE :: GetEvents Word16
      let stat = fromIntegral s
      return StopThread{thread=t, status = if stat > maxBound
                                              then NoStatus
                                              else mkStat stat}
   )),

 ("Stop thread",
  (sz_tid + 2 + sz_tid, do  -- (thread, status, info)
      t <- getE
      s <- getE :: GetEvents Word16
      i <- getE :: GetEvents ThreadId
      let stat = fromIntegral s
      return StopThread{thread = t,
                        status = case () of
                                  _ | stat > maxStat
                                    -> NoStatus
                                    | stat == 8 {- XXX yeuch -}
                                    -> BlockedOnBlackHoleOwnedBy i
                                    | otherwise
                                    -> mkStat stat}
   )),

 ("Thread runnable",
  (sz_tid, do  -- (thread)
      t <- getE
      return ThreadRunnable{thread=t}
   )),

 ("Migrate thread",
  (sz_tid + sz_cap, do  --  (thread, newCap)
      t  <- getE
      nc <- getE :: GetEvents CapNo
      return MigrateThread{thread=t,newCap=fromIntegral nc}
   )),

 ("Run spark",
  (sz_tid, do  -- (thread)
      t <- getE
      return RunSpark{thread=t}
   )),

 ("Steal spark",
  (sz_tid + sz_cap, do  -- (thread, victimCap)
      t  <- getE
      vc <- getE :: GetEvents CapNo
      return StealSpark{thread=t,victimCap=fromIntegral vc}
   )),

 ("Create spark thread",
  (sz_tid, do  -- (sparkThread)
      st <- getE :: GetEvents ThreadId
      return CreateSparkThread{sparkThread=st}
   )),

 ("Shutdown", (0, return Shutdown)),

 ("Wakeup thread",
  (sz_tid + sz_cap, do  -- (thread, other_cap)
      t <- getE
      oc <- getE :: GetEvents CapNo
      return WakeupThread{thread=t,otherCap=fromIntegral oc}
   )),

 ("Request sequential GC", (0, return RequestSeqGC)),

 ("Request parallel GC", (0, return RequestParGC)),

 ("Starting GC", (0, return StartGC)),

 ("GC working", (0, return GCWork)),

 ("GC idle", (0, return GCIdle)),

 ("GC done", (0, return GCDone)),

 ("Finished GC", (0, return EndGC)),
 ("Blackhole", (4, liftM Blackhole getE)),

 -----------------------
 -- GHC 6.12 compat: GHC 6.12 reported the wrong sizes for some events,
 -- so we have to recognise those wrong sizes here for backwards 
 -- compatibility.

 ("Startup",
  (0, do -- BUG in GHC 6.12: the startup event was incorrectly 
         -- declared as size 0, so we accept it here.
      c <- getE :: GetEvents CapNo
      return Startup{ n_caps = fromIntegral c }
   )),

 ("Create thread",
  (sz_old_tid, do  -- (thread)
      t <- getE
      return CreateThread{thread=t}
   )),

 ("Run thread",
  (sz_old_tid, do  --  (thread)
      t <- getE
      return RunThread{thread=t}
   )),

 {-
 -- XXX this one doesn't work; see mkEventTypeParsers above
 (EVENT_STOP_THREAD,
  (sz_old_tid + 2, do  -- (thread, status)
      t <- getE
      s <- getE :: GetEvents Word16
      let stat = fromIntegral s
      return StopThread{thread=t, status = if stat > maxBound
                                              then NoStatus
                                              else mkStat stat}
   )),
 -}

 ("Thread runnable",
  (sz_old_tid, do  -- (thread)
      t <- getE
      return ThreadRunnable{thread=t}
   )),

 ("Migrate thread",
  (sz_old_tid + sz_cap, do  --  (thread, newCap)
      t  <- getE
      nc <- getE :: GetEvents CapNo
      return MigrateThread{thread=t,newCap=fromIntegral nc}
   )),

 ("Run spark",
  (sz_old_tid, do  -- (thread)
      t <- getE
      return RunSpark{thread=t}
   )),

 ("Steal spark",
  (sz_old_tid + sz_cap, do  -- (thread, victimCap)
      t  <- getE
      vc <- getE :: GetEvents CapNo
      return StealSpark{thread=t,victimCap=fromIntegral vc}
   )),

 ("Create spark thread",
  (sz_old_tid, do  -- (sparkThread)
      st <- getE :: GetEvents ThreadId
      return CreateSparkThread{sparkThread=st}
   )),

 ("Wakeup thread",
  (sz_old_tid + sz_cap, do  -- (thread, other_cap)
      t <- getE
      oc <- getE :: GetEvents CapNo
      return WakeupThread{thread=t,otherCap=fromIntegral oc}
   )),
 ("EVENT_CAPSET_CREATE", -- TODO
  (sz_capset + sz_capset_type, do -- (capset, capset_type)
      cs <- getE
      ct <- fmap mkCapsetType getE
      return CapsetCreate{capset=cs,capsetType=ct}
   )),
 ("EVENT_CAPSET_DELETE", -- TODO
  (sz_capset, do -- (capset)
      cs <- getE
      return CapsetDelete{capset=cs}
   )),
 ("EVENT_CAPSET_ASSIGN_CAP", -- TODO
  (sz_capset + sz_cap, do -- (capset, cap)
      cs <- getE
      cp <- getE :: GetEvents CapNo
      return CapsetAssignCap{capset=cs,cap=fromIntegral cp}
   )),
 ("EVENT_CAPSET_REMOVE_CAP", -- TODO
  (sz_capset + sz_cap, do -- (capset, cap)
      cs <- getE
      cp <- getE :: GetEvents CapNo
      return CapsetRemoveCap{capset=cs,cap=fromIntegral cp}
   )),
 ("EVENT_OSPROCESS_PID", -- TODO
  (sz_capset + 4, do -- (capset, pid)
      cs <- getE
      pd <- getE
      return OsProcessPid{capset=cs,pid=pd}
   )),
 ("EVENT_OSPROCESS_PPID", -- TODO
  (sz_capset + 4, do -- (capset, ppid)
      cs <- getE
      pd <- getE
      return OsProcessParentPid{capset=cs,ppid=pd}
  ))
 ]

variableEventTypeParsers :: Map String (GetEvents EventTypeSpecificInfo)
variableEventTypeParsers = Map.fromList [

 ("Log message", do -- (msg)
      num <- getE :: GetEvents Word16
      bytes <- lift $ P.take $ fromIntegral num
      return Message{ msg = map (chr . fromIntegral) $ S.unpack bytes }
   ),

 ("User message", do -- (msg)
      num <- getE :: GetEvents Word16
      bytes <- replicateM (fromIntegral num) getE 
      return UserMessage{ msg = bytesToString bytes }
   ),
 ("EVENT_PROGRAM_ARGS", do -- (capset, [arg]) -- TODO!
      num <- getE :: GetEvents Word16
      cs <- getE
      bytes <- replicateM (fromIntegral num - 4) getE
      return ProgramArgs{ capset = cs
                        , args = splitNull $ bytesToString bytes }
   ),
 ("EVENT_PROGRAM_ENV", do -- (capset, [arg]) -- TODO!
      num <- getE :: GetEvents Word16
      cs <- getE
      bytes <- replicateM (fromIntegral num - 4) getE
      return ProgramEnv{ capset = cs
                       , env = splitNull $ bytesToString bytes }
   ),
 ("EVENT_RTS_IDENTIFIER", do -- (capset, str) -- TODO!
      num <- getE :: GetEvents Word16
      cs <- getE
      bytes <- replicateM (fromIntegral num - 4) getE
      return RtsIdentifier{ capset = cs
                          , rtsident = bytesToString bytes }
   ),
 
 ("HPC module", do
     num <- getE :: GetEvents Word16
     let len = (num - 12)
     bytes <- replicateM (fromIntegral len) getE :: GetEvents [Word8]
     modCount <- getE :: GetEvents Word32
     modHash <- getE :: GetEvents Word32
     modBase <- getE :: GetEvents Word32
     return HpcModule { modName = map (chr . fromIntegral) bytes
                      , modCount = modCount
                      , modHash = modHash
                      , modBase = modBase
                      }
 ),
 
 ("Tick dump", do
     num <- getE :: GetEvents Word16
     let cnt = (num - 2) `div` 8
     cap <- getE :: GetEvents CapNo
     dump <- replicateM (fromIntegral cnt) $ do
       tick <- getE :: GetEvents Word32
       freq <- getE :: GetEvents Word32
       return (tick, freq)
     return TickDump { cap=fromIntegral cap, dump=dump }
 ),
 
 ("Instruction pointer sample", do
     num <- getE :: GetEvents Word16
     let cnt = (num - 2) `div` 4
     cap <- getE :: GetEvents CapNo
     ips <- replicateM (fromIntegral cnt) getE :: GetEvents [Word32]
     return InstrPtrSample { cap = fromIntegral cap, ips = ips }
 )
 
 ]
 where
    bytesToString :: [Word8] -> String
    bytesToString = map (chr . fromIntegral)

    splitNull [] = []
    splitNull xs = case span (/= '\0') xs of
                    (x, xs') -> x : splitNull (drop 1 xs')


noEventTypeParser :: Int -> Maybe EventTypeSize
                  -> GetEvents EventTypeSpecificInfo
noEventTypeParser num mb_size = do
  bytes <- case mb_size of
             Just n  -> return n
             Nothing -> getE :: GetEvents Word16
  _ <- lift $ P.take (fromIntegral bytes)
  return UnknownEvent{ ref = fromIntegral num }



getData :: GetEvents Data
getData = do
   db <- getE :: GetEvents Marker
   when (db /= EVENT_DATA_BEGIN) $ fail "Data begin marker not found"
   return . Data =<< getEvents 0 []

getEvents :: Timestamp -> [Event] -> GetEvents [Event]
getEvents t evs =
  join $ msum
    [ -- Check for end of file or end of data marker
      do lift endOfInput
         return $ return $ reverse evs
    , do e <- (getE :: GetEvents EventTypeNum)
         guard $ e == EVENT_DATA_END
         return $ return $ reverse evs
      -- Try to parse event
    , do e <- getEvent
         return $ getEvents (time e) (e:evs)
      -- If failed, try to recover by skipping the number of bytes
      -- given in the header.
    , do etRef <- getE :: GetEvents EventTypeNum
         EventParsers parsers <- ask
         guard $ inRange (bounds parsers) (fromIntegral etRef)
         let Just evTy = fst $ parsers ! fromIntegral etRef 
         case size evTy of
           Just n  -> lift (P.take $ fromIntegral n) >> return ()
           Nothing -> do n <- getE :: GetEvents Word16
                         lift $ P.take (fromIntegral n) >> return ()
         let e = Event t $ ErrorEvent $ "Failed to parse event " ++ desc evTy ++ "!"
         return $ getEvents t (e:evs)
      -- Finally, fail completely
    , do let e = Event t $ ErrorEvent "Failed to parse event - unknown event or data missing."
         return $ return $ reverse (e:evs)
    ]

getEventLog :: Parser EventLog
getEventLog = do
    header <- getHeader
    let imap = M.fromList [ (fromIntegral (num t),t) | t <- eventTypes header]
        parsers = mkEventTypeParsers imap
    dat <- runReaderT getData (EventParsers parsers)
    return (EventLog header dat)

readEventLogFromFile :: FilePath -> IO (Either String EventLog)
readEventLogFromFile f = do
    h <- openFile f ReadMode
    empty <- hIsEOF h
    if empty
      then return (Left "File is empty!")
      else continueEventLogFromHandle h $ parse getEventLog S.empty

continueEventLogFromHandle :: Handle -> Result EventLog -> IO (Either String EventLog)
continueEventLogFromHandle h res = do
  -- Read a chunk
  eof <- hIsEOF h
  bs <- if eof then return S.empty
               else S.hGetSome h 1024
  -- Feed to Attoparsec
  case feed res bs of
    Fail rest ctx err -> do
      pos <- hTell h
      let restLen = fromIntegral $ S.length rest
      return $ Left $ "Error at " ++ show (pos - restLen) ++ ": " ++ err ++ show ctx
    r'@Partial{}
      | eof      -> return $ Left $ "Internal error: Parser did not finish!" -- should not happen
      | not eof  -> continueEventLogFromHandle h r'
    Done _ res   -> return $ Right res

-- -----------------------------------------------------------------------------
-- Utilities

-- | An event annotated with the Capability that generated it, if any
data CapEvent
  = CapEvent { ce_cap   :: Maybe Int,
               ce_event :: Event
               -- we could UNPACK ce_event, but the Event constructor
               -- might be shared, in which case we could end up
               -- increasing the space usage.
             }

sortEvents :: [Event] -> [CapEvent]
sortEvents = sortGroups . groupEvents

-- | Sort the raw event stream by time, annotating each event with the
-- capability that generated it.
sortGroups :: [(Maybe Int, [Event])] -> [CapEvent]
sortGroups groups = mergesort' (compare `on` (time . ce_event)) $
                      [ [ CapEvent cap e | e <- es ]
                      | (cap, es) <- groups ]
     -- sorting is made much faster by the way that the event stream is
     -- divided into blocks of events.
     --  - All events in a block belong to a particular capability
     --  - The events in a block are ordered by time
     --  - blocks for the same capability appear in time order in the event
     --    stream and do not overlap.
     --
     -- So to sort the events we make one list of events for each
     -- capability (basically just concat . filter), and then
     -- merge the resulting lists.

groupEvents :: [Event] -> [(Maybe Int, [Event])]
groupEvents es = (Nothing, n_events) :
                 [ (Just (cap (head blocks)), concatMap block_events blocks)
                 | blocks <- groups ]
  where
   (blocks, anon_events) = partitionEithers (map separate es)
      where separate e | b@EventBlock{} <- spec e = Left  b
                       | otherwise                = Right e

   (cap_blocks, gbl_blocks) = partition (is_cap . cap) blocks
      where is_cap c = fromIntegral c /= ((-1) :: Word16)

   groups = groupBy ((==) `on` cap) $ sortBy (compare `on` cap) cap_blocks

     -- There are two sources of events without a capability: events
     -- in the raw stream not inside an EventBlock, and EventBlocks
     -- with cap == -1.  We have to merge those two streams.
     -- In light of merged logs, global blocks may have overlapping
     -- time spans, thus the blocks are mergesorted
   n_events = mergesort' (compare `on` time) (anon_events : map block_events gbl_blocks)

mergesort' :: (a -> a -> Ordering) -> [[a]] -> [a]
mergesort' _   [] = []
mergesort' _   [xs] = xs
mergesort' cmp xss = mergesort' cmp (merge_pairs cmp xss)

merge_pairs :: (a -> a -> Ordering) -> [[a]] -> [[a]]
merge_pairs _   [] = []
merge_pairs _   [xs] = [xs]
merge_pairs cmp (xs:ys:xss) = merge cmp xs ys : merge_pairs cmp xss

merge :: (a -> a -> Ordering) -> [a] -> [a] -> [a]
merge _   [] ys = ys
merge _   xs [] = xs
merge cmp (x:xs) (y:ys)
 = case x `cmp` y of
        GT -> y : merge cmp (x:xs)   ys
        _  -> x : merge cmp    xs (y:ys)


buildEventTypeMap :: [EventType] -> IntMap EventType
buildEventTypeMap etypes = M.fromList [ (fromIntegral (num t),t) | t <- etypes ]

-----------------------------------------------------------------------------
-- Some pretty-printing support

showEventTypeSpecificInfo :: EventTypeSpecificInfo -> String
showEventTypeSpecificInfo spec =
      case spec of
        Startup n_caps ->
          printf "startup: %d capabilities" n_caps
        EventBlock end_time cap _block_events ->
          printf "event block: cap %d, end time: %d\n" cap end_time
        CreateThread thread ->
          printf "creating thread %d" thread
        RunThread thread ->
          printf "running thread %d" thread
        StopThread thread status ->
          printf "stopping thread %d (%s)" thread (showThreadStopStatus status)
        ThreadRunnable thread ->
          printf "thread %d is runnable" thread
        MigrateThread thread newCap  ->
          printf "migrating thread %d to cap %d" thread newCap
        RunSpark thread ->
          printf "running a local spark (thread %d)" thread
        StealSpark thread victimCap ->
          printf "thread %d stealing a spark from cap %d" thread victimCap
        CreateSparkThread sparkThread ->
          printf "creating spark thread %d" sparkThread
        Shutdown ->
          printf "shutting down"
        WakeupThread thread otherCap ->
          printf "waking up thread %d on cap %d" thread otherCap
        RequestSeqGC ->
          printf "requesting sequential GC"
        RequestParGC ->
          printf "requesting parallel GC"
        StartGC ->
          printf "starting GC"
        EndGC ->
          printf "finished GC"
        GCWork ->
          printf "GC working"
        GCIdle ->
          printf "GC idle"
        GCDone ->
          printf "GC done"
        Message msg ->
          msg
        UserMessage msg ->
          msg
        CapsetCreate cs ct ->
          printf "created capset %d of type %s" cs (show ct)
        CapsetDelete cs ->
          printf "deleted capset %d" cs
        CapsetAssignCap cs cp ->
          printf "assigned cap %d to capset %d" cp cs
        CapsetRemoveCap cs cp ->
          printf "removed cap %d from capset %d" cp cs
        OsProcessPid cs pid ->
          printf "capset %d: pid %d" cs pid
        OsProcessParentPid cs ppid ->
          printf "capset %d: parent pid %d" cs ppid
        RtsIdentifier cs i ->
          printf "capset %d: RTS version %s" cs i
        ProgramArgs cs args ->
          printf "capset %d: args: %s" cs (show args)
        ProgramEnv cs env ->
          printf "capset %d, env: %s" cs (show env)
        HpcModule name boxes _ base ->
          printf "HPC module %s with %d tick boxes, iticks starting at %d" name boxes base
        TickDump cap dump ->
          printf "Tick dump cap %d: %s" cap (show $ sortBy (compare `on` fst) dump)
        InstrPtrSample cap ips ->
          printf "Instruction ptr sample cap %d: %s" cap (intercalate "," (map (flip showHex "") ips))
        Blackhole ip ->
          printf "Blackhole %s" (showHex ip "")
        UnknownEvent _ ->
          "Unknown event type"
        ErrorEvent msg ->
          "Error in stream: " ++ msg

showThreadStopStatus :: ThreadStopStatus -> String
showThreadStopStatus NoStatus       = "no status"
showThreadStopStatus HeapOverflow   = "heap overflow"
showThreadStopStatus StackOverflow  = "stack overflow"
showThreadStopStatus ThreadYielding = "thread yielding"
showThreadStopStatus ThreadBlocked  = "thread blocked"
showThreadStopStatus ThreadFinished = "thread finished"
showThreadStopStatus ForeignCall    = "making a foreign call"
showThreadStopStatus BlockedOnMVar  = "blocked on an MVar"
showThreadStopStatus BlockedOnBlackHole = "blocked on a black hole"
showThreadStopStatus BlockedOnRead = "blocked on I/O read"
showThreadStopStatus BlockedOnWrite = "blocked on I/O write"
showThreadStopStatus BlockedOnDelay = "blocked on threadDelay"
showThreadStopStatus BlockedOnSTM = "blocked in STM retry"
showThreadStopStatus BlockedOnDoProc = "blocked on asyncDoProc"
showThreadStopStatus BlockedOnCCall = "blocked in a foreign call"
showThreadStopStatus BlockedOnCCall_NoUnblockExc = "blocked in a foreign call"
showThreadStopStatus BlockedOnMsgThrowTo = "blocked in throwTo"
showThreadStopStatus ThreadMigrating = "thread migrating"
showThreadStopStatus BlockedOnMsgGlobalise = "waiting for data to be globalised"
showThreadStopStatus (BlockedOnBlackHoleOwnedBy target) =
          "blocked on black hole owned by thread " ++ show target

ppEventLog :: EventLog -> String
ppEventLog (EventLog (Header ets) (Data es)) = unlines $ concat (
    [ ["Event Types:"]
    , map ppEventType ets
    , [""] -- newline
    , ["Events:"]
    , map (ppEvent imap) sorted
    , [""] ]) -- extra trailing newline
 where
    imap = buildEventTypeMap ets
    sorted = sortEvents es

ppEventType :: EventType -> String
ppEventType (EventType num dsc msz) = printf "%4d: %s (size %s)" num dsc
   (case msz of Nothing -> "variable"; Just x -> show x)

ppEvent :: IntMap EventType -> CapEvent -> String
ppEvent imap (CapEvent cap (Event time spec)) =
  printf "%9d: " time ++
  (case cap of
    Nothing -> ""
    Just c  -> printf "cap %d: " c) ++
  case spec of
    UnknownEvent{ ref=ref } ->
      printf (desc (fromJust (M.lookup (fromIntegral ref) imap)))

    Message msg -> msg
    UserMessage msg -> msg

    other -> showEventTypeSpecificInfo spec

type PutEvents a = PutM a

putE :: Binary a => a -> PutEvents ()
putE = put

runPutEBS :: PutEvents () -> L.ByteString
runPutEBS = runPut

writeEventLogToFile f el = L.writeFile f $ runPutEBS $ putEventLog el

putType :: EventTypeNum -> PutEvents ()
putType = putE

putCap :: Int -> PutEvents ()
putCap c = putE (fromIntegral c :: CapNo)

putMarker :: Word32 -> PutEvents ()
putMarker = putE

putEventLog :: EventLog -> PutEvents ()
putEventLog (EventLog hdr es) = do
    putHeader hdr
    putData es

putHeader :: Header -> PutEvents ()
putHeader (Header ets) = do
    putMarker EVENT_HEADER_BEGIN
    putMarker EVENT_HET_BEGIN
    mapM_ putEventType ets
    putMarker EVENT_HET_END
    putMarker EVENT_HEADER_END
 where
    putEventType (EventType n d msz) = do
        putMarker EVENT_ET_BEGIN
        putType n
        putE $ fromMaybe 0xffff msz
        putE (fromIntegral $ length d :: EventTypeDescLen)
        mapM_ put d
        -- the event type header allows for extra data, which we don't use:
        putE (0 :: Word32)
        putMarker EVENT_ET_END

putData :: Data -> PutEvents ()
putData (Data es) = do
    putMarker EVENT_DATA_BEGIN -- Word32
    mapM_ putEvent es
    putType EVENT_DATA_END -- Word16

eventTypeNum :: EventTypeSpecificInfo -> EventTypeNum
eventTypeNum e = case e of
    CreateThread {} -> EVENT_CREATE_THREAD
    RunThread {} -> EVENT_RUN_THREAD
    StopThread {} -> EVENT_STOP_THREAD
    ThreadRunnable {} -> EVENT_THREAD_RUNNABLE
    MigrateThread {} -> EVENT_MIGRATE_THREAD
    RunSpark {} -> EVENT_RUN_SPARK
    StealSpark {} -> EVENT_STEAL_SPARK
    Shutdown {} -> EVENT_SHUTDOWN
    WakeupThread {} -> EVENT_THREAD_WAKEUP
    StartGC {} -> EVENT_GC_START
    EndGC {} -> EVENT_GC_END
    RequestSeqGC {} -> EVENT_REQUEST_SEQ_GC
    RequestParGC {} -> EVENT_REQUEST_PAR_GC
    CreateSparkThread {} -> EVENT_CREATE_SPARK_THREAD
    Message {} -> EVENT_LOG_MSG
    Startup {} -> EVENT_STARTUP
    EventBlock {} -> EVENT_BLOCK_MARKER
    UserMessage {} -> EVENT_USER_MSG
    GCIdle {} -> EVENT_GC_IDLE
    GCWork {} -> EVENT_GC_WORK
    GCDone {} -> EVENT_GC_DONE
    CapsetCreate {} -> EVENT_CAPSET_CREATE
    CapsetDelete {} -> EVENT_CAPSET_DELETE
    CapsetAssignCap {} -> EVENT_CAPSET_ASSIGN_CAP
    CapsetRemoveCap {} -> EVENT_CAPSET_REMOVE_CAP
    RtsIdentifier {} -> EVENT_RTS_IDENTIFIER
    ProgramArgs {} -> EVENT_PROGRAM_ARGS
    ProgramEnv {} -> EVENT_PROGRAM_ENV
    OsProcessPid {} -> EVENT_OSPROCESS_PID
    OsProcessParentPid{} -> EVENT_OSPROCESS_PPID

putEvent :: Event -> PutEvents ()
putEvent (Event t spec) = do
    putType (eventTypeNum spec)
    put t
    putEventSpec spec

putEventSpec (Startup caps) = do
    putCap (fromIntegral caps)

putEventSpec (EventBlock end cap es) = do
    let block = runPutEBS (mapM_ putEvent es)
    put (fromIntegral (L.length block) + 24 :: Word32)
    putE end
    putE (fromIntegral cap :: CapNo)
    putLazyByteString block

putEventSpec (CreateThread t) = do
    putE t

putEventSpec (RunThread t) = do
    putE t

-- here we assume that ThreadStopStatus fromEnum matches the definitions in
-- EventLogFormat.h
putEventSpec (StopThread t s) = do
    putE t
    putE $ case s of
            NoStatus -> 0 :: Word16
            HeapOverflow -> 1
            StackOverflow -> 2
            ThreadYielding -> 3
            ThreadBlocked -> 4
            ThreadFinished -> 5
            ForeignCall -> 6
            BlockedOnMVar -> 7
            BlockedOnBlackHole -> 8
            BlockedOnBlackHoleOwnedBy _ -> 8
            BlockedOnRead -> 9
            BlockedOnWrite -> 10
            BlockedOnDelay -> 11
            BlockedOnSTM -> 12
            BlockedOnDoProc -> 13
            BlockedOnCCall -> 14
            BlockedOnCCall_NoUnblockExc -> 15
            BlockedOnMsgThrowTo -> 16
            ThreadMigrating -> 17
            BlockedOnMsgGlobalise -> 18
    putE $ case s of
            BlockedOnBlackHoleOwnedBy i -> i
            _                           -> 0

putEventSpec (ThreadRunnable t) = do
    putE t

putEventSpec (MigrateThread t c) = do
    putE t
    putCap c

putEventSpec (RunSpark t) = do
    putE t

putEventSpec (StealSpark t c) = do
    putE t
    putCap c

putEventSpec (CreateSparkThread t) = do
    putE t

putEventSpec (WakeupThread t c) = do
    putE t
    putCap c

putEventSpec Shutdown = do
    return ()

putEventSpec RequestSeqGC = do
    return ()

putEventSpec RequestParGC = do
    return ()

putEventSpec StartGC = do
    return ()

putEventSpec GCWork = do
    return ()

putEventSpec GCIdle = do
    return ()

putEventSpec GCDone = do
    return ()

putEventSpec EndGC = do
    return ()

putEventSpec (CapsetCreate cs ct) = do
    putE cs
    putE $ case ct of
            CapsetCustom -> 1 :: Word16
            CapsetOsProcess -> 2
            CapsetClockDomain -> 3
            CapsetUnknown -> 0

putEventSpec (CapsetDelete cs) = do
    putE cs

putEventSpec (CapsetAssignCap cs cp) = do
    putE cs
    putCap cp

putEventSpec (CapsetRemoveCap cs cp) = do
    putE cs
    putCap cp

putEventSpec (RtsIdentifier cs rts) = do
    putE (fromIntegral (length rts) + 4 :: Word16)
    putE cs
    mapM_ putE rts

putEventSpec (ProgramArgs cs as) = do
    let as' = unsep as
    putE (fromIntegral (length as') + 4 :: Word16)
    putE cs
    mapM_ putE as'

putEventSpec (ProgramEnv cs es) = do
    let es' = unsep es
    putE (fromIntegral (length es') + 4 :: Word16)
    putE cs
    mapM_ putE es'

putEventSpec (OsProcessPid cs pid) = do
    putE cs
    putE pid

putEventSpec (OsProcessParentPid cs ppid) = do
    putE cs
    putE ppid

putEventSpec (Message s) = do
    putE (fromIntegral (length s) :: Word16)
    mapM_ putE s

putEventSpec (UserMessage s) = do
    putE (fromIntegral (length s) :: Word16)
    mapM_ putE s

-- [] == []
-- [x] == x\0
-- [x, y, z] == x\0y\0
unsep :: [String] -> String
unsep = concatMap (++"\0") -- not the most efficient, but should be ok
