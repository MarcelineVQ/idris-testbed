module Oanda.ToDB

import SQLite3
import Control.Monad.Managed
import Control.Monad.Either

import Oanda.Types
import Oanda.Request

import Data.IORef

import System -- usleep

import TimeIt

-- import Data.String
import Data.List

import Control.Monad.Trans

import Generics.Derive
%language ElabReflection

-- export
-- managedDB : String -> Managed (Either SqlResult DB)
-- managedDB file = managed (withDB file)
-- 
-- export
-- managedStmt : DB -> String -> Managed (Either SqlResult Stmt)
-- managedStmt db sql = managed (withStmt db sql)

-- CandleType : Type
-- CandleType = (String, String, Bool  , Int   , String,
--               Double, Double, Double, Double,
--               Double, Double, Double, Double,
--               Double, Double, Double, Double)

export
Show StepResult where
  show SRBusy = "SRBusy"
  show SRDone = "SRDone"
  show SRRow = "SRRow"
  show SRError = "SRError"
  show SRMisuse = "SRMisuse"


-- I don't really neeeed this type, can just convert when pulling to/from db
-- a bunch of tuples was annihilating the elaborator
public export
data SQLCandleType : Type where
  MkSQLCandle : String -> String -> Bool   -> Integer -> String ->
                String -> String -> String -> String  -> -- bid
                String -> String -> String -> String  -> -- mid
                String -> String -> String -> String  -> -- ask
                SQLCandleType
%runElab derive "SQLCandleType" [Generic,Meta,Eq,Show]

export
sqlCandleMids : SQLCandleType -> List String
sqlCandleMids (MkSQLCandle _ _ _ _ _ _ _ _ _ o h l c _ _ _ _) = [o,h,l,c]

export
sqlCandleTypeWasComplete : SQLCandleType -> Bool
sqlCandleTypeWasComplete (MkSQLCandle _ _ b _ _ _ _ _ _ _ _ _ _ _ _ _ _) = b

export
timeFrom : SQLCandleType -> String
timeFrom (MkSQLCandle _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ _) = t

export
candleRespToSQLType : CandlestickResponse -> Maybe (List SQLCandleType)
candleRespToSQLType r = for (candles r) $ \ca => do
    b <- bid ca
    m <- mid ca
    a <- ask ca
    pure $ MkSQLCandle (show $ instrument r) (show $ granularity r)
                (complete ca)  (volume ca)    (show $ time ca)
                (o b)   (h b)   (l b)   (c b)
                (o m)   (h m)   (l m)   (c m)
                (o a)   (h a)   (l a)   (c a)



export
testCandleType1 : SQLCandleType
testCandleType1 = MkSQLCandle "USD_CAD" "M30" True 492 "2010-08-31T00:00:00.000000000Z" "1.05991" "1.06080" "1.05984" "1.06072" "1.06006" "1.06094" "1.05998" "1.06086" "1.06020" "1.06109" "1.06013" "1.06101"
export
testCandleType2 : SQLCandleType
testCandleType2 = MkSQLCandle "USD_CAD" "M30" True 318 "2010-08-31T00:30:00.000000000Z" "1.06069" "1.06090" "1.06043" "1.06073" "1.06084" "1.06104" "1.06058" "1.06088" "1.06098" "1.06119" "1.06072" "1.06102"
export
testCandleType3 : SQLCandleType
testCandleType3 = MkSQLCandle "USD_CAD" "M30" True 439 "2010-08-31T01:00:00.000000000Z" "1.06070" "1.06072" "1.05941" "1.05955" "1.06084" "1.06086" "1.05956" "1.05970" "1.06099" "1.06101" "1.05970" "1.05984"

export
boolToSQLBool : Bool -> Int
boolToSQLBool b = if b then 1 else 0

export
sqlBoolToBool : Int -> Bool
sqlBoolToBool b = if b == 1 then True else False

-- This should really be generated, but idc
-- hideous memory blowup, probably due to Alt on pair
export
candleTypeToString : SQLCandleType -> String
candleTypeToString (MkSQLCandle instrument granularity completed volume opentime
  bidOpen bidHigh bidLow bidClose
  midOpen midHigh midLow midClose
  askOpen askHigh askLow askClose)
    = "INSERT INTO candle VALUES(" ++ (concat $ Data.List.intersperse "," $ [show instrument, show granularity, show (boolToSQLBool completed),show volume, show opentime
    ,show bidOpen, show bidHigh, show bidLow, show bidClose
    ,show midOpen, show midHigh, show midLow, show midClose
    ,show askOpen, show askHigh, show askLow, show askClose]) ++ ");"



export
mkUSDCADTableStr : String
mkUSDCADTableStr = """
    CREATE TABLE candle(instrument String
    , Granularity String, Complete Bool, Volume Int, OpenTime String
    , BidOpen String, BidHigh String, BidLow String, BidClose String
    , MidOpen String, MidHigh String, MidLow String, MidClose String
    , AskOpen String, AskHigh String, AskLow String, AskClose String);
    """

-- consolidate stmt and step, don't ask questions
-- sqlCmd : DB -> String -> Managed ()
-- sqlCmd db sql = do
--   Right begin <- managedStmt db sql
--     | Left err => liftIO (putStrLn "sqlCmd: managed failed to make stmt")
--   Right res <- liftIO $ sqliteStep begin
--     | Left err => liftIO (putStrLn "sqlCmd: sqliteStep failed")
--   pure ()

-- consolidate stmt and step, don't ask questions
sqlCmd : DB -> String -> Managed ()
sqlCmd db sql = do
  Right begin <- managedStmt db sql
    | Left err => liftIO (putStrLn "sqlCmd: managed failed to make stmt")
  Right res <- liftIO $ sqliteStep begin
    | Left err => liftIO (putStrLn "sqlCmd: sqliteStep failed")
  pure ()

withTransaction : DB -> (() -> IO a) -> IO a
withTransaction db act = do
  runManaged $ sqlCmd db "BEGIN TRANSACTION;"
  r <- act ()
  pure r <* (runManaged $ sqlCmd db "COMMIT TRANSACTION;")

export
||| Ends automatically when scope ends due to managed
||| You might not actually want this, use withTransaction when you don't
beginTransaction : DB -> Managed ()
beginTransaction db = managed $ withTransaction db

-- Bool is: was the last entry complete
insertCandlestickResponse : DB -> CandlestickResponse -> Managed (Either SqlResult Bool)
insertCandlestickResponse db resp = do
  Just r <- pure $ candleRespToSQLType resp
    | _ => pure (Right False)
  -- is last candle complete
  ref <- liftIO $ newIORef False
  -- beginTransaction db
  sqlCmd db "BEGIN TRANSACTION;"
  _ <- for r $ \candle => do
    if sqlCandleTypeWasComplete candle
      then do
        Right stmt <- managedStmt db (candleTypeToString candle)
          | Left err => liftIO (putStrLn "managed failed to make stmt") *> pure ()
        Right res <- liftIO $ sqliteStep stmt
          | Left l => liftIO (putStrLn "sqliteStep failed") *> pure ()
        pure ()
      else writeIORef ref (sqlCandleTypeWasComplete candle)
  sqlCmd db "COMMIT TRANSACTION;"
  -- was the last candle complete
  pure (Right !(readIORef ref))

export
getSome : CandlestickGranularity -> DateTime -> Either Integer DateTime -> IO ()
getSome gran from to = runManaged $ do
    Right db <- managedDB "oanda-data.db"
      | Left err => liftIO $ putStrLn "db open error"
    Right r <- liftIO $ runRequest (usdCadRequest gran from to)
      | Left rerr => printLn rerr
    Just r' <- pure (respToCandles r)
      | _ => liftIO $ putStrLn "failed respToCandles"
    Right _ <- insertCandlestickResponse db r'
      | Left _ => liftIO $ putStrLn "failed inserts"
    pure ()


-- sqlExec : DB -> (sql : String) -> (a -> Int -> List String -> List String -> PrimIO Int) -> a -> String -> PrimIO Int

-- try fetch via callback
-- sqlCallback : DB -> (sql : String) ->

{-
int sqlite3_exec(
  sqlite3*,                                  /* An open database */
  const char *sql,                           /* SQL to be evaluated */
  int (*callback)(void*,int,char**,char**),  /* Callback function */
  void *,                                    /* 1st argument to callback */
  char **errmsg                              /* Error msg written here */
);
-}

export
fetchSQLCandleType : Stmt -> IO SQLCandleType
fetchSQLCandleType stmt = do
    inst <- getValue stmt 0
    gran <- getValue stmt 1
    comp <- getValue stmt 2
    volu <- getValue stmt 3 {t=Int}
    time <- getValue stmt 4
    bo   <- getValue stmt 5
    bh   <- getValue stmt 6
    bl   <- getValue stmt 7
    bc   <- getValue stmt 8
    mo   <- getValue stmt 9
    mh   <- getValue stmt 10
    ml   <- getValue stmt 11
    mc   <- getValue stmt 12
    ao   <- getValue stmt 13
    ah   <- getValue stmt 14
    al   <- getValue stmt 15
    ac   <- getValue stmt 16
    pure $ MkSQLCandle inst gran (sqlBoolToBool comp) (cast volu) time
                       bo bh bl bc mo mh ml mc ao ah al ac


-- seems to order correctly
-- I MUST speed up fetchSQLCandleType
export
fetchRows : Stmt -> IO (Either SqlResult (List SQLCandleType))
fetchRows stmt = runEitherT {m=IO} {e=SqlResult} $ do
        SRRow <- MkEitherT $ liftIO $ sqliteStep stmt
          | SRDone => pure []
          | SRBusy => left SQLITE_BUSY
          | SRError => left SQLITE_ERROR
          | SRMisuse => left SQLITE_MISUSE
        row <- liftIO $ fetchSQLCandleType stmt
        rest <- MkEitherT $ liftIO $ fetchRows stmt
        pure (row :: rest)

export
getCandles' : String -> Managed (List SQLCandleType)
getCandles' sql = do
    Right db <- managedDB "oanda-data.db"
      | Left err => putStrLn "db open error" *> pure []
    Right stmt <- managedStmt db sql
      | Left err => putStrLn "stmt make error" *> pure []
    -- sqlCmd db "begin;"
    Right r <- liftIO $ fetchRows stmt
      | Left err => putStrLn "row get error" *> pure []
    -- sqlCmd db "end;"
    pure r

export
getCandles : String -> Managed (List SQLCandleType)
getCandles mod = getCandles' "select * from candle \{mod};"

export
getCandles'' : String -> IO (List SQLCandleType)
getCandles'' mod = do
  r <- newIORef []
  runManaged $ do
    c <- getCandles' "select * from candle \{mod};"
    liftIO $ writeIORef r c
  readIORef r

-- grab latest candle of given gran
latestCandle : InstrumentName -> CandlestickGranularity -> Managed (Maybe SQLCandleType)
latestCandle inst gran = do
  let sql = "select * from candle where instrument = \"\{show inst}\" and granularity = \"\{show gran}\" order by opentime desc limit 1;"
  -- putStrLn sql
  [candle] <- getCandles' sql
    | _ => liftIO (putStrLn "no results") *> pure Nothing
  pure (Just candle)

-- Now I want to accept a time, and fetch everything from that point on, stopping
-- when a candle comes back as incomplete.
-- We can further automate this by having a version that grabs time from latestCandle

-- fetch 500 at a time to start
fetchAllFrom : InstrumentName -> DateTime -> CandlestickGranularity -> Managed (List SQLCandleType)
fetchAllFrom inst dt gran = do
  -- make request
  ?fdsfsd
  -- insertCandlestickResponse
  -- respToCandles resp 

-- rarf : IO ()
-- rarf = ?ssdffd $ runEitherT {m=Managed} {e=Char} {a=()} ?dsffsd

fetchAllFrom' : InstrumentName -> CandlestickGranularity -> DateTime -> Integer -> Managed ((Either SqlResult ()))
fetchAllFrom' inst gran from count = runEitherT {m = Managed} $ do
    db <- MkEitherT $ use $ managedDB "oanda-data.db"
    Right r <- liftIO $ runRequest $ mkRequest (CandleReq DTRFC3339 inst gran from (Left count)) selfAuth
      | Left rerr => printLn rerr
-- insert into db
-- query db for last entry, use that as new DateTime, repeat until unfinished candle
    Just r' <- pure (respToCandles r)
      | _ => liftIO $ putStrLn "failed respToCandles"
    b <- MkEitherT $ insertCandlestickResponse db r'
    if not b
      then pure ()
      else do
        Just from' <- use $ latestCandle inst gran
          | _ => pure ()
        liftIO $ usleep 100000
        MkEitherT $ fetchAllFrom' inst gran (MkDateTime (timeFrom from')) count
-- "2010-01-01T00:00:00.000000000Z"

export
doFetchAllFrom : InstrumentName -> CandlestickGranularity -> DateTime -> Integer -> IO ()
doFetchAllFrom inst gran from count = runManaged $ do
  _ <- fetchAllFrom' inst gran from count
  pure ()

main : IO ()
main = pure ()



-- example : MonadManaged m => EitherT SqlResult m String
-- example = do f <- MkEitherT $ use (managedDB "/dev/urandom" Read)
--              r <- MkEitherT $ liftIO $ fGetChars f 20
--              pure (length r) -- '\0' ends Strings, this probably won't be 20!
-- 
-- example_main : IO ()
-- example_main = runManaged $ do
--     Right x <- runEitherT example
--       | Left y => liftIO (printLn y)
--     putStrLn $ show x ++ " chars read from /dev/urandom"





