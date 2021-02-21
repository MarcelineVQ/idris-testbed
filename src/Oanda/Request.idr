module Oanda.Request

import public Oanda.Types
import System.File
import JSON
import Data.String
import Data.List

import System -- usleep

import Generics.Derive
%language ElabReflection

-- more to be added later maybe
public export
data RequestKind = Candle

public export
data Request : RequestKind -> Type where
  CandleReq : AcceptDateTimeFormat -> InstrumentName -> CandlestickGranularity ->
            (from : DateTime) -> (countOrTo : Either Integer DateTime) -> Request Candle

-- data Header = MkHeader (List String)
-- data Body = MkBody String

public export
data CurlReq : RequestKind -> Type where
  MkCurlReq : (headers : List String) -> (body : String) -> CurlReq rk

export
contenth : String
contenth = "\"Content-Type: application/json\""

export
selfAuth : AuthToken
selfAuth = MkAuthToken "21603a35787c64d4c1277856a8551a43-9dea44e08f2473bcef690b265264530c"

export
timeh : AcceptDateTimeFormat -> String
timeh dtf = "\"Accept-Datetime-Format: " ++ show dtf ++ "\""

export
authStr : AuthToken -> String
authStr tok = "\"Authorization: Bearer " ++ unAuthToken tok ++ "\""

export
apiUrl : String
apiUrl = "https://api-fxtrade.oanda.com/v3/"

export
basicHeader : AuthToken -> AcceptDateTimeFormat -> List String
basicHeader tok dtf = [contenth, timeh dtf, authStr tok]

export
mkRequest : Request k -> AuthToken -> CurlReq k
mkRequest (CandleReq dtf pair gran from countOrTo) token =
    let arg1 = "&from=" ++ show from
        arg2 = either (\c => "&count=" ++ show c) (\t => "&to=" ++ show t) countOrTo
        arg3 = "&granularity=" ++ show gran
    in MkCurlReq (basicHeader token dtf) (apiUrl ++ "instruments/" ++ show pair ++ "/candles?price=MBA" ++ arg1 ++ arg2 ++ arg3)

-- TODO: repeal this token
export
testRequest : CurlReq Candle
testRequest = mkRequest (CandleReq DTRFC3339 USD_CAD M1 "2010-08-31T00:01:00.000000000Z" (Left 10)) selfAuth

export
usdCadRequest : CandlestickGranularity -> DateTime -> Either Integer DateTime -> CurlReq Candle
usdCadRequest gran from to = mkRequest (CandleReq DTRFC3339 USD_CAD gran from to) selfAuth

export
fGetLines : HasIO io => (h : File) -> io (Either FileError (List String))
fGetLines f = do
  Right l <- fGetLine f
    | Left err => pure (Left err)
  case l of
    "" => pure (Right [])
    str => pure [| pure str :: !(fGetLines f) |]

public export
data ReqError = FileErr FileError | ParseErr String | HttpError StatusCode String | ResponseParseError
%runElab derive "ReqError" [Generic,Meta,Show,Eq]

public export
record Response (rk : RequestKind) where
  constructor MkResponse
  statuscode : StatusCode
  header : List String
  body : String
%runElab derive "Response" [Generic,Meta,Show,Eq]

export
-- parseRawResponse : List String -> Maybe (StatusCode, List String, String)
parseRawResponse : List String -> Maybe (Response rk)
parseRawResponse ss =
    let (headers,body) = mapSnd (drop 1) $ break (=="\r\n") ss
    in case headers of
         (status :: headers') =>
           MkResponse <$> extract status <*> pure headers' <*> head' body
         _ => Nothing
  where
    extract : String -> Maybe StatusCode
    extract str = case words str of
                    (httpver :: code :: _) => parseStatusCode code
                    _ => Nothing

export
okStatusCode : StatusCode -> Bool
okStatusCode Ok200 = True
okStatusCode _ = False

export
runRequest : CurlReq rk -> IO (Either ReqError (Response rk))
runRequest re@(MkCurlReq hs bs) = do
  let hs' = map ("-H " ++) hs
  let str = unwords $ ["curl -i -s"] ++ hs' ++ ["\"" ++ bs ++ "\""]
  printLn str
  Right r <- popen str Read
    | Left err => printLn err *> pure (Left (FileErr err))
  Right res <- fGetLines r
    | Left err => printLn err *> pure (Left (FileErr err))
  -- printLn res
  case parseRawResponse res of
    Nothing => pure $ Left ResponseParseError
    Just r => if okStatusCode (statuscode r)
      then pure $ Right r
      else case statuscode r of
             Err504 => putStrLn (body r) *> usleep 250000 *> runRequest re
             err => pure $ Left (HttpError err (body r))
        
        -- pure $ Left (HttpError (statuscode r) (body r))

export
respToCandles : Response Candle -> Maybe CandlestickResponse
respToCandles r = either (\_ => Nothing) Just $ decode (body r)



-- I want to load candles from some start period, send those into sqlite, get
-- more, send them in, etc. I also want the functionality to find the newest
-- candle in sqlite, and grab all candles after that point.
-- I don't need to be super careful about overlaps because I can just prune
-- duplicate entries in db by time