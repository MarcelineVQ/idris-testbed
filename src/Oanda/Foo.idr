module Oanda.Foo

import public Oanda.Types
import System.File

import Data.String
import Data.List

public export
data ReqError = FileErr FileError | ParseErr String | HttpError StatusCode String | ResponseParseError

public export
data RequestKind = Candle

public export
data Request : RequestKind -> Type where
  CandleReq : AcceptDateTimeFormat -> InstrumentName -> CandlestickGranularity ->
            (from : DateTime) -> (countOrTo : Either Integer DateTime) -> Request Candle


public export
data CurlReq : RequestKind -> Type where
  MkCurlReq : (headers : List String) -> (body : String) -> CurlReq rk

public export
record Response (rk : RequestKind) where
  constructor MkResponse
  statuscode : StatusCode
  header : List String
  body : String

export
contenth : String
contenth = "\"Content-Type: application/json\""

export
selfAuth : AuthToken
selfAuth = unsafePerformIO $ do
  key <- readFile "oanda-api-key.txt"
  pure $ either (const (MkAuthToken "")) MkAuthToken key

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
    in MkCurlReq (basicHeader token dtf) "\{apiUrl}instruments/\{show pair}/candles?price=MBA\{arg1}\{arg2}\{arg3}"


export
testRequest : CurlReq Candle
testRequest = mkRequest (CandleReq DTRFC3339 USD_CAD M1 "2010-08-31T00:01:00.000000000Z" (Left 10)) selfAuth

export
runRequest : CurlReq rk -> IO (Either ReqError (Response rk))
runRequest _ = pure (Left ResponseParseError)

main : IO ()
-- main = ignore $ runRequest testRequest
main = ignore $ runRequest {rk = Candle} $ testRequest
