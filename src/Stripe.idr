module Stripe

import System.File
import System

import Data.String
import Data.List

import Generics.Derive
%language ElabReflection

data RequestKind = Get | Post
%runElab derive "RequestKind" [Generic,Meta,Show,Eq]

-- 504, timeout waiting for response
public export
data StatusCode =  Ok200 | Err400 | Err401 | Err403 | Err404 | Err405 | Err504
%runElab derive "StatusCode" [Generic,Meta,Show,Eq]
-- %runElab derive "StatusCode" [Generic,Meta,Show,Eq,Ord]

export
parseStatusCode : String -> Maybe StatusCode
parseStatusCode "200" = Just Ok200
parseStatusCode "400" = Just Err400
parseStatusCode "401" = Just Err401
parseStatusCode "403" = Just Err403
parseStatusCode "404" = Just Err404
parseStatusCode "405" = Just Err405
parseStatusCode "504" = Just Err504
parseStatusCode _     = Nothing

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

-- export
-- parseRawResponse : List String -> Maybe (StatusCode, List String, String)
parseRawResponse : List String -> Maybe (Response rk)
parseRawResponse ss =
    let (headers,body) = mapSnd (drop 1) $ break (=="\r\n") ss
    in case headers of
         (status :: headers') =>
           MkResponse <$> extract status <*> pure headers' <*> Just (concat body) -- head' body, y?
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

public export
data CurlReq : RequestKind -> Type where
  MkCurlReq : (headers : List String) -> (body : String) -> CurlReq rk
%runElab derive "CurlReq" [Generic,Meta,Show,Eq]

infixl 4 `u`
u : CurlReq k -> Either String (String,String) -> CurlReq k
u (MkCurlReq h bs) e = case e of
  Left usr => MkCurlReq h (bs ++ " -u \{usr}:")
  Right (usr,pass) => MkCurlReq h (bs ++ " -u \{usr}:\{pass}")

infixl 4 `d`
d : CurlReq k -> String -> CurlReq k
d (MkCurlReq h bs) str = MkCurlReq h (bs ++ " -d \{str}")

export
runRequest : CurlReq rk -> IO (Either ReqError (Response rk))
runRequest re@(MkCurlReq hs bs) = do
  let hs' = map ("-H " ++) hs
  let str = unwords $ ["curl -i -s -G"] ++ hs' ++ [bs]
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

main : IO ()
main = pure ()


-- :exec runRequest {rk=Get} (u (MkCurlReq [] "https://api.stripe.com/v1/events") (Left "sk_test_4eC39HqLyjWDarjtT1zdp7dc") `d` "limit=1" `d` "type=invoice.payment_failed") >>= \(Right b) => putStrLn (body b)