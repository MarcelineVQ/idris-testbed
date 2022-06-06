module Oanda.Types

import Util
import JSON

import public Oanda.Types.Instrument

import Generics.Derive
%language ElabReflection

public export
data AcceptDateTimeFormat = DTUnix | DTRFC3339

public export
Show AcceptDateTimeFormat where
  show DTUnix = "UNIX"
  show DTRFC3339 = "RFC3339"

-- public export
-- data Endpoint = Account | Instrument' | Order | Trade | Position | Transaction | Pricing

namespace PC
  export
  data PricingComponent = M | B | A
  
  %runElab derive "PricingComponent"
    [Generic,Meta,Eq,Show,EnumToJSON,EnumFromJSON]

public export
data WeeklyAlignment = Monday
                     | Tuesday
                     | Wednesday
                     | Thursday
                     | Friday
                     | Saturday
                     | Sunday

%runElab derive "WeeklyAlignment"
  [Generic,Meta,Eq,Ord,Show,EnumToJSON,EnumFromJSON]


public export
data AuthToken = MkAuthToken String

%runElab derive "AuthToken"
  [Generic,Meta,Eq,Show,NewtypeToJSON,NewtypeFromJSON]

public export
unAuthToken : AuthToken -> String
unAuthToken (MkAuthToken s) = s

-- define with sop

public export
data DateTime : Type where
  MkDateTime : String -> DateTime

export
Show DateTime where
  show (MkDateTime s) = s

export
FromString DateTime where
  fromString = MkDateTime

export
FromDouble DateTime where
  fromDouble d = MkDateTime (show d)

%runElab derive "DateTime" [Generic,Meta,Eq,Ord,NewtypeToJSON,NewtypeFromJSON]

-- 5m,15m,30m,h1,h4,h8,d are plenty for now
-- granularity is a mere string in oanda
public export
data CandlestickGranularity = S5 | S10 | S15 | S30
                            | M1 | M2  | M4  | M5 | M10 | M15 | M30
                            | H1 | H2  | H3  | H4 | H6  | H8  | H12
                            | D  | W   | M

%runElab derive "CandlestickGranularity"
  [Generic,Meta,Eq,Ord,Show,DecEq,EnumToJSON,EnumFromJSON]


-- It makes more sense to use doubles, but oanda uses strings for numbers, we'll
-- use strings here to keep this api in step.
public export
record CandlestickData where
  constructor MkCandlestickData
  o : String -- Open
  h : String -- High
  l : String -- Low
  c : String -- Close

-- ToJSON CandlestickData where
--   toJSON (MkCandlestickData o h l c) = array
--     [object ["o" .= cast {to=String} o]
--     ,object ["h" .= cast {to=String} h]
--     ,object ["l" .= cast {to=String} l]
--     ,object ["c" .= cast {to=String} c]]
-- 
-- FromJSON CandlestickData where
--   fromJSON = withObject "CandlestickData" $ \obj => do
--     o <- cast {from=String} <$> obj .: "o"
--     h <- cast {from=String} <$> obj .: "h"
--     l <- cast {from=String} <$> obj .: "l"
--     c <- cast {from=String} <$> obj .: "c"
--     pure $ MkCandlestickData o h l c

%runElab derive "CandlestickData"
  [Generic,Meta,Eq,Show,RecordToJSON,RecordFromJSON]
  -- [Generic,Meta,Eq,Show]

public export
Semigroup CandlestickData where
  x <+> y = { o := o x             -- Open is first open
            , h := max (h x) (h y) -- high is highest high
            , l := min (l x) (l y) -- low is lowest low
            , c := c y} x          -- Close is last close

public export
record Candlestick where
  constructor MkCandlestick
  time : DateTime
  bid : Maybe CandlestickData
  mid : Maybe CandlestickData
  ask : Maybe CandlestickData
  volume : Integer
  complete : Bool

%runElab derive "Candlestick" [Generic,Meta,Show,Eq,RecordToJSON,RecordFromJSON]

public export
Semigroup Candlestick where
  x <+> y = if time x < time y then combine x y else combine y x
    where
      combine : Candlestick -> Candlestick -> Candlestick
      combine a b = {complete := complete a && complete b
                    ,volume   := volume a + volume b
                    ,bid      := bid a <+> bid b
                    ,mid      := mid a <+> mid b
                    ,ask      := ask a <+> ask b} a

public export
record CandlestickResponse where
  constructor MkCandlestickResponse 
  instrument : InstrumentName
  granularity : CandlestickGranularity
  candles : List Candlestick

%runElab derive "CandlestickResponse" [Generic,Meta,Show,Eq,RecordToJSON,RecordFromJSON]



-- The form that oanda json-returned errors take,e.g:
-- {"errorMessage":"Invalid value specified for 'price'"}
export
record ErrorMessage where
  errorMessage : String
%runElab derive "ErrorMessage" [Generic,Meta,Show,Eq,RecordToJSON,RecordFromJSON]

-- 504, timeout waiting for response
public export
data StatusCode =  Ok200 | Err400 | Err401 | Err403 | Err404 | Err405 | Err504
%runElab derive "StatusCode" [Generic,Meta,Show,Eq,Ord]

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
testData : String
testData = """
{"instrument":"USD_CAD","granularity":"D","candles":[{"complete":true,"volume":21318,"time":"2021-08-29T21:00:00.000000000Z","bid":{"o":"1.26205","h":"1.26332","l":"1.25728","c":"1.26037"},"mid":{"o":"1.26255","h":"1.26342","l":"1.25738","c":"1.26060"},"ask":{"o":"1.26305","h":"1.26352","l":"1.25748","c":"1.26082"}},{"complete":false,"volume":1360,"time":"2021-08-30T21:00:00.000000000Z","bid":{"o":"1.26046","h":"1.26150","l":"1.26010","c":"1.26084"},"mid":{"o":"1.26068","h":"1.26160","l":"1.26020","c":"1.26095"},"ask":{"o":"1.26091","h":"1.26171","l":"1.26030","c":"1.26106"}}]}
"""



{-

public export
record TimeStamp where
  constructor MkTimeStamp
  -- seconds : Double
  -- minutes : Integer
  -- hours : Integer
  -- timezone : TimeZone
  unixTime : Double
  -- Seconds since the Unix Epoch (January 1st, 1970 at UTC). The value is a
  -- fractional number, where the fractional part represents a fraction of a
  -- second (up to nine decimal places).

-}