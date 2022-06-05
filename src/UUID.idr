module UUID

import public Data.String.Parser
import Data.Bits
import public Data.Vect
import Data.List
import Data.String

import System.Clock
import System.Random

{- Variant 1 UUID's

This library makes the choice to treat variant 1 version as 100 instead of 10x as
outlined in https://www.rfc-editor.org/errata/eid5560 in order to made hashing
more predictable.
The problem is futher explained by
https://uuid.pirate-server.com/blog/brother-uuids-or-why-uuids-are-not-unique.html

This is 'wrong' by the literal letter of the spec as "don't care" means leave alone.

This lib doesn't implement DCE UUID version at this time.

-}




-- record UUID where
  -- constructor MkUUID
  -- time_low : (Bits16, Bits16)
  -- time_mid : Bits16
  -- time_hi_and_version : Bits16
  -- clock_seq_hi_and_res__clock_seq_low : Bits16
  -- node : (Bits16,Bits16,Bits16)

-- ^ there's not likely a particular advantage to modeling the UUID structure
-- closely. functions can interpret the form as needed

public export
data Version = Time | DCE | NameMD5 | Random | NameSHA | Undefined

verNum : Version -> Nat
verNum Time = 1
verNum DCE = 2
verNum NameMD5 = 3
verNum Random = 4
verNum NameSHA = 5
verNum Undefined = 0 -- is this correct to do?

numVer : Bits64 -> Version
numVer 1 = Time
numVer 2 = DCE
numVer 3 = NameMD5
numVer 4 = Random
numVer 5 = NameSHA
numVer _ = Undefined

||| 128 bits separated into high and low ends, functions are to treat this as
||| big-endian when appropriate.
||| shiftL high 64 + low = 128-bit UUID
export
data UUID : Type where
  MkUUID : (high : Bits64) -> (low : Bits64) -> UUID
-- This doesn't really leverage idris very well, I should probably have all the
-- fields defined here and their positions in the zeitgeist so idris can tell me
-- when I'm shifting too much or too little

-- time_low : UUID -> Bits32
-- time_low = ?sdfsfd

hexDigit : Applicative m => ParseT m Char -- 8 bits
hexDigit = satisfy isHexDigit <?> "expected [A-F]|[a-f]|[0-9]"

hexOctet : Monad m => ParseT m (Vect 2 Char) -- 16 bits
hexOctet = ntimes 2 hexDigit

time_low : Monad m => ParseT m (Vect 8 Char) -- 32 bits
time_low = concat <$> ntimes 4 hexOctet

time_mid : Monad m => ParseT m (Vect 4 Char) -- 16 bits
time_mid = concat <$> ntimes 2 hexOctet

timehigh_and_version : Monad m => ParseT m (Vect 4 Char) -- 16 bits
timehigh_and_version = concat <$> ntimes 2 hexOctet

clock_seq_and_reserved : Monad m => ParseT m (Vect 2 Char) -- 8 bits
clock_seq_and_reserved = hexOctet

clock_seq_low : Monad m => ParseT m (Vect 2 Char) -- 8 bits
clock_seq_low = hexOctet

node : Monad m => ParseT m (Vect 12 Char) -- 48 bits
node = concat <$> ntimes 6 hexOctet

-- This is cute but there's probably a faster way to do this. e.g. use ord and
-- if it's within the right range, subtract as appropriate. This should also
-- probably fail instead of giving 0's, it's safe how it's used though due to
-- parseUUID validating the input.
fromHex : Num a => Char -> a
fromHex c = fromMaybe 0 $ lookup (toUpper c) hexmap
  where
    hexmap : List (Char,a)
    hexmap = [('0',0),('1',1),('2',2),('3',3),('4',4),
              ('5',5),('6',6),('7',7),('8',8),('9',9),
              ('A',10),('B',11),('C',12),('D',13),('E',14),('F',15)]

-- ^ e.g.
fromHex' : Char -> Int
fromHex' c = let i = ord (toUpper c)
             in if i >= 48 && i <= 57 then i - 48
                  else if i >= 65 && i <= 70 then i - 55
                    else 0

toHexDigit : List Char -> Bits64 -> List Char
toHexDigit acc i' = let i = cast {to=Int} i' in chr (if i < 10 then i + ord '0' else (i-10) + ord 'A') :: acc

toHexDigit' : Bits64 -> Char
toHexDigit' i' = let i = cast {to=Int} i' in chr (if i < 10 then i + ord '0' else (i-10) + ord 'a')

slice : Int -> Bits64 -> List Bits64 -> List Bits64
slice 0 _ acc = acc
slice d n acc = slice (d-1) (n `div` 16) ((n `mod` 16) :: acc)

export
toHex : Bits64 -> List Char
toHex n = map toHexDigit' $ slice 16 n []

accumBits : Vect n Char -> Bits64 -- did you know that every base is base 10?
accumBits = foldl (\acc,v => acc * 0x10 + cast (fromHex' v)) 0

unAccumBits : Bits64 -> List Bits8 -- did you know that every base is base 10?
unAccumBits = unfoldr $ \bs => case (bs `div` 0o10, bs `mod` 0o10) of
    (0,0) => Nothing
    (0,m) => Just (cast m,0)
    (d,m) => Just (cast m,d)

-- TODO: validate the variant and version here
export
parseUUID : Monad m => ParseT m UUID
parseUUID = do
  tl <- (`shiftL`32) . accumBits <$> time_low <* char '-'
  tm <- (`shiftL`16) . accumBits <$> time_mid <* char '-'
  th <-                accumBits <$> timehigh_and_version <* char '-'
  cr <- (`shiftL`56) . accumBits <$> clock_seq_and_reserved
  cl <- (`shiftL`48) . accumBits <$> clock_seq_low <* char '-'
  n  <-                accumBits <$> node
  pure $ MkUUID (tl + tm + th) (cr + cl + n)

||| Chunk a list `ys` into sublists using a list of chunk lengths `ixs`.
||| Discards any remainder `ys` might have. Does not ignore `0` lengths in `ixs`.
||| e.g. chunksFrom [4,0,2] [1,2,3,4,5,6,7] = [[1, 2, 3, 4], [], [5, 6]]
export
chunksFrom : List Nat -> List a -> List (List a)
chunksFrom [] ys = []
chunksFrom (ix :: ixs) ys = case splitAt ix ys of (f,r) => f :: chunksFrom ixs r

export
toString : UUID -> String
toString (MkUUID high low) =
  let hs = chunksFrom [8,4,4] $ toHex high
      ls = chunksFrom [4,12] $ toHex low
  in joinBy "-" $ map pack $ hs ++ ls
 

-- "123e4567-e89b-12d3-a456-426655440000"
-- Right ((1314564453825188563, 11841725277501915136), 36)
export
test1 : UUID
test1 = MkUUID 1314564453825188563 11841725277501915136

-- "00112233-4455-6677-8899-aabbccddeeff"
-- Right ((4822678189205111, 9843086184167632639), 36)
export  -- this one isn't a valid Version
test2 : UUID
test2 = MkUUID 4822678189205111 9843086184167632639

nil : UUID
nil = MkUUID 0 0

-- system generated, time version
test3 : UUID
test3 = either (\_ => nil) fst $ parse parseUUID "76351db8-df1f-11ec-8dfc-94de80a0c588"

-- system generated, random version
test4 : UUID
test4 = either (\_ => nil) fst $ parse parseUUID "05e1dcb3-9503-4c23-baa7-d1269d46f060"

-- system generated, md5
test5 : UUID
test5 = either (\_ => nil) fst $ parse parseUUID "5e2b4bf8-b734-315d-abfb-391349532a3d"

 
-- We can parse and print with the above. Let's make the machinery to generate
-- them ourselves now.

export
getVariant : UUID -> Bits64
getVariant (MkUUID high low) = shiftR low 61

export
getVersion : UUID -> Version
getVersion (MkUUID high low) = numVer $ 0xf .&. shiftR high 12

setVersion : UUID -> Version -> UUID
setVersion (MkUUID high low) ver =
  let v = shiftL (cast {to=Bits64} $ verNum ver) 12
      m = 0xffffffffffff0fff
  in MkUUID ((high .&. m) + v) low

-- case on ver to start
variant1 : HasIO io => Version -> (mac : Maybe Bits64) -> io UUID
variant1 ver mac = do
    utc <- liftIO $ clockTime UTC
    let timestamp = cast {to=Bits64} $ (seconds utc * 1000000000 + nanoseconds utc) `div` 100
    -- let timestamp = the Bits64 0x01d3bfde63b00000
    let time_low  = (timestamp .&. 0x00000000ffffffff) `shiftL` 32
    let time_mid  = (timestamp .&. 0x0000ffff00000000) `shiftR` 16
    let time_high = (timestamp .&. 0xffff000000000000) `shiftR` 48
    let h = time_low + time_mid + time_high
    printLn h
    -- let clk' = (the Bits64 0x00007852) `shiftL` 48
    clk' <- (`shiftL` 48) . cast {to = Bits64} . (.&. 0x0000ffff) <$> randomIO {a = Int32}
    let clk = clearBit (setBit clk' 63) 62 -- variant1
    printLn clk
    let res = MkUUID h (clk + fromMaybe 0 mac)
    pure $ setVersion res ver

public export
data Namespace = MkNS UUID

dnsNS : Namespace
dnsNS = MkNS ?dffd

export
Name : Type
Name = List Bits8

verReq : {io: Type -> Type} -> Version -> Type
verReq Time = Bits64
verReq DCE = Void
verReq NameMD5 = (UUID, Name)
verReq Random = ()
verReq NameSHA = (UUID, Name)
verReq Undefined = Void

-- case on ver to start
genUUID : HasIO io => (ver : Version) -> verReq ver -> io UUID
genUUID Time mac = ?sdfsd_0
genUUID DCE mac = pure nil
genUUID NameMD5 (MkUUID high low, n) = ?sdfd (unAccumBits high ++ unAccumBits low ++ n)
genUUID Random mac = ?sdfsd_3
genUUID NameSHA mac = ?sdfsd_4
genUUID Undefined mac = ?sdfsd_5

-- generation of UUID's should be a Monad in order to ensure increasing/changing values
-- data UUIDGen: Type -> Type where
