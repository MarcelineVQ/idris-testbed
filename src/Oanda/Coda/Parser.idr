module Oanda.Coda.Parser

--------------------------------------------------
||| Tries to convert parts of a list of string tokens
||| returning either the result plus the remainder
||| of the list or the remainder of the list where parsing failed.
public export
record Parser (t : Type) where
  constructor MkParser
  run : List String -> Either (List String) (t, List String)

public export
Functor Parser where
  map f pa = MkParser $ \ts => do (a,ts') <- pa.run ts
                                  pure (f a, ts')

public export
Applicative Parser where
  pure a = MkParser $ \ts => Right (a,ts)

  pf <*> pa = MkParser $ \ts => do (f, ts' ) <- pf.run ts
                                   (a, ts'') <- pa.run ts'
                                   pure (f a, ts'')

public export
Monad Parser where
  pa >>= f = MkParser $ \ts => do (a, ts' ) <- pa.run ts
                                  (f a).run ts'

public export
Alternative Parser where
  empty = MkParser Left

  p1 <|> p2 = MkParser $ \ts => case p1.run ts of
                                     Left _ => p2.run ts
                                     res    => res

||| Returns the next string token, failing if
||| the list of tokens is empty.
public export
next : Parser String
next = MkParser $ \ts => case ts of
                              []     => Left []
                              (h::t) => Right (h,t)

||| Succeeds if the next token matches exactly the
||| given String.
public export
string : String -> Parser ()
string s = next >>= guard . (s ==)

||| Maps a partial function over the result
||| of a parser. This fails, if the function returns
||| `Nothing`-
public export
mapMaybe : (a -> Maybe b) -> Parser a -> Parser b
mapMaybe f = (>>= maybe empty pure . f)

||| Tries to parse the given number of values.
public export
repeat : Parser a -> Nat -> Parser (List a)
repeat _ 0     = pure []
repeat p (S n) = [| p :: repeat p n |]

||| Runs a parser against a list of string tokens.
||| Fails if not the whole list is consumed.
public export
parse : Parser t -> List String -> Either (List String) t
parse p ts = case p.run ts of
                  Right (t,[]) => Right t
                  Right (_,ts) => Left ts
                  Left ts      => Left ts
--------------------------------------------------