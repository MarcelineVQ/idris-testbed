module Language.C

-- parse C in a limited fashion

import Text.Lexer
import Text.Token

import Text.Parser
import Text.Token

-- import Language.JSON.String
import Text.Token
import Text.Bounded

import Generics.Newtype

%language ElabReflection
%default total

public export
strTrue : String
strTrue = "true"

public export
strFalse : String
strFalse = "false"

public export
data Bracket = Open | Close

%runElab derive "Bracket" [Generic, Meta, Eq, Ord, Show]

public export
data Punctuation
  = Comma
  | Colon
  | SemiColon
  | Square Bracket
  | Round Bracket
  | Curly Bracket

%runElab derive "Punctuation" [Generic, Meta, Eq, Ord, Show]
{-
public export
data JSONTokenKind
  = JTBoolean
  | JTNumber
  | JTString
  | JTNull
  | JTPunct Punctuation
  | JTIgnore

public export
JSONToken : Type
JSONToken = Token JSONTokenKind

public export
Eq JSONTokenKind where
  (==) JTBoolean JTBoolean = True
  (==) JTNumber JTNumber = True
  (==) JTString JTString = True
  (==) JTNull JTNull = True
  (==) (JTPunct p1) (JTPunct p2) = p1 == p2
  (==) _ _ = False

public export
TokenKind JSONTokenKind where
  TokType JTBoolean = Bool
  TokType JTNumber = Double
  TokType JTString = Maybe String
  TokType JTNull = ()
  TokType (JTPunct _) = ()
  TokType JTIgnore = ()

  tokValue JTBoolean x = x == strTrue
  tokValue JTNumber x = cast x
  tokValue JTString x = stringValue x
  tokValue JTNull _ = ()
  tokValue (JTPunct _) _ = ()
  tokValue JTIgnore _ = ()

export
ignored : WithBounds JSONToken -> Bool
ignored (MkBounded (Tok JTIgnore _) _ _) = True
ignored _ = False
-}


-- I want to parse enum defs. for names like f32 I want it to be F32, for names
-- like fooBaz32 I want FOO_BAZ_32
{-
typedef enum {
    f32,    ///< 32-bit floating point values
    c32,    ///< 32-bit complex floating point values
    f64,    ///< 64-bit floating point values
    c64,    ///< 64-bit complex floating point values
    b8 ,    ///< 8-bit boolean values
    s32,    ///< 32-bit signed integral values
    u32,    ///< 32-bit unsigned integral values
    u8 ,    ///< 8-bit unsigned integral values
    s64,    ///< 64-bit signed integral values
    u64    ///< 64-bit unsigned integral values
#if AF_API_VERSION >= 32
    , s16    ///< 16-bit signed integral values
#endif
#if AF_API_VERSION >= 32
    , u16    ///< 16-bit unsigned integral values
#endif
#if AF_API_VERSION >= 37
    , f16    ///< 16-bit floating point value
#endif
} af_dtype;
-}