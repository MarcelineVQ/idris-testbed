module Data.ArrayFire

import System.FFI

import public Data.Vect
import Data.Fin

import Data.Buffer

import System.Random

import Numeric.Floating

import Util

import Generics.Newtype
%language ElabReflection

-- Shorthand for our custom arrayfire helpers
libArrayFire : String -> String
libArrayFire str = "C:\{str},libarrayfire"

public export
Cast Bool Int where
  cast True = 1
  cast False = 0

--------------------------------------------------

public export
data AFErr = AF_SUCCESS               -- =   0
           | AF_ERR_NO_MEM            -- = 101
           | AF_ERR_DRIVER            -- = 102
           | AF_ERR_RUNTIME           -- = 103
           | AF_ERR_INVALID_ARRAY     -- = 201
           | AF_ERR_ARG               -- = 202
           | AF_ERR_SIZE              -- = 203
           | AF_ERR_TYPE              -- = 204
           | AF_ERR_DIFF_TYPE         -- = 205
           | AF_ERR_BATCH             -- = 207 -- weird name, can result from incorrect dim size for function used, like AF_ERR_SIZE
           | AF_ERR_DEVICE            -- = 208
           | AF_ERR_NOT_SUPPORTED     -- = 301
           | AF_ERR_NOT_CONFIGURED    -- = 302
           | AF_ERR_NONFREE           -- = 303
           | AF_ERR_NO_DBL            -- = 401
           | AF_ERR_NO_GFX            -- = 402
           | AF_ERR_NO_HALF           -- = 403
           | AF_ERR_LOAD_LIB          -- = 501
           | AF_ERR_LOAD_SYM          -- = 502
           | AF_ERR_ARR_BKND_MISMATCH -- = 503
           | AF_ERR_INTERNAL          -- = 998
           | AF_ERR_UNKNOWN           -- = 999
%runElab derive "AFErr" [Generic, Meta, Eq, Ord, Show]

public export
Cast AFErr Int where
  cast AF_SUCCESS               =   0
  cast AF_ERR_NO_MEM            = 101
  cast AF_ERR_DRIVER            = 102
  cast AF_ERR_RUNTIME           = 103
  cast AF_ERR_INVALID_ARRAY     = 201
  cast AF_ERR_ARG               = 202
  cast AF_ERR_SIZE              = 203
  cast AF_ERR_TYPE              = 204
  cast AF_ERR_DIFF_TYPE         = 205
  cast AF_ERR_BATCH             = 207
  cast AF_ERR_DEVICE            = 208
  cast AF_ERR_NOT_SUPPORTED     = 301
  cast AF_ERR_NOT_CONFIGURED    = 302
  cast AF_ERR_NONFREE           = 303
  cast AF_ERR_NO_DBL            = 401
  cast AF_ERR_NO_GFX            = 402
  cast AF_ERR_NO_HALF           = 403
  cast AF_ERR_LOAD_LIB          = 501
  cast AF_ERR_LOAD_SYM          = 502
  cast AF_ERR_ARR_BKND_MISMATCH = 503
  cast AF_ERR_INTERNAL          = 998
  cast AF_ERR_UNKNOWN           = 999

public export
Cast Int AFErr where
  cast 0   = AF_SUCCESS
  cast 101 = AF_ERR_NO_MEM
  cast 102 = AF_ERR_DRIVER
  cast 103 = AF_ERR_RUNTIME
  cast 201 = AF_ERR_INVALID_ARRAY
  cast 202 = AF_ERR_ARG
  cast 203 = AF_ERR_SIZE
  cast 204 = AF_ERR_TYPE
  cast 205 = AF_ERR_DIFF_TYPE
  cast 207 = AF_ERR_BATCH
  cast 208 = AF_ERR_DEVICE
  cast 301 = AF_ERR_NOT_SUPPORTED
  cast 302 = AF_ERR_NOT_CONFIGURED
  cast 303 = AF_ERR_NONFREE
  cast 401 = AF_ERR_NO_DBL
  cast 402 = AF_ERR_NO_GFX
  cast 403 = AF_ERR_NO_HALF
  cast 501 = AF_ERR_LOAD_LIB
  cast 502 = AF_ERR_LOAD_SYM
  cast 503 = AF_ERR_ARR_BKND_MISMATCH
  cast 998 = AF_ERR_INTERNAL
  cast 999 = AF_ERR_UNKNOWN
  cast _   = AF_ERR_UNKNOWN

--------------------------------------------------
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

public export
data DType = F32    -- ///< 32-bit floating point values
           | C32    -- ///< 32-bit complex floating point values
           | F64    -- ///< 64-bit floating point values
           | C64    -- ///< 64-bit complex floating point values
           | B8     -- ///< 8-bit boolean values
           | S32    -- ///< 32-bit signed integral values
           | U32    -- ///< 32-bit unsigned integral values
           | U8     -- ///< 8-bit unsigned integral values
           | S64    -- ///< 64-bit signed integral values
           | U64    -- ///< 64-bit unsigned integral values
           | S16    -- ///< 16-bit signed integral values
           | U16    -- ///< 16-bit unsigned integral values
           | F16    -- ///< 16-bit floating point value
%runElab derive "DType" [Generic, Meta, Eq, Ord, Show]

FromDType : DType -> Type
FromDType F32 = Double
FromDType C32 = Void
FromDType F64 = Double
FromDType C64 = Void
FromDType B8 = Bool
FromDType S32 = Int32
FromDType U32 = Bits32
FromDType U8 = Bits8
FromDType S64 = Int64
FromDType U64 = Bits64
FromDType S16 = Int32
FromDType U16 = Bits32
FromDType F16 = Double

ToDType : Type -> DType
ToDType Double = F64
ToDType Bool = B8
ToDType Int32 = S32
ToDType Bits32 = U32
ToDType Bits8 = B8
ToDType Int64 = S64
ToDType Bits64 = U64
ToDType Int32 = S32
ToDType Bits32 = U32
ToDType _ = F64 -- idris is mostly Double so we'll default to F64 instead of F32

public export
Cast DType Int where
  cast F32 = 0
  cast C32 = 1
  cast F64 = 2
  cast C64 = 3
  cast B8 = 4
  cast S32 = 5
  cast U32 = 6
  cast U8 = 7
  cast S64 = 8
  cast U64 = 9
  cast S16 = 10
  cast U16 = 11
  cast F16 = 12

data MatProp = AF_MAT_NONE        --    ///< Default
             | AF_MAT_TRANS       --    ///< Data needs to be transposed
             | AF_MAT_CTRANS      --    ///< Data needs to be conjugate tansposed
             | AF_MAT_CONJ        --    ///< Data needs to be conjugate
             | AF_MAT_UPPER       --   ///< Matrix is upper triangular
             | AF_MAT_LOWER       --   ///< Matrix is lower triangular
             | AF_MAT_DIAG_UNIT   --  ///< Matrix diagonal contains unitary values
             | AF_MAT_SYM         --  ///< Matrix is symmetric
             | AF_MAT_POSDEF      -- ///< Matrix is positive definite
             | AF_MAT_ORTHOG      -- ///< Matrix is orthogonal
             | AF_MAT_TRI_DIAG    -- ///< Matrix is tri diagonal
             | AF_MAT_BLOCK_DIAG  -- ///< Matrix is block diagonal

Cast MatProp Int where
  cast AF_MAT_NONE = 0
  cast AF_MAT_TRANS = 1
  cast AF_MAT_CTRANS = 2
  cast AF_MAT_CONJ = 4
  cast AF_MAT_UPPER = 32
  cast AF_MAT_LOWER = 64
  cast AF_MAT_DIAG_UNIT = 128
  cast AF_MAT_SYM = 512
  cast AF_MAT_POSDEF = 1024
  cast AF_MAT_ORTHOG = 2048
  cast AF_MAT_TRI_DIAG = 4096
  cast AF_MAT_BLOCK_DIAG = 8192

Cast Int MatProp where
  cast 1 = AF_MAT_TRANS
  cast 2 = AF_MAT_CTRANS
  cast 4 = AF_MAT_CONJ
  cast 32 = AF_MAT_UPPER
  cast 64 = AF_MAT_LOWER
  cast 128 = AF_MAT_DIAG_UNIT
  cast 512 = AF_MAT_SYM
  cast 1024 = AF_MAT_POSDEF
  cast 2048 = AF_MAT_ORTHOG
  cast 4096 = AF_MAT_TRI_DIAG
  cast 8192 = AF_MAT_BLOCK_DIAG
  cast _ = AF_MAT_NONE

public export
data AFRandomEngineType = AF_RANDOM_ENGINE_PHILOX_4X32_10   --  = 100                                 --  //Philox variant with N = 4, W = 32 and Rounds = 10
                        | AF_RANDOM_ENGINE_THREEFRY_2X32_16 --  = 200                                 --  //Threefry variant with N = 2, W = 32 and Rounds = 16
                        | AF_RANDOM_ENGINE_MERSENNE_GP11213 --  = 300                                 --  //Mersenne variant with MEXP = 11213
                        | AF_RANDOM_ENGINE_PHILOX           --  = AF_RANDOM_ENGINE_PHILOX_4X32_10     --  //Resolves to Philox 4x32_10
                        | AF_RANDOM_ENGINE_THREEFRY         --  = AF_RANDOM_ENGINE_THREEFRY_2X32_16   --  //Resolves to Threefry 2X32_16
                        | AF_RANDOM_ENGINE_MERSENNE         --  = AF_RANDOM_ENGINE_MERSENNE_GP11213   --  //Resolves to Mersenne GP 11213
                        | AF_RANDOM_ENGINE_DEFAULT          --  = AF_RANDOM_ENGINE_PHILOX             --  //Resolves to Philox

export
Cast AFRandomEngineType Int where
  cast AF_RANDOM_ENGINE_PHILOX_4X32_10     = 100
  cast AF_RANDOM_ENGINE_THREEFRY_2X32_16   = 200
  cast AF_RANDOM_ENGINE_MERSENNE_GP11213   = 300
  cast AF_RANDOM_ENGINE_PHILOX             = cast AF_RANDOM_ENGINE_PHILOX_4X32_10
  cast AF_RANDOM_ENGINE_THREEFRY           = cast AF_RANDOM_ENGINE_THREEFRY_2X32_16
  cast AF_RANDOM_ENGINE_MERSENNE           = cast AF_RANDOM_ENGINE_MERSENNE_GP11213
  cast AF_RANDOM_ENGINE_DEFAULT            = cast AF_RANDOM_ENGINE_PHILOX

export
Cast Int AFRandomEngineType where
  cast 100 = AF_RANDOM_ENGINE_PHILOX_4X32_10
  cast 200 = AF_RANDOM_ENGINE_THREEFRY_2X32_16
  cast 300 = AF_RANDOM_ENGINE_MERSENNE_GP11213
  cast _ = AF_RANDOM_ENGINE_DEFAULT


{-
    /**
        \param[out] out The generated array
        \param[in] ndims Size of dimension array \p dims
        \param[in] dims The array containing sizes of the dimension
        \param[in] type The type of array to generate

       \ingroup random_func_randu
    */
    AFAPI af_err af_randu(af_array *out, const unsigned ndims,
                          const dim_t * const dims, const af_dtype type);
-}

-- export
-- data ForeignPtr : Type -> Type where
  -- MkFP : GCPtr t -> ForeignPtr t

export %foreign libArrayFire "deref_double"
deref_double : Ptr Double -> PrimIO Double

export %foreign libArrayFire "deref_bits64"
deref_bits64 : Ptr Bits64 -> PrimIO Bits64

export %foreign libArrayFire "size_of_double"
size_of_double : Int

export %foreign libArrayFire "size_of_bits64"
size_of_bits64 : Int

export %foreign libArrayFire "size_of_dim_t"
size_of_dim_t : Int

export %foreign libArrayFire "size_of_void"
size_of_void : Int

||| Overload free to eliminate some hassle.
free : HasIO io => Ptr t -> io ()
free = free . prim__forgetPtr

export
||| Control the lifetime of an allocation by running free when it's garbage
||| collected.
alloc : HasIO io => Int -> io (GCPtr t)
alloc s = prim__castPtr !(malloc s) `onCollect` free

export
||| Control the lifetime of an allocation by freeing it immediately after the
||| action using it completes.
alloc' : HasIO io => Int -> (Ptr t -> io a) -> io a
alloc' s act = do
  ptr <- malloc s
  r <- act (prim__castPtr ptr)
  free ptr
  pure r

export
||| Control the lifetime of an allocation by running a custom function on it
||| when it's garbage collected.
allocThen : HasIO io => Int -> (Ptr t -> IO ()) -> io (GCPtr t)
allocThen s act = prim__castPtr !(malloc s) `onCollect` act

{- af_array is a typedef for void*, so af_array *out is  **out, so we only need
to allocate a pointer, not enough memory for more -}
public export
data AFArrayPtrTag : Type where

CAFArray : Type -- void*
CAFArray = Ptr AFArrayPtrTag

export %foreign libArrayFire "deref"
derefCafArray : GCPtr CAFArray -> CAFArray

export %foreign libArrayFire "deref"
derefCafArray' : Ptr CAFArray -> CAFArray

export %foreign libArrayFire "deref"
derefString : Ptr (Ptr String) -> Ptr String

export %foreign libArrayFire "af_release_array"
af_release_array : CAFArray -> PrimIO Int
    -- AFAPI af_err af_release_array(af_array arr);

export
||| Control the lifetime of an array by running free when it's garbage
||| collected and freeing from the AF backend.
allocAF : HasIO io => io (GCPtr CAFArray)
allocAF = onCollect (prim__castPtr !(malloc size_of_void)) $ \ptr => do
  -- free af's mem
  r <- map (cast {to = AFErr}) . primIO $ af_release_array (derefCafArray' ptr)
  unless (r == AF_SUCCESS) $ printLn r
  -- free our ptr
  -- printLn r
  free ptr

-- dims is actually max 4 long
public export
data AFArray : Vect n Nat -> DType -> Type where
  MkAFArray : GCPtr CAFArray -> (n : Nat) -> (dims : Vect n Nat) -> (dt : DType) -> AFArray dims dt

export
sizeOfAFArray : AFArray dims ty -> Int
sizeOfAFArray (MkAFArray _ _ dims _) = cast $ product dims

wrapAPIFunc : (func : String) -> (msg : String) -> IO (Either AFErr a) -> a
wrapAPIFunc func msg act =
  either (\err => lieErrorCall "ArrayFire" func (msg ++ ": " ++ show err)) id (unsafePerformIO act)

wrapIOAPIFunc : HasIO io => (func : String) -> (msg : String) -> io (Either AFErr a) -> io a
wrapIOAPIFunc func msg act =
  pure . either (\err => lieErrorCall "ArrayFire" func (msg ++ ": " ++ show err)) id =<< act

public export
interface Storable a where
  -- sizeOf : a -> Int
  peek : HasIO io => Ptr a -> Int -> io a
  poke : HasIO io => Ptr a -> Int -> a -> io ()

export %foreign libArrayFire "int_peek"
int_peek : Ptr Int -> (offset : Int) -> PrimIO Int

export %foreign libArrayFire "int_poke"
int_poke : Ptr Int -> (offset : Int) -> Int -> PrimIO ()

public export
Storable Int where
  peek ptr i = primIO (int_peek ptr i)
  poke ptr i v = primIO $ int_poke ptr i v

public export
data Dim = MkDim Int

export %foreign libArrayFire "dim_peek"
dim_peek : (newAfarray : Ptr Dim) -> (offset : Int) -> PrimIO Int

export %foreign libArrayFire "dim_poke"
dim_poke : (newAfarray : Ptr Dim) -> (offset : Int) -> Int -> PrimIO ()

public export
Storable Dim where
  peek ptr i = MkDim <$> primIO (dim_peek ptr i)
  poke ptr i (MkDim v) = primIO $ dim_poke ptr i v

getDereffedCAFArray : AFArray dims ty -> CAFArray
getDereffedCAFArray (MkAFArray ptr _ _ _) = derefCafArray ptr

--------------------------------------------------

afNumOp1 : HasIO io => (op : GCPtr CAFArray -> CAFArray -> PrimIO Int) -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afNumOp1 op (MkAFArray xptr n dims dt) = do
    ptr <- allocAF
    res <- primIO $ op ptr (derefCafArray xptr)
    case cast res of
      AF_SUCCESS => pure (Right (MkAFArray ptr n dims dt))
      err => pure (Left err)

afNumOp2 : HasIO io => (op : GCPtr CAFArray -> CAFArray -> CAFArray -> Int -> PrimIO Int) -> AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afNumOp2 op (MkAFArray xptr n dims dt) (MkAFArray yptr _ _ _) = do
    ptr <- allocAF
    res <- primIO $ op ptr (derefCafArray xptr) (derefCafArray yptr) (cast False)
    case cast res of
      AF_SUCCESS => pure (Right (MkAFArray ptr n dims dt))
      err => pure (Left err)

afNumOp3 : HasIO io => (op : GCPtr CAFArray -> CAFArray -> CAFArray -> CAFArray -> Int -> PrimIO Int) -> AFArray dims dt -> AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afNumOp3 op (MkAFArray x n' dims dt) y z = do
    ptr <- allocAF
    AF_SUCCESS <- map cast . primIO $ op ptr (derefCafArray x) (getDereffedCAFArray y) (getDereffedCAFArray z) (cast False)
      | err => pure (Left err)
    pure (Right (MkAFArray ptr n' dims dt))

export %foreign libArrayFire "af_add"
af_add : (newAFarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afAdd : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAdd = afNumOp2 af_add

export %foreign libArrayFire "af_sub"
af_sub : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afSub : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSub = afNumOp2 af_sub

export %foreign libArrayFire "af_mul"
af_mul : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afMul : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afMul = afNumOp2 af_mul

export %foreign libArrayFire "af_div"
af_div : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afDiv : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afDiv = afNumOp2 af_div

export %foreign libArrayFire "af_abs"
af_abs : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afAbs : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAbs = afNumOp1 af_abs

export %foreign libArrayFire "af_exp"
af_exp : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afExp : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afExp = afNumOp1 af_exp

export %foreign libArrayFire "af_pow"
af_pow : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afPow : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afPow = afNumOp2 af_pow

export %foreign libArrayFire "af_log"
af_log : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afLog : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afLog = afNumOp1 af_log

export %foreign libArrayFire "af_sin"
af_sin : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afSin : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSin = afNumOp1 af_sin

export %foreign libArrayFire "af_cos"
af_cos : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afCos : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afCos = afNumOp1 af_cos

export %foreign libArrayFire "af_tan"
af_tan : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afTan : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afTan = afNumOp1 af_tan

export %foreign libArrayFire "af_asin"
af_asin : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afAsin : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAsin = afNumOp1 af_asin

export %foreign libArrayFire "af_acos"
af_acos : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afAcos : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAcos = afNumOp1 af_acos

export %foreign libArrayFire "af_atan"
af_atan : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afAtan : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAtan = afNumOp1 af_atan

export %foreign libArrayFire "af_sinh"
af_sinh : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afSinh : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSinh = afNumOp1 af_sinh

export %foreign libArrayFire "af_cosh"
af_cosh : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afCosh : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afCosh = afNumOp1 af_cosh

export %foreign libArrayFire "af_tanh"
af_tanh : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afTanh : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afTanh = afNumOp1 af_tanh

export %foreign libArrayFire "af_sqrt"
af_sqrt : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afSqrt : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSqrt = afNumOp1 af_sqrt

export %foreign libArrayFire "af_sigmoid"
af_sigmoid : (newAfarray : GCPtr CAFArray) -> (lhs : CAFArray) -> PrimIO Int

export
afSigmoid : HasIO io => AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSigmoid = afNumOp1 af_sigmoid

export
sigmoid : AFArray dims dt -> AFArray dims dt
sigmoid x = wrapAPIFunc "afSigmoid" "sigmoid" $ afSigmoid x

--------------------------------------------------

-- booleans

export %foreign libArrayFire "af_and"
af_and : (newAFarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afAnd : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afAnd = afNumOp2 af_and
    -- AFAPI af_err af_le    (af_array *out, const af_array lhs, const af_array rhs, const bool batch);

export
and : AFArray dims dt -> AFArray dims dt -> AFArray dims dt
and x y = wrapAPIFunc "afAnd" "and" $ afAnd x y

export %foreign libArrayFire "af_le"
af_le : (newAFarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (bool : Int) -> PrimIO Int

export
afLe : HasIO io => AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afLe = afNumOp2 af_le
    -- AFAPI af_err af_le    (af_array *out, const af_array lhs, const af_array rhs, const bool batch);

export
le : AFArray dims dt -> AFArray dims dt -> AFArray dims dt
le x y = wrapAPIFunc "afLe" "le" $ afLe x y


--------------------------------------------------

export %foreign libArrayFire "af_max"
af_max : (newAFarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (dim : Int) -> PrimIO Int

export
afMax : HasIO io => AFArray (dim :: r) dt -> io (Either AFErr (AFArray [dim] dt))
afMax (MkAFArray xptr (S n) (dim :: r) dt) = do
    ptr <- allocAF
    AF_SUCCESS <- map cast . primIO $ af_max ptr (derefCafArray xptr) 0
      | err => pure (Left err)
    pure (Right (MkAFArray ptr 1 [dim] dt))
    -- AFAPI af_err af_max(af_array *out, const af_array in, const int dim);


export %foreign libArrayFire "af_min"
af_min : (newAFarray : GCPtr CAFArray) -> (lhs : CAFArray) -> (dim : Int) -> PrimIO Int

export
afMin : HasIO io => AFArray (dim :: r) dt -> io (Either AFErr (AFArray [dim] dt))
afMin (MkAFArray xptr (S n) (dim :: r) dt) = do
    ptr <- allocAF
    AF_SUCCESS <- map cast . primIO $ af_min ptr (derefCafArray xptr) 0
      | err => pure (Left err)
    pure (Right (MkAFArray ptr 1 [dim] dt))
    -- AFAPI af_err af_min(af_array *out, const af_array in, const int dim);

export
min : AFArray (dim :: _) dt -> AFArray [dim] dt
min x = wrapAPIFunc "afMin" "min" $ afMin x

--------------------------------------------------

export %foreign libArrayFire "af_print_array"
af_print_array : CAFArray -> PrimIO Int

export
afPrintArray : HasIO io => AFArray dims dt -> io AFErr
afPrintArray (MkAFArray arr _ _ _) = map cast . primIO $ af_print_array (derefCafArray arr)

export %foreign libArrayFire "af_array_to_string"
af_array_to_string : Ptr (Ptr String) -> String -> CAFArray -> (precision : Int) -> (trans : Int) -> PrimIO Int

export
afArrayToString : HasIO io => AFArray dims dt -> io (Either AFErr String)
afArrayToString (MkAFArray arr _ _ _) =
  alloc' size_of_void $ \ptr => do
    AF_SUCCESS <- map cast . primIO $ af_array_to_string ptr "" (derefCafArray arr) 7 0
      | err =>  pure (Left err)
    let strptr = derefString ptr
        str = prim__getString strptr
    free strptr
    pure $ Right str
    -- AFAPI af_err af_array_to_string(char **output, const char *exp, const af_array arr,
                                    -- const int precision, const bool transpose);

export
arrayToString : AFArray dims dt -> String
arrayToString arr = wrapAPIFunc "afArrayToString" "arrayToString" (afArrayToString arr)

export
Show (AFArray dims dt) where
  show = arrayToString

--------------------------------------------------

data RandomEngineTag : Type where

CAFRandomEngine : Type
CAFRandomEngine = Ptr RandomEngineTag -- void*

public export
data RandomEngine : Type where
  MkRandomEngine : GCPtr CAFRandomEngine -> (seed : Bits64) -> RandomEngine

export %foreign libArrayFire "deref"
derefCafRandomEngine : GCPtr CAFRandomEngine -> CAFRandomEngine

export %foreign libArrayFire "af_create_random_engine"
af_create_random_engine : GCPtr CAFRandomEngine -> (rtype : Int) -> (seed : Bits64) -> PrimIO Int

-- this should have its own gc method prob
export
afCreateRandomEngine : HasIO io => AFRandomEngineType -> (seed : Bits64) -> io (Either AFErr RandomEngine)
afCreateRandomEngine ty seed = do
      ptr <- alloc size_of_void
      AF_SUCCESS <- map cast . primIO $ af_create_random_engine ptr (cast ty) seed
        | err =>  pure (Left err)
      pure $ Right $ MkRandomEngine ptr seed
    -- AFAPI af_err af_create_random_engine(af_random_engine *engine,
                                         -- af_random_engine_type rtype,
                                         -- unsigned long long seed);
export %foreign libArrayFire "af_set_seed"
af_set_seed : Bits64 -> PrimIO Int

export
afSetSeed : HasIO io => Bits64 -> io AFErr
afSetSeed seed = map cast . primIO $ af_set_seed seed
    -- AFAPI af_err af_set_seed(const unsigned long long seed);

export %foreign libArrayFire "af_get_seed"
af_get_seed : Ptr Bits64 -> PrimIO Int

export
afGetSeed : HasIO io => io (Either AFErr Bits64)
afGetSeed = alloc' size_of_void $ \ptr => do
  AF_SUCCESS <- map cast . primIO $ af_get_seed ptr
    | err => pure $ Left err
  d <- primIO $ deref_bits64 ptr
  pure $ Right d

--------------------------------------------------

fillDims : HasIO io => Vect n Nat -> Ptr Dim -> io (Ptr Dim)
fillDims = dimsloop 0
  where
    dimsloop : forall n. Int -> Vect n Nat -> Ptr Dim -> io (Ptr Dim)
    dimsloop i [] ptr = pure ptr
    dimsloop i (x :: xs) ptr = poke ptr i (MkDim (cast x)) *> dimsloop (i + 1) xs ptr

export %foreign libArrayFire "af_create_handle"
af_create_handle : (newAFarray : GCPtr CAFArray) -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> PrimIO Int


export %foreign libArrayFire "af_create_array"
af_create_array : (newAFarray : GCPtr CAFArray) -> Buffer -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> PrimIO Int

export
afCreateArray : HasIO io => Buffer -> (dt : DType) -> (dims : Vect n Nat) -> io (Either AFErr (AFArray dims dt))
afCreateArray datas dt dims = do
    let dimcount = cast (length dims)
    alloc' (size_of_dim_t * dimcount) $ \dimbuf => do
      ptr <- allocAF
      AF_SUCCESS <- map cast . primIO $ af_create_array ptr datas dimcount !(fillDims dims dimbuf) (cast dt)
        | err =>  pure (Left err)
      let dims' : Vect (length dims) Nat
          dims' = rewrite lengthCorrect dims in dims
      pure $ Right $ rewrite sym (lengthCorrect dims) in MkAFArray ptr (length dims) dims' dt
    -- AFAPI af_err af_create_array(af_array *arr, const void * const data, const unsigned ndims, const dim_t * const dims, const af_dtype type);

export
createArrayIO : HasIO io => Buffer -> (dt : DType) -> (dims : Vect n Nat) -> io (AFArray dims dt)
createArrayIO b dt dims = wrapIOAPIFunc "afCreateArray" "createArray" $ afCreateArray b dt dims

export
createArray : Buffer -> (dt : DType) -> (dims : Vect n Nat) -> AFArray dims dt
createArray b dt dims = wrapAPIFunc "afCreateArray" "createArray" $ afCreateArray b dt dims


data Dims : List Nat -> Type where
  Dim1 : GCAnyPtr -> Dims [a]
  Dim2 : GCAnyPtr -> Dims [a,b]
  Dim3 : GCAnyPtr -> Dims [a,b,c]
  Dim4 : GCAnyPtr -> Dims [a,d,b,c]

arf : (xs : Vect n a) -> Vect n a = Vect (length xs) a
arf xs = rewrite lengthCorrect xs in Refl

export %foreign libArrayFire "af_random_uniform"
af_random_uniform : (newAFarray : GCPtr CAFArray) -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> CAFRandomEngine -> PrimIO Int

export
afRandomUniform : HasIO io => (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> io (Either AFErr (AFArray dims dt))
afRandomUniform (MkRandomEngine rptr _) dt dims = do
    let dimcount = cast (length dims)
    alloc' (size_of_dim_t * dimcount) $ \dimbuf => do
      ptr <- allocAF
      AF_SUCCESS <- map cast . primIO $ af_random_uniform ptr dimcount !(fillDims dims dimbuf) (cast dt) (derefCafRandomEngine rptr)
        | err =>  pure (Left err)
      let dims' : Vect (length dims) Nat
          dims' = rewrite lengthCorrect dims in dims
      pure $ Right $ rewrite sym (lengthCorrect dims) in MkAFArray ptr (length dims) dims' dt

export
randomUniform : (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> AFArray dims dt
randomUniform rand dt dims = wrapAPIFunc "afRandomUniform" "randomUniform" $ afRandomUniform rand dt dims

export
randomUniform' : {auto rand : RandomEngine} -> {dt : DType} -> {dims : Vect n Nat} -> AFArray dims dt
randomUniform' = wrapAPIFunc "afRandomUniform" "randomUniform" $ afRandomUniform rand dt dims

export
randomUniformIO : HasIO io => (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> io (AFArray dims dt)
randomUniformIO rand dt dims = wrapIOAPIFunc "afRandomUniform" "randomUniform" $ afRandomUniform rand dt dims

export
randomUniformIO' : HasIO io => {auto rand : RandomEngine} -> {dt : DType} -> {dims : Vect n Nat} -> io (AFArray dims dt)
randomUniformIO' = wrapIOAPIFunc "afRandomUniform" "randomUniform" $ afRandomUniform rand dt dims

export %foreign libArrayFire "af_random_normal"
af_random_normal : (newAFarray : GCPtr CAFArray) -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> CAFRandomEngine -> PrimIO Int

export
afRandomNormal : HasIO io => (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> io (Either AFErr (AFArray dims dt))
afRandomNormal (MkRandomEngine rptr _) dt dims = do
    let dimcount = cast (length dims)
    alloc' (size_of_dim_t * dimcount) $ \dimbuf => do
      ptr <- allocAF
      AF_SUCCESS <- map cast . primIO $ af_random_normal ptr dimcount !(fillDims dims dimbuf) (cast dt) (derefCafRandomEngine rptr)
        | err =>  pure (Left err)
      let dims' : Vect (length dims) Nat
          dims' = rewrite lengthCorrect dims in dims
      pure $ Right $ rewrite sym (lengthCorrect dims) in MkAFArray ptr (length dims) dims' dt

export
randomNormal : (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> AFArray dims dt
randomNormal rand dt dims = wrapAPIFunc "afRandomNormal" "randomNormal" $ afRandomNormal rand dt dims

export
randomNormal' : {auto rand : RandomEngine} -> {dt : DType} -> {dims : Vect n Nat} -> AFArray dims dt
randomNormal' = wrapAPIFunc "afRandomNormal" "randomNormal" $ afRandomNormal rand dt dims

export
randomNormalIO : HasIO io => (rand : RandomEngine) -> (dt : DType) -> (dims : Vect n Nat) -> io (AFArray dims dt)
randomNormalIO rand dt dims = wrapIOAPIFunc "afRandomNormal" "randomNormal" $ afRandomNormal rand dt dims

export
randomNormalIO' : HasIO io => {auto rand : RandomEngine} -> {dt : DType} -> {dims : Vect n Nat} -> io (AFArray dims dt)
randomNormalIO' = wrapIOAPIFunc "afRandomNormal" "randomNormal" $ afRandomNormal rand dt dims


export %foreign libArrayFire "af_constant"
af_constant : (newAFarray : GCPtr CAFArray) -> Double -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> PrimIO Int

export
afConstant : HasIO io => (dt : DType) -> (dims : Vect n Nat) -> Double -> io (Either AFErr (AFArray dims dt))
afConstant dt dims v = do
    let dimcount = cast (length dims)
    alloc' (size_of_dim_t * dimcount) $ \dimbuf => do
      ptr <- allocAF
      AF_SUCCESS <- map cast . primIO $ af_constant ptr v dimcount !(fillDims dims dimbuf) (cast dt)
        | err =>  pure (Left err)
      let dims' : Vect (length dims) Nat
          dims' = rewrite lengthCorrect dims in dims
      pure $ Right $ rewrite sym (lengthCorrect dims) in MkAFArray ptr (length dims) dims' dt

export
constant : (dt : DType) -> (dims : Vect n Nat) -> Double -> AFArray dims dt
constant dt dims d = wrapAPIFunc "afConstant" "constant" (afConstant dt dims d)

%foreign libArrayFire "af_randu"
export
af_randu : (newAFarray : GCPtr CAFArray) -> (dimslen : Int) -> (dims : Ptr Dim) -> (dtype : Int) -> PrimIO Int

-- export
-- afRandu : HasIO io => {n:_} -> (dt : DType) -> (dims : Vect n Nat) -> io (Either AFErr (AFArray dims dt))
-- afRandu dt dims = do
--     let dimcount = cast n
--     alloc' (size_of_dim_t * dimcount) $ \dimbuf => do
--       ptr <- allocAF
--       res <- primIO $ af_randu ptr dimcount !(fillDims dims dimbuf) (cast dt)
--       case cast res of
--         AF_SUCCESS => pure (Right (MkAFArray ptr n dims dt))
--         err => pure (Left err)
--   where
--     dimsloop : forall n. Int -> Vect n Nat -> Ptr Dim -> io ()
--     dimsloop i [] _ = pure ()
--     dimsloop i (x :: xs) ptr = poke ptr i (MkDim (cast x)) *> dimsloop (i + 1) xs ptr
-- 
-- export
-- randu : {n:_} -> (dt : DType) -> (dims : Vect n Nat) -> AFArray dims dt
-- randu dt dims = wrapAPIFunc "afRandu" "randu" $ afRandu dt dims

--------------------------------------------------

%foreign libArrayFire "af_select"
export
af_select : (newAFarray : GCPtr CAFArray) -> (cond : CAFArray) -> (a : CAFArray) -> (b : CAFArray) -> PrimIO Int

export
afSelect : HasIO io => AFArray dims dt -> AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afSelect (MkAFArray condptr n dims dt) a b = do
    new <- allocAF
    AF_SUCCESS <- map cast . primIO $ af_select new (derefCafArray condptr) (getDereffedCAFArray a) (getDereffedCAFArray b)
      | err => pure $ Left err
    pure (Right (MkAFArray new n dims dt))
    -- AFAPI af_err af_select(af_array *out, const af_array cond, const af_array a, const af_array b);

export
select : AFArray dims dt -> AFArray dims dt -> AFArray dims dt -> AFArray dims dt
select cond a b = wrapAPIFunc "afSelect" "select" $ afSelect cond a b


--------------------------------------------------

%foreign libArrayFire "af_get_scalar"
export
af_get_scalar : AnyPtr -> (arr : CAFArray) -> PrimIO Int

export
afGetScalarD : HasIO io => AFArray dims dt -> io (Either AFErr Double)
afGetScalarD (MkAFArray arrptr _ _ _) = alloc' size_of_double $ \ptr => do
      AF_SUCCESS <- map cast . primIO $ af_get_scalar (prim__forgetPtr ptr) (derefCafArray arrptr)
        | err => pure (Left err)
      d <- primIO $ deref_double ptr
      pure $ Right $ d
      -- AFAPI af_err af_get_scalar(void* output_value, const af_array arr);

export
afGetScalarB64 : HasIO io => AFArray dims dt -> io (Either AFErr Bits64)
afGetScalarB64 (MkAFArray arrptr _ _ _) = alloc' size_of_bits64 $ \ptr => do
      AF_SUCCESS <- map cast . primIO $ af_get_scalar (prim__forgetPtr ptr) (derefCafArray arrptr)
        | err => pure (Left err)
      b <- primIO $ deref_bits64 ptr
      pure $ Right $ b
      -- AFAPI af_err af_get_scalar(void* output_value, const af_array arr);

export
getScalarD : AFArray dims dt -> Double
getScalarD arr = wrapAPIFunc "afGetScalarD" "getScalarD" $ afGetScalarD arr

export
getScalarB64 : AFArray dims dt -> Bits64
getScalarB64 arr = wrapAPIFunc "afGetScalarB64" "getScalarB64" $ afGetScalarB64 arr

--------------------------------------------------


export %foreign libArrayFire "af_dot_all"
af_dot_all : (real : Ptr Double) -> (imag : Ptr Double) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (optLhs : Int) -> (optRhs : Int) -> PrimIO Int

export -- doesn't seem to handle multiple dim
afDotAll : HasIO io => AFArray [n] dt -> AFArray [n] dt -> io (Either AFErr Double)
afDotAll (MkAFArray xptr _ _ _) (MkAFArray yptr _ _ _) =
    alloc' size_of_double $ \d => alloc' size_of_double $ \i => do
    AF_SUCCESS <- map cast . primIO $ af_dot_all d i (derefCafArray xptr) (derefCafArray yptr) 0 0
      | err => pure (Left err)
    d' <- primIO $ deref_double d
    pure $ Right d'
    -- AFAPI af_err af_dot_all(double *real, double *imag,
                            -- const af_array lhs, const af_array rhs,
                            -- const af_mat_prop optLhs, const af_mat_prop optRhs);

export %foreign libArrayFire "af_clamp"
af_clamp : (newAfarray : GCPtr CAFArray) -> (in' : CAFArray) -> (low : CAFArray) -> (high : CAFArray) -> (bool : Int) -> PrimIO Int

export
afClamp : HasIO io => AFArray dims dt -> AFArray dims dt -> AFArray dims dt -> io (Either AFErr (AFArray dims dt))
afClamp = afNumOp3 af_clamp
    -- AFAPI af_err af_clamp(af_array *out, const af_array in,
                          -- const af_array lo, const af_array hi, const bool batch);

export
clamp : AFArray dims dt -> AFArray dims dt -> AFArray dims dt -> AFArray dims dt
clamp n lo hi = wrapAPIFunc "afClamp" "clamp" $ afClamp n lo hi


export
DTypeFn : DType -> Type

export %foreign libArrayFire "af_sum_all"
af_sum_all : (real : Ptr Double) -> (imag : Ptr Double) -> (in' : CAFArray) -> PrimIO Int

export
afSumAll : HasIO io => AFArray dims dt -> io (Either AFErr Double)
afSumAll (MkAFArray xptr _ _ _) =
    alloc' size_of_double $ \d => alloc' size_of_double $ \i => do
    AF_SUCCESS <- map cast . primIO $ af_sum_all d i (derefCafArray xptr)
      | err => pure (Left err)
    d' <- primIO $ deref_double d
    pure $ Right d'
-- AFAPI af_err af_sum_all(double *real, double *imag, const af_array in);

export
sumAll : AFArray dims dt -> Double
sumAll arr = wrapAPIFunc "afSumAll" "sumAll" $ afSumAll arr

export %foreign libArrayFire "af_lookup"
af_lookup : (out : GCPtr CAFArray) -> (in' : CAFArray) -> (indices : CAFArray) -> (dim : Int) -> PrimIO Int

export
afLookup : HasIO io => AFArray dims dt -> Int -> io (Either AFErr Double)
afLookup (MkAFArray ptr _ _ dt) ix = do
    new <- allocAF
    Right (MkAFArray r _ _ _) <- afConstant F32 [1] (cast ix)
      | Left err => pure $ Left err
    _ <- primIO $ af_print_array (derefCafArray r)
    res <- primIO $ af_lookup new (derefCafArray ptr) (derefCafArray r) 0
    _ <- primIO $ af_print_array (derefCafArray new)
    case cast res of
      AF_SUCCESS => do
        Right r <- afSumAll (MkAFArray new 1 [1] dt)
          | Left err => pure $ Left err
        _ <- afPrintArray ((MkAFArray new 1 [1] dt))
        pure $ Right r
      err => pure (Left err)
    -- AFAPI af_err af_lookup( af_array *out,
                            -- const af_array in, const af_array indices,
                            -- const unsigned dim);


-- we can achieve perturb by generating a random uniform array and ge 0.5
-- this gives us an array of 1's saying where to make updates, 
-- and then combining 

--------------------------------------------------

export %foreign libArrayFire "af_device_gc"
af_device_gc : PrimIO Int

export
afDeviceGC : HasIO io => io AFErr
afDeviceGC = map cast . primIO $ af_device_gc
    -- AFAPI af_err af_device_gc();

export %foreign libArrayFire "af_info"
af_info : PrimIO ()

export %foreign libArrayFire "af_info_string"
af_info_string : Ptr (Ptr String) -> (bool : Int) -> PrimIO String

export
infoString : HasIO io => io String
infoString = do
  ptr <- prim__castPtr <$> malloc 8
  res <- primIO $ af_info_string ptr (cast False)
  pure $ prim__getString (derefString ptr)

--------------------------------------------------

--------------------------------------------------
-- Backend
--------------------------------------------------

data AFBackend = AF_BACKEND_DEFAULT -- = 0,  ///< Default backend order: OpenCL -> CUDA -> CPU
               | AF_BACKEND_CPU     -- = 1,  ///< CPU a.k.a sequential algorithms
               | AF_BACKEND_CUDA    -- = 2,  ///< CUDA Compute Backend
               | AF_BACKEND_OPENCL  -- = 4   ///< OpenCL Compute Backend

%runElab derive "AFBackend" [Generic, Meta, Eq, Ord, Show]

public export
Cast AFBackend Int where
  cast AF_BACKEND_DEFAULT = 0
  cast AF_BACKEND_CPU = 1
  cast AF_BACKEND_CUDA = 2
  cast AF_BACKEND_OPENCL = 4

public export
Cast Int AFBackend where
  cast 1 = AF_BACKEND_CPU
  cast 2 = AF_BACKEND_CUDA
  cast 4 = AF_BACKEND_OPENCL
  cast _ = AF_BACKEND_DEFAULT

export %foreign libArrayFire "af_get_active_backend"
af_get_active_backend : (backend : Ptr AFBackend) -> PrimIO Int

export
afGetActiveBackend : HasIO io => io (Either AFErr AFBackend)
afGetActiveBackend = do
    ptr <- prim__castPtr {t=AFBackend} <$> malloc 8
    AF_SUCCESS <- cast <$> primIO (af_get_active_backend ptr)
      | err => pure (Left err)
    v <- peek {a=Int} (prim__castPtr (prim__forgetPtr ptr)) 0
    pure (Right (cast v))

export %foreign libArrayFire "af_get_backend_id"
af_get_backend_id : (backend : Ptr AFBackend) -> CAFArray -> PrimIO Int

export
afGetBackendId : HasIO io => AFArray dims dt -> io (Either AFErr AFBackend)
afGetBackendId (MkAFArray carr _ _ _) = do
    ptr <- prim__castPtr {t=AFBackend} <$> malloc 8
    AF_SUCCESS <- cast <$> primIO (af_get_backend_id ptr (derefCafArray carr))
      | err => pure (Left err)
    v <- peek {a=Int} (prim__castPtr (prim__forgetPtr ptr)) 0
    pure (Right (cast v))

export %foreign libArrayFire "af_set_backend"
af_set_backend : (backend : Int) -> PrimIO Int

export
afSetBackend : HasIO io => AFBackend -> io AFErr
afSetBackend be = cast <$> primIO (af_set_backend (cast be))

--------------------------------------------------

export %foreign libArrayFire "testo"
testo : PrimIO ()

export
{ty:_} -> {dims:_} -> FromDouble (AFArray dims ty) where
  fromDouble x = wrapAPIFunc "AFArrayNum" "fromDouble" $ afConstant _ _ (fromDouble x)

export
{ty:_} -> {dims:_} -> Num (AFArray dims ty) where
  x + y = wrapAPIFunc "AFArrayNum" "+" $ afAdd x y
  x * y = wrapAPIFunc "AFArrayNum" "*" $ afMul x y
  fromInteger x = wrapAPIFunc "AFArrayNum" "fromInteger" $ afConstant _ _ (cast $ Prelude.fromInteger x)

export
{ty:_} -> {dims:_} -> Neg (AFArray dims ty) where
  x - y = wrapAPIFunc "AFArrayNeg" "-" $ afSub x y
  negate x = wrapAPIFunc "AFArrayNeg" "negate" $ afSub 0 x -- todo use api method for this if there is one

export
{ty:_} -> {dims:_} -> Fractional (AFArray dims ty) where
  x / y = wrapAPIFunc "AFArrayFractional" "/" $ afDiv x y
  recip x = wrapAPIFunc "AFArrayFractional" "recip" $ afDiv 1 x -- todo use api method for this if there is one

export
{ty:_} -> {dims:_} -> Abs (AFArray dims ty) where
  abs x = wrapAPIFunc "AFArrayAbs" "abs" $ afAbs x

export
{ty:_} -> {dims:_} -> Floating (AFArray dims ty) where
  pi = wrapAPIFunc "AFArrayFloating" "pi" $ afConstant _ _ pi
  euler = wrapAPIFunc "AFArrayFloating" "euler" $ afConstant _ _ euler
  exp x = wrapAPIFunc "AFArrayFloating" "exp" $ afExp x
  log x = wrapAPIFunc "AFArrayFloating" "log" $ afLog x
  pow x y = wrapAPIFunc "AFArrayFloating" "pow" $ afPow x y
  sin x = wrapAPIFunc "AFArrayFloating" "sin" $ afSin x
  cos x = wrapAPIFunc "AFArrayFloating" "cos" $ afCos x
  tan x = wrapAPIFunc "AFArrayFloating" "tan" $ afTan x
  asin x = wrapAPIFunc "AFArrayFloating" "asin" $ afAsin x
  acos x = wrapAPIFunc "AFArrayFloating" "acos" $ afAcos x
  atan x = wrapAPIFunc "AFArrayFloating" "atan" $ afAtan x
  sinh x = wrapAPIFunc "AFArrayFloating" "sinh" $ afSinh x
  cosh x = wrapAPIFunc "AFArrayFloating" "cosh" $ afCosh x
  tanh x = wrapAPIFunc "AFArrayFloating" "tanh" $ afTanh x
  sqrt x = wrapAPIFunc "AFArrayFloating" "sqrt" $ afSqrt x

-- define Floating too and use those instances for math

{-
        array m = iota(dim4(4, 4));
        array v = constant(1, dim4(4));

        af_print(m);
        af_print(v);
        af_print(matmulTN(m, v));
-}

    -- AFAPI af_err af_matmul( af_array *out ,
    --                         const af_array lhs, const af_array rhs,
    --                         const af_mat_prop optLhs, const af_mat_prop optRhs);
export %foreign libArrayFire "af_matmul"
af_matmul : (new : GCPtr CAFArray) -> (lhs : CAFArray) -> (rhs : CAFArray) -> (optLhs : Int) -> (optRhs : Int) ->PrimIO Int

export -- just define the one we need for now
matVectMul : HasIO io => AFArray [x,y] dt -> AFArray [y] dt -> io (Either AFErr (AFArray [x] dt))
matVectMul (MkAFArray xptr _ (ex :: _) dt) (MkAFArray yptr _ _ _) = do
    new <- allocAF
    res <- primIO $ af_matmul new (derefCafArray xptr) (derefCafArray yptr) (cast AF_MAT_NONE) (cast AF_MAT_NONE)
    case cast res of
      AF_SUCCESS => pure $ Right $ MkAFArray new 1 [ex] dt
      err => pure (Left err)

infixr 9 #>

export
%inline
(#>) : AFArray [x,y] dt -> AFArray [y] dt -> AFArray [x] dt
x #> y = wrapAPIFunc "vectMult" "#>" $ matVectMul x y




export
test : IO ()
test = do
  seed <- cast {from=Int} {to=Bits64} <$> randomIO
  printLn seed
 -- rng seed defaults to 0 until it's set :(
  _ <- afSetSeed seed

  primIO $ testo
  afSetBackend AF_BACKEND_OPENCL >>= printLn
  -- Right arr1 <- afRandu F32 [10]
    -- | Left err => putStrLn $ "arr1: " ++ show err
  -- Right arr2 <- afRandu F32 [10]
    -- | Left err => putStrLn $ "arr2: " ++ show err
  -- Right arr3 <- afMul arr1 arr2
    -- | Left err => putStrLn $ "arr3: " ++ show err
  -- ignore $ afPrintArray arr1
  -- ignore $ afPrintArray arr2
  -- ignore $ afPrintArray arr3
  -- ignore $ afPrintArray $ randu F64 [10]
  -- ignore $ afPrintArray $ randu F64 [10]
  -- ignore $ afPrintArray $ randu F64 [10]
  -- Right d <- afDotAll arr1 arr2
  --   | Left err => putStrLn $ "d: " ++ show err
  -- printLn d
  -- Right arr4 <- afConstant F32 [2,10] 2.345
  --   | Left err => putStrLn $ "arr4: " ++ show err
  -- ignore $ afPrintArray arr4
  -- ignore $ afPrintArray $ arr3 + arr2
  -- ignore $ afPrintArray $ arr1 * arr2
  -- Right arr5 <- matVectMul (constant F64 [3,2] 2) (constant F64 [2] 5)
  --   | Left err => putStrLn $ "arr5: " ++ show err
  -- ignore $ afPrintArray $ arr5
  pure ()

-- todo remove me
main : IO ()
main = pure ()