module System.Random.Types

import Data.Bits
import System.Random

-------------------------------------------------
-- Taken directly from System.Random since it doesn't re-export them

-- %foreign "scheme:blodwen-random"
--          "javascript:lambda:(max)=>Math.floor(Math.random() * max)"
-- prim__randomBits32 : Bits32 -> PrimIO Bits32

-- randomBits32' : Bits32 -> IO Bits32
-- randomBits32' upperBound = fromPrim (prim__randomBits32 upperBound)

----
-- Somehow the above is being re-exported anyway?
----

%foreign "scheme:blodwen-random"
         "javascript:lambda:()=>Math.random()"
prim__randomBits64 : Bits64 -> PrimIO Bits64

randomBits32' : HasIO io => Bits32 -> io Bits32
randomBits32' upperBound = liftIO $ randomBits32 upperBound

-------------------------------------------------

public export
Random Int64 where
  randomIO = map cast . liftIO $ fromPrim (prim__randomBits64 0xffffffffffffffff)
  randomRIO (lo',hi') = do let (lo,hi) = (cast lo', cast hi')
                           r <- liftIO $ fromPrim $ prim__randomBits64 (hi - lo + 1)
                           pure $ cast r + lo'

public export
Random Int where
  randomIO = cast <$> randomIO {a=Int64}
  randomRIO range = cast <$> randomRIO {a=Int64} (bimap cast cast range)

public export
Random Bits32 where
  randomIO = map cast . liftIO $ fromPrim (prim__randomBits32 0xffffffff)
  randomRIO (lo',hi') = do let (lo,hi) = (cast lo', cast hi')
                           r <- liftIO $ fromPrim $ prim__randomBits32 (hi - lo + 1)
                           pure $ cast r + lo'

public export
Random Bits64 where
  randomIO = map cast . liftIO $ fromPrim (prim__randomBits64 0xffffffffffffffff)
  randomRIO (lo',hi') = do let (lo,hi) = (cast lo', cast hi')
                           r <- liftIO $ fromPrim $ prim__randomBits64 (hi - lo + 1)
                           pure $ cast r + lo'
