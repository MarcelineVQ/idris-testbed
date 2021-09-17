module System.Random.PRNG.Keys

import System.Random.PRNG.Keys.Keys1
import System.Random.PRNG.Keys.Keys2
import System.Random.PRNG.Keys.Keys3

-- use lazylist?
keys : List Bits64
keys = keys1 ++ keys2 ++ keys3
