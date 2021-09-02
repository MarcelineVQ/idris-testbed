module Net.SQL

import Net.FFNN

import JSON

import Data.Strong.IOArray
import Data.Strong.IOMatrix

import Net.Types

import Generics.Derive
%language ElabReflection

-- honestly, let's just use JSON!

-- an array of arrays should do fine for matrix representation



-- convert nets to sql
weightsToSQL : Weights i o -> String
weightsToSQL (MkWeights wBias wNodes) = ?asDsfsdf --"W" ++ toList wBias ++ toList wNodes

-- 
networkToSQL : Network i hs o -> String
networkToSQL (O x) = ?dsfe_1
networkToSQL (L x y) = ?dsfe_2

-- L W [1,2,3] [[4,5,6],[10,11,12]] O [9,0]

genomeToSQL : Genome i o -> String
