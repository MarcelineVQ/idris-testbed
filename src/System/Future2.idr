module System.Future2


import System.Future

Foldable Future where
  foldr f acc fut = ?holeFoldableFoldr

Traversable Future where
  traverse = ?holeTraverse

-- withFuture 