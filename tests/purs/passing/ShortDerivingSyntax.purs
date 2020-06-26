module Main where

import Prelude
import Effect.Console (log)

data D = D
  derive (Eq, Ord)

instance Show D where
  show D = "D"

newtype N = N D
  derive (Eq, Ord)
  derive newtype Show

newtype F a = F a
  derive Functor

main = log "Done"
