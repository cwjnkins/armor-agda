module HelloWorld where

open import Data.Nat
open import IO

main = run (putStrLn "Hello, world!")
