{-# OPTIONS --subtyping --guardedness #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
open import Aeres.Grammar.Parser
import      Aeres.IO
open import Aeres.Prelude
open import Aeres.Prelude
import      IO

module Aeres.Main where

open Base256

usage : String
usage = "usage: 'aeres [CERT]'"

-- ref : https://stackoverflow.com/questions/11763639/agda-parse-a-string-with-numbers
isDigit : Char → Maybe Dig
isDigit '0' = just (# 0)
isDigit '1' = just (# 1)
isDigit '2' = just (# 2)
isDigit '3' = just (# 3)
isDigit '4' = just (# 4)
isDigit '5' = just (# 5)
isDigit '6' = just (# 6)
isDigit '7' = just (# 7)
isDigit '8' = just (# 8)
isDigit '9' = just (# 9)
isDigit _   = nothing

attach : Maybe Dig → Dig → Maybe Dig
attach nothing  n = just n
attach (just m) n
  with (10 * (toℕ m) + (toℕ n))
... | eqn
  with eqn <? 256
... | no ¬p = nothing
... | yes p = just (Fin.fromℕ< p)

Quote : List Char → Maybe (List Dig)
Quote xs = parse xs nothing []
  where
    parse : List Char → Maybe Dig → List Dig → Maybe (List Dig)
    parse []         nothing  ns = just ns
    parse []         (just n) ns = just (n ∷ ns)
    parse (' ' ∷ tl) (just n) ns = parse tl nothing (n ∷ ns)
    parse (hd ∷ tl)  m        ns with isDigit hd
    ... | nothing = nothing
    ... | just n  = parse tl (attach m n) ns

stringListToDig : String → Maybe (List Dig)
stringListToDig xs with Quote (String.toList xs)
... | nothing = nothing
... | just ns = just (reverse ns)

str2dig : String → Maybe (List Dig)
str2dig xs = do
  bs ← decToMaybe ∘ All.all? (_<? 256) ∘ map toℕ ∘ String.toList $ xs
  return (map (λ where (n , n<256) → Fin.fromℕ< n<256) (All.toList bs))

-- TODO: bindings for returning error codes?
main : IO.Main
main = IO.run $
  Aeres.IO.getArgs IO.>>= λ args →
  case (head args) of λ where
    nothing →
      IO.getLine IO.>>= λ str →
      runParserIO str
    (just str) → runParserIO str
  where
  runParserIO : String → IO.IO _
  runParserIO bs =
    case stringListToDig bs of λ where
      nothing   → Aeres.IO.putStrLnErr "invalid char range in input"
      (just bs) → case runParser parseCert bs of λ where
        (mkLogged log (yes _)) → Aeres.IO.exitSuccess
        (mkLogged log (no  _)) →
          Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
          Aeres.IO.exitFailure

