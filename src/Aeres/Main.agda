{-# OPTIONS --subtyping --guardedness #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Cert
open import Aeres.Grammar.Parser
import      Aeres.IO
open import Aeres.Prelude
import      IO

module Aeres.Main where

open Base256

usage : String
usage = "usage: 'aeres [CERT]'"

-- str2dig : String → Maybe (List Dig)
-- str2dig xs = do
--   bs ← decToMaybe ∘ All.all? (_<? 256) ∘ map toℕ ∘ String.toList $ xs
--   return (map (λ where (n , n<256) → Fin.fromℕ< n<256) (All.toList bs))

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
    case Decode.base64 (String.toList bs) of λ where
      nothing   → Aeres.IO.putStrLnErr "invalid char range in input"
      (just bs) → case runParser parseCert bs of λ where
        (mkLogged log (yes _)) → Aeres.IO.exitSuccess
        (mkLogged log (no  _)) →
          Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
          Aeres.IO.exitFailure

