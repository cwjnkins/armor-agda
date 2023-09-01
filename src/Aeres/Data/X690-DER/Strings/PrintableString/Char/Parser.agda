{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Strings.PrintableString.Char.Properties
open import Aeres.Data.X690-DER.Strings.PrintableString.Char.TCB
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.Tag
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X690-DER.Strings.PrintableString.Char.Parser where

open Aeres.Grammar.Parser UInt8

private
  here' = "X690-DER: Strings: PrintableString: Char: parseChar:"

parse : Parser (Logging ∘ Dec) PrintableStringChar
runParser parse [] = do
  tell $ here' String.++ " underflow"
  return ∘ no $ λ where
    (success prefix read read≡ value suffix ps≡) →
      contradiction{P = prefix ≡ []} (++-conicalˡ _ _ ps≡) (nonempty value)
runParser parse (x ∷ xs) =
  case printableStringChar? x of λ where
    (no ¬p) → do
      tell $ here' String.++ " invalid char: " String.++ (show ∘ toℕ $ x)
      return ∘ no $ λ where
        (success prefix read read≡ (mkPrintableStringChar c range refl) suffix ps≡) → ‼
            (case (‼ ps≡) of λ where
              refl → contradiction range ¬p)
    (yes p) →
      return (yes (success [ x ] _ refl (mkPrintableStringChar x p refl) _ refl))
