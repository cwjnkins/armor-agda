{-# OPTIONS --subtyping #-}

import      Aeres.Data.Base64.Parser
import      Aeres.Data.Base64.Properties
import      Aeres.Data.Base64.TCB
open import Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.Base64 where

open Aeres.Data.Base64.Parser       public
module Base64 where
  open Aeres.Data.Base64.Properties public
    renaming ( module Base64Char to Char
             ; module Base64Pad  to Pad
             ; module Base64Str  to Str)
open Aeres.Data.Base64.TCB          public

base64Char? : Decidable Base64Char
base64Char? xs =
  let (mkLogged _ v₂) = runParser parseBase64Char xs
  in
  case v₂ of λ where
    (no ¬p) → no (λ x → contradiction (success xs _ refl x [] (++-identityʳ _)) ¬p)
    (yes (success prefix read read≡ value [] ps≡)) →
      yes (subst₀ Base64Char (trans (sym $ ++-identityʳ _) ps≡) value)
    (yes (success prefix read read≡ (mk64 c' c'∈ i' refl) suffix@(c“ ∷ s') ps≡)) →
      no λ where
        (mk64 c c∈ i bs≡) →
          contradiction {P = [ c ] ≡ c' ∷ c“ ∷ s'}
            (begin ([ c ] ≡⟨ sym bs≡ ⟩
                   xs ≡⟨ sym ps≡ ⟩
                   c' ∷ suffix ∎))
            (λ ())
  where
  open ≡-Reasoning
