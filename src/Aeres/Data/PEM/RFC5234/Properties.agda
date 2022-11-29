{-# OPTIONS --subtyping #-}


open import Aeres.Binary
  renaming (module Base64 to B64)
open import Aeres.Data.Base64
open import Aeres.Data.PEM.RFC5234.TCB
  hiding (module EOL)
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Relation.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

module Aeres.Data.PEM.RFC5234.Properties where

open Aeres.Grammar.Definitions          Char
open Aeres.Grammar.Relation.Definitions Char
open Aeres.Grammar.Sum                  Char

module EOL where
  Rep =  Sum (_≡ '\r' ∷ [ '\n' ])
        (Sum (_≡ [ '\r' ])
             (_≡ [ '\n' ]))

  char₁ : ∀ {@0 b bs} → EOL (b ∷ bs) → b ≡ '\r' ⊎ b ≡ '\n'
  char₁ crlf = inj₁ refl
  char₁ cr = inj₁ refl
  char₁ lf = inj₂ refl

  equiv : Equivalent Rep EOL
  proj₁ equiv (Sum.inj₁ refl) = crlf
  proj₁ equiv (Sum.inj₂ (Sum.inj₁ refl)) = cr
  proj₁ equiv (Sum.inj₂ (Sum.inj₂ refl)) = lf
  proj₂ equiv crlf = Sum.inj₁ refl
  proj₂ equiv cr = Sum.inj₂ (Sum.inj₁ refl)
  proj₂ equiv lf = Sum.inj₂ (Sum.inj₂ refl)

  @0 eolLen : ∀ {@0 bs} → EOL bs → InRange 1 2 (length bs)
  eolLen crlf = toWitness{Q = inRange? 1 2 2} tt
  eolLen cr = toWitness{Q = inRange? 1 2 1} tt
  eolLen lf = toWitness{Q = inRange? 1 2 1} tt

  noOverlap : NoOverlap Base64Str EOL
  noOverlap ws [] ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ str₁ str₂ =
    inj₁ refl
  noOverlap ws xs₁@(x₁' ∷ xs₁') ys₁ xs₂ ys₂ xs₁++ys₁≡xs₂++ys₂ str₁ str₂ =
    inj₂ absurd
    where
    xs₂≡ : EOL xs₂ → Σ[ p ∈ (Char × List Char) ] uncurry _∷_ p ≡ xs₂
    xs₂≡ crlf = -, refl
    xs₂≡ cr = -, refl
    xs₂≡ lf = -, refl
  
    module _ (e : EOL xs₂) where

      x₂' : Char
      x₂' = proj₁ (proj₁ (xs₂≡ e))

      xs₂' : List Char
      xs₂' = proj₂ (proj₁ (xs₂≡ e))

      e' : EOL (x₂' ∷ xs₂')
      e' = subst₀ EOL (sym ∘ proj₂ ∘ xs₂≡ $ e) e

      e“ : EOL (x₁' ∷ xs₂')
      e“ = subst₀ (λ x → EOL (x ∷ xs₂'))
             (∷-injectiveˡ
               (trans
                 (cong (_++ ys₂) ((proj₂ ∘ xs₂≡ $ e)))
                 (sym xs₁++ys₁≡xs₂++ys₂)))
             e'

      x₁'∈ : x₁' ∈ B64.charset ⊎ x₁' ≡ '='
      x₁'∈ = Base64.Str.char∈ (Any.++⁺ʳ ws (here refl)) str₁

      absurd : ⊥
      absurd =
        contradiction{P = x₁' ≡ '\r' ⊎ x₁' ≡ '\n'}
          (char₁ e“)
          λ where
            (inj₁ refl) →
              contradiction₂ x₁'∈ (toWitnessFalse{Q = _ ∈? _} tt) λ ()
            (inj₂ refl) → contradiction₂ x₁'∈ (toWitnessFalse{Q = _ ∈? _} tt) (λ ())
