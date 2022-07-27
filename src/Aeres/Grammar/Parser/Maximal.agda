{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser.Core
open import Aeres.Prelude
  renaming (Σ to Sigma)
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.Maximal
  (Σ : Set) where

open Aeres.Grammar.Definitions Σ
open Aeres.Grammar.Parser.Core Σ

module Generic (M : Set → Set) (Lift : (A : Set) (P : A → Set) → M A → Set) where
  GreatestSuccess : ∀ {A xs} → Success A xs → Set
  GreatestSuccess{A}{xs} s =
    ∀ pre' suf' → pre' ++ suf' ≡ xs → A pre'
    → length pre' ≤ Success.read s

  Maximal : ∀ {A} → Parser M A → Set
  Maximal{A} p = ∀ xs → Lift (Success A xs) GreatestSuccess (runParser p xs)

  record MaximalParser (@0 A : List Σ → Set) : Set where
    field
      parser : Parser M A
      max    : Maximal parser

module LogDec where
  Lift : (A : Set) (P : A → Set) → Logging (Dec A) → Set
  Lift A P (mkLogged _ (no  _)) = ⊤
  Lift A P (mkLogged _ (yes x)) = P x

  open Generic (Logging ∘ Dec) Lift public

  @0 nonnesting : ∀ {A} → NonNesting A → Parser (Logging ∘ Dec) A → MaximalParser A
  MaximalParser.parser (nonnesting nn p) = p
  MaximalParser.max (nonnesting{A} nn p) xs
    with runParser p xs
  ... | mkLogged log (no ¬p) = tt
  ... | (mkLogged log (yes p₁)) = help
    where
    help : (pre' suf' : List Σ) → pre' ++ suf' ≡ xs → A pre' → length pre' ≤ Success.read p₁
    help pre' suf' eq a =
      Lemmas.≡⇒≤
        (trans₀
          (‼ cong length
            (nn (trans eq (sym (Success.ps≡ p₁))) a (Success.value p₁)))
          (sym $ Success.read≡ p₁))

  parse&₁ : ∀ {@0 A B} → Parser (Logging ∘ Dec) A → NonNesting A → MaximalParser B → MaximalParser (&ₚ A B)
  runParser (Generic.MaximalParser.parser (parse&₁{B = B} p₁ nn p₂)) xs =
    case runParser p₁ xs of λ where
      (mkLogged l₁ (no ¬p)) →
        mkLogged l₁ (no λ where
          (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} v₁ v₂ refl) suffix ps≡) →
            contradiction (success bs₁ _ refl v₁ (bs₂ ++ suffix) (trans (sym $ ++-assoc bs₁ bs₂ suffix) ps≡)) ¬p)
      (mkLogged l₁ (yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁))) →
        case runParser (MaximalParser.parser{B} p₂) suf₁ of λ where
          (mkLogged log (no ¬p)) → {!!}
          (mkLogged log (yes p)) → {!!} 
  Generic.MaximalParser.max (parse&₁ p₁ nn p₂) = {!!}
