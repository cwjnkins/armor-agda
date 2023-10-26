{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq.Properties
import      Aeres.Grammar.Seq.TCB
import      Aeres.Grammar.Option.Properties
import      Aeres.Grammar.Option.TCB
import      Aeres.Grammar.Parser
open import Aeres.Prelude
open import Tactic.MonoidSolver
  using (solve ; solve-macro)

module Aeres.Grammar.Seq.Parser (Σ : Set) where

open Aeres.Grammar.Definitions    Σ
open Aeres.Grammar.Option.TCB     Σ
  hiding (module Option)
private
  module Option where
    open Aeres.Grammar.Option.Properties Σ
open Aeres.Grammar.Parser         Σ
open Aeres.Grammar.Seq.Properties Σ
open Aeres.Grammar.Seq.TCB        Σ

open ≡-Reasoning

parse& : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : List Σ → Set}
         → (@0 _ : NoSubstrings A)
         → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
         → Parser (M ∘ Dec) (&ₚ A B)
runParser (parse& nn p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) →
          contradiction
            (success bs₁ _ refl fstₚ (bs₂ ++ suffix)
              (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                     (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                     xs ∎))
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p₂ suf₀
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) → ‼
          let @0 xs≡ : bs₁ ++ bs₂ ++ suffix      ≡ pre₀ ++ suf₀
              xs≡ = begin bs₁ ++ bs₂ ++ suffix   ≡⟨ solve (++-monoid Σ) ⟩
                          (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                          xs                     ≡⟨ sym ps≡₀ ⟩
                          pre₀ ++ suf₀           ∎

              @0 bs₁≡ : bs₁ ≡ pre₀
              bs₁≡ = nn xs≡ fstₚ v₀
          in
          contradiction
            (success bs₂ _ refl sndₚ suffix
              (++-cancelˡ pre₀ (trans (cong (_++ bs₂ ++ suffix) (sym bs₁≡)) xs≡)))
            ¬parse
  return (yes
    (success (pre₀ ++ pre₁) (r₀ + r₁)
      (begin r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
             length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
             length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
             length (pre₀ ++ pre₁) ∎)
      (mk&ₚ v₀ v₁ refl) suf₁
      (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
             pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
             pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
             xs ∎)))

parse&ᵈ : {M : Set → Set} ⦃ _ : Monad M ⦄
          → {@0 A : List Σ → Set} {@0 B : {@0 bs : List Σ} → A bs → List Σ → Set}
          → (@0 _ : NoSubstrings A) (@0 _ : Unambiguous A)
          → Parser (M ∘ Dec) A
          → (∀ {@0 bs} → Singleton (length bs) → (a : A bs) → Parser (M ∘ Dec) (B a))
          → Parser (M ∘ Dec) (&ₚᵈ A B)
runParser (parse&ᵈ{A = A}{B} nn ua p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser{A = A} p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) →
          contradiction
            (success bs₁ _ refl fstₚ (bs₂ ++ suffix)
              (begin bs₁ ++ bs₂ ++ suffix ≡⟨ solve (++-monoid Σ) ⟩
                     (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                     xs ∎))
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser (p₂ (singleton r₀ r₀≡) v₀) suf₀
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk&ₚ{bs₁}{bs₂} fstₚ sndₚ refl) suffix ps≡) → ‼
          let @0 xs≡ : bs₁ ++ bs₂ ++ suffix      ≡ pre₀ ++ suf₀
              xs≡ = begin bs₁ ++ bs₂ ++ suffix   ≡⟨ solve (++-monoid Σ) ⟩
                          (bs₁ ++ bs₂) ++ suffix ≡⟨ ps≡ ⟩
                          xs                     ≡⟨ sym ps≡₀ ⟩
                          pre₀ ++ suf₀           ∎

              @0 bs₁≡ : bs₁ ≡ pre₀
              bs₁≡ = nn xs≡ fstₚ v₀

              @0 fstₚ≡ : subst A bs₁≡ fstₚ ≡ v₀
              fstₚ≡ =
                ≡-elim (λ {bs} eq → ∀ v₀ → subst A eq fstₚ ≡ v₀)
                  (ua fstₚ) bs₁≡ v₀
          in
          contradiction
            (success bs₂ _ refl
              (subst (λ x → B x bs₂) fstₚ≡
                (≡-elim (λ {pre₀} eq → B (subst A eq fstₚ) bs₂)
                  sndₚ bs₁≡))
              suffix
              (++-cancelˡ pre₀ (trans (cong (_++ bs₂ ++ suffix) (sym bs₁≡)) xs≡)))
            ¬parse
  return (yes
    (success (pre₀ ++ pre₁) (r₀ + r₁)
      (begin r₀ + r₁ ≡⟨ cong (_+ r₁) r₀≡ ⟩
             length pre₀ + r₁ ≡⟨ cong (length pre₀ +_) r₁≡ ⟩
             length pre₀ + length pre₁ ≡⟨ (sym $ length-++ pre₀) ⟩
             length (pre₀ ++ pre₁) ∎)
      (mk&ₚ v₀ v₁ refl) suf₁
      (begin (pre₀ ++ pre₁) ++ suf₁ ≡⟨ solve (++-monoid Σ) ⟩
             pre₀ ++ pre₁ ++ suf₁ ≡⟨ cong (pre₀ ++_) ps≡₁ ⟩
             pre₀ ++ suf₀ ≡⟨ ps≡₀ ⟩
             xs ∎)))

parseOption₁
  : ∀ {A B} → String → @0 NoSubstrings A 
    → Parser (Logging ∘ Dec) A → Parser (Logging ∘ Dec) B
    → Parser (Logging ∘ Dec) (&ₚ (Option A) B)
runParser (parseOption₁ loc ns₁ p₁ p₂) xs = do
  tell $ loc String.++ ": parseOption₁ (present)"
  (no ¬p₁₂) ← runParser (parse& ns₁ p₁ p₂) xs
    where (yes (success pre r r≡ (mk&ₚ v₁ v₂ bs≡) suf ps≡)) → do
      return (yes (success pre r r≡ (mk&ₚ (some v₁) v₂ bs≡) suf ps≡))
  tell $ loc String.++ ": parseOption₁ (absent)"
  (no ¬p₂) ← runParser p₂ xs
    where (yes (success pre r r≡ v₂ suf ps≡)) → do
      return (yes (success pre r r≡ (mk&ₚ none v₂ refl) suf ps≡))
  return ∘ no $ λ where
    (success prefix read read≡ (mk&ₚ none v₂ refl) suffix ps≡) →
      contradiction
        (success prefix read read≡ v₂ suffix ps≡)
        ¬p₂
    (success prefix read read≡ (mk&ₚ{pre₁}{pre₂} (some v₁) v₂ refl) suffix ps≡) →
      contradiction
        (success prefix read read≡ (mk&ₚ v₁ v₂ refl) suffix ps≡)
        ¬p₁₂
