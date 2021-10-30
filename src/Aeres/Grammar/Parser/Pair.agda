{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser.Pair (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Parser.Core Σ

parse& : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : List Σ → Set}
         → (@0 _ : NonNesting A)
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
  where open ≡-Reasoning

