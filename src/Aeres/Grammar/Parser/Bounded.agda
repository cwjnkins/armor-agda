{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Grammar.Parser.Bounded (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Parser.Core Σ

ExactLengthParser : (M : Set → Set) (A : List Σ → Set) → Set
ExactLengthParser M A = ∀ n → Parser M (ExactLength A n)

parseN : {M : Set → Set} ⦃ _ : Monad M ⦄ →
         (n : ℕ) → M (Level.Lift _ ⊤) → Parser (M ∘ Dec) (ExactLength Singleton n)
runParser (parseN zero _) xs =
  return (yes (success [] _ refl (mk×ₚ (singleton [] refl) (─ refl) refl) xs refl))
runParser (parseN (suc n) m) [] = do
  m
  return ∘ no $ λ where
    (success .bs read read≡ (mk×ₚ (singleton bs refl) (─ bsLen) refl) suffix ps≡) → ‼
      (0≢1+n $ begin
        length{A = Σ} [] ≡⟨ cong length (sym (‼ ps≡)) ⟩
        length (bs ++ suffix) ≡⟨ length-++ bs ⟩
        length bs + length suffix ≡⟨ cong (_+ length suffix) bsLen ⟩
        suc n + length suffix ∎)
  where open ≡-Reasoning
runParser (parseN (suc n) m) (x ∷ xs) = do
  yes (success .bs r₀ r₀≡ (mk×ₚ (singleton bs refl) (─ bsLen) refl) suf₀ ps≡₀) ←
    runParser (parseN n m) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success .(x ∷ bs) read read≡ (mk×ₚ (singleton (x ∷ bs) refl) (─ bsLen) refl) suffix ps≡) →
          contradiction
            (success bs _ refl (mk×ₚ (singleton bs refl) (─ cong pred bsLen) refl) suffix (∷-injectiveʳ ps≡))
            ¬parse
  return (yes
    (success _ _ (cong suc r₀≡) (mk×ₚ (singleton (x ∷ bs) refl) (─ cong suc bsLen) refl) suf₀ (cong (x ∷_) ps≡₀)))

parseLit : {M : Set → Set} ⦃ _ : Monad M ⦄ ⦃ _ : Eq Σ ⦄ → (underflow mismatch : M (Level.Lift _ ⊤))
           → (lit : List Σ) → Parser (M ∘ Dec) (_≡ lit)
runParser (parseLit underflow mismatch []) xs = return (yes (success [] 0 refl refl xs refl))
runParser (parseLit underflow mismatch (l ∷ lit)) [] = do
  underflow
  return ∘ no $ λ where
    (success .(l ∷ lit) read read≡ refl suffix ())
runParser (parseLit underflow mismatch (l ∷ lit)) (x ∷ xs)
  with x ≟ l
... | no ¬x≡l = do
  mismatch
  return ∘ no $ λ where
    (success .(l ∷ lit) read read≡ refl suffix ps≡) →
      contradiction (sym (∷-injectiveˡ ps≡)) ¬x≡l
... | yes refl = do
  yes (success pre₀ _ r₀≡ refl suf₀ refl) ← runParser (parseLit underflow mismatch lit) xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success .(l ∷ lit) read read≡ refl suffix ps≡) →
          contradiction (success lit _ (cong pred read≡) refl suffix (∷-injectiveʳ ps≡)) ¬parse
  return (yes (success (l ∷ pre₀) _ (cong suc r₀≡) refl suf₀ refl))

parseExactLength : {M : Set → Set} ⦃ _ : Monad M ⦄ →
                   {A : List Σ → Set} → (@0 _ : NonNesting A) →
                   M (Level.Lift _ ⊤) →
                   Parser (M ∘ Dec) A →
                   ∀ n → Parser (M ∘ Dec) (ExactLength A n)
runParser (parseExactLength nn m p n) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v vLen refl) suffix ps≡) →
          contradiction
            (success prefix _ read≡ v suffix ps≡)
            ¬parse
  case r₀ ≟ n of λ where
    (no  r₀≢) → do
      m
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v (─ vLen) refl) suffix ps≡) → ‼
          let @0 pre₀≡ : pre₀ ≡ prefix
              pre₀≡ = nn (trans ps≡₀ (sym ps≡)) v₀ v
          in
          contradiction
            (begin (r₀           ≡⟨ r₀≡ ⟩
                   length pre₀   ≡⟨ cong length pre₀≡ ⟩
                   length prefix ≡⟨ vLen ⟩
                   n ∎))
            r₀≢
    (yes refl) →
      return (yes (success pre₀ _ r₀≡ (mk×ₚ v₀ (─ sym r₀≡) refl) suf₀ ps≡₀))
  where open ≡-Reasoning

parse≤ : ∀ {A} {M : Set → Set} ⦃ _ : Monad M ⦄ (n : ℕ) →
  Parser (M ∘ Dec) A → (@0 _ : NonNesting A) → M (Level.Lift _ ⊤) →
  Parser (M ∘ Dec) (WithinLength A n)
runParser (parse≤{A} n p nn m) xs = do
  (yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀)) ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v _ refl) suffix ps≡) →
          contradiction (success prefix _ read≡ v suffix ps≡) ¬parse
  case r₀ ≤? n of λ where
    (no  r₀≰n) → do
      m
      return ∘ no $ λ where
        (success prefix r r≡ (mk×ₚ v (─ r≤n) refl) suffix ps≡) →
          contradiction
            (begin (r₀           ≡⟨ r₀≡ ⟩
                   length pre₀   ≡⟨ cong length (nn (trans ps≡₀ (sym ps≡)) v₀ v) ⟩
                   length prefix ≤⟨ r≤n ⟩
                   n ∎))
            r₀≰n
    (yes r₀≤n) →
      return (yes (success pre₀ _ r₀≡ (mk×ₚ v₀ (─ subst₀ (λ i → i ≤ n) r₀≡ r₀≤n) refl) suf₀ ps≡₀))
  where open ≤-Reasoning
