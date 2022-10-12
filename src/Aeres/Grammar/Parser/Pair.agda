{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Grammar.Parser.Pair (Σ : Set) where

open import Aeres.Grammar.Definitions Σ
open import Aeres.Grammar.Parser.Core Σ

open ≡-Reasoning

parse×Singleton
  : {M : Set → Set} ⦃ _ : Monad M ⦄ {@0 A : List Σ → Set}
    → Parser (M ∘ Dec) A
    → Parser (M ∘ Dec) (A ×ₚ Singleton)
runParser (parse×Singleton p) xs = do
  yes (success pre r r≡ v suf ps≡) ← runParser p xs
    where no ¬p → return ∘ no $ λ where
      (success pre r r≡ (mk×ₚ v _ refl) suf ps≡) →
        contradiction (success pre _ r≡ v suf ps≡) ¬p
  return (yes (success
    pre r r≡
      (mk×ₚ v
        (singleton (take r xs)
          (begin take r xs ≡⟨ cong (take r) (sym ps≡) ⟩
                 take r (pre ++ suf) ≡⟨ cong (λ x → take x (pre ++ suf)) r≡ ⟩
                 take (length pre) (pre ++ suf) ≡⟨ Lemmas.take-length-++ pre suf ⟩
                 pre ∎))
        refl)
      suf ps≡))

parse×Dec : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : List Σ → Set}
            → @0 NonNesting A
            → (decNo : M (Level.Lift _ ⊤))
            → Parser (M ∘ Dec) A → Decidable B
            → Parser (M ∘ Dec) (A ×ₚ B)
runParser (parse×Dec{M}{A = A}{B} nn₁ decNo p b?) xs = do
  yes x ← runParser p xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ value _ refl) suffix ps≡) →
          contradiction (success prefix _ read≡ value suffix ps≡) ¬parse
  check x
  where
  check : Success A xs → M (Dec (Success (A ×ₚ B) xs))
  check (success prefix read read≡ value suffix ps≡) =
    case v₁ ret _ of λ where
      (no ¬b) → do
        decNo
        return ∘ no $ λ where
          (success prefix' read' read≡' (mk×ₚ v₀' b' refl) suffix' ps≡') → ‼
            let @0 prefix≡ : prefix ≡ prefix'
                prefix≡ = nn₁ (trans₀ ps≡ (sym ps≡')) value v₀'
            in
            contradiction (subst₀ B (sym prefix≡) b') ¬b
      (yes b) → return (yes (success _ _ read≡ (mk×ₚ value b refl) suffix ps≡))
    where
    v₁ : Dec (B prefix)
    v₁ = subst₀ (Dec ∘ B) (take read xs ≡ prefix ∋ trans₀ (cong₂ take read≡ (sym ps≡)) (Lemmas.take-length-++ prefix suffix)) (b? (take read xs))

  -- case b? (take r₀ xs) of λ where
  --   x → {!!}

parse× : {M : Set → Set} ⦃ _ : Monad M ⦄ {A B : List Σ → Set}
         → @0 NonNesting A → @0 NonNesting B
         → (mismatch : M (Level.Lift _ ⊤))
         → Parser (M ∘ Dec) A → Parser (M ∘ Dec) B
         → Parser (M ∘ Dec) (A ×ₚ B)
runParser (parse×{B = B} nn₁ nn₂ m p₁ p₂) xs = do
  yes (success pre₀ r₀ r₀≡ v₀ suf₀ ps≡₀) ← runParser p₁ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' refl) suffix ps≡) →
          contradiction
            (success _ _ read≡ v₀' _ ps≡)
            ¬parse
  yes (success pre₁ r₁ r₁≡ v₁ suf₁ ps≡₁) ← runParser p₂ xs
    where no ¬parse → do
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' refl) suffix ps≡) →
          contradiction
            (success _ _ read≡ v₁' _ ps≡)
            ¬parse
  case r₀ ≟ r₁ of λ where
    (no  r₀≢r₁) → do
      m
      return ∘ no $ λ where
        (success prefix read read≡ (mk×ₚ v₀' v₁' refl) suffix ps≡) → ‼
          contradiction
            (begin (r₀ ≡⟨ r₀≡ ⟩
                   length pre₀ ≡⟨ cong length (nn₁ (trans₀ ps≡₀ (sym ps≡)) v₀ v₀') ⟩
                   length prefix ≡⟨ cong length (nn₂ (trans₀ ps≡ (sym ps≡₁)) v₁' v₁) ⟩
                   length pre₁ ≡⟨ sym r₁≡ ⟩
                   r₁ ∎))
            r₀≢r₁
    (yes refl) →
      return (yes
        (success pre₀ r₀ r₀≡ (mk×ₚ v₀ (subst₀ B (proj₁ (Lemmas.length-++-≡ _ _ _ _ (trans ps≡₁ (sym ps≡₀)) (trans (sym r₁≡) r₀≡))) v₁) refl) suf₀ ps≡₀))


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

parse&ᵈ : {M : Set → Set} ⦃ _ : Monad M ⦄
          → {@0 A : List Σ → Set} {@0 B : (@0 bs : List Σ) → A bs → List Σ → Set}
          → (@0 _ : NonNesting A) (@0 _ : Unambiguous A)
          → Parser (M ∘ Dec) A
          → (∀ {@0 bs} → Singleton (length bs) → (a : A bs) → Parser (M ∘ Dec) (B bs a))
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
              (subst (λ x → B pre₀ x bs₂) fstₚ≡
                (≡-elim (λ {pre₀} eq → B pre₀ (subst A eq fstₚ) bs₂)
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

