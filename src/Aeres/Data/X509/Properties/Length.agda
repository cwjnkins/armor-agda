{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Length where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 minrepUnique : ∀ {lₕ lₜ} → Unique (Length.MinRep lₕ lₜ)
minrepUnique{lₕ}{[]} p₁ p₂ = ≤-irrelevant p₁ p₂
minrepUnique {lₕ} {x ∷ lₜ} tt tt = refl

@0 unambiguous : Unambiguous Length
unambiguous (Length.short (Length.mkShort l l<128 refl)) (Length.short (Length.mkShort .l l<129 refl)) =
  case ≤-irrelevant l<128 l<129 of λ where
    refl → refl
unambiguous (Length.short (Length.mkShort l l<128 refl)) (Length.long (Length.mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep ()))
unambiguous (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.short (Length.mkShort l₁ l<128 ()))
unambiguous (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.long (Length.mkLong .l l>129 .lₕ lₕ≢1 .lₜ lₜLen₁ lₕₜMinRep₁ refl)) =
  case _ × _ × _ × _ ∋ ≤-irrelevant l>128 l>129 , ≤-irrelevant lₕ≢0 lₕ≢1 , ≡-unique lₜLen lₜLen₁ , minrepUnique lₕₜMinRep lₕₜMinRep₁ of λ where
    (refl , refl , refl , refl) → refl

@0 unambiguous-getLength : ∀ {xs ys} → xs ≡ ys → (l₁ : Length xs) (l₂ : Length ys) → getLength l₁ ≡ getLength l₂
unambiguous-getLength refl l₁ l₂ = cong getLength (unambiguous l₁ l₂)

@0 nonnesting : NonNesting Length
nonnesting xs₁++ys₁≡xs₂++ys₂ (Length.short (Length.mkShort l l<128 refl)) (Length.short (Length.mkShort l₁ l<129 refl)) =
  cong [_] (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂)
nonnesting xs₁++ys₁≡xs₂++ys₂ (Length.short (Length.mkShort l l<128 refl)) (Length.long (Length.mkLong l₁ l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i) (sym $ ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nonnesting xs₁++ys₁≡xs₂++ys₂ (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.short (Length.mkShort l₁ l<128 refl)) =
  contradiction l<128 (<⇒≯ (subst (λ i → 128 < toℕ i)  (∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂) l>128))
nonnesting xs₁++ys₁≡xs₂++ys₂ (Length.long (Length.mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRep refl)) (Length.long (Length.mkLong l₁ l>129 lₕ₁ lₕ≢1 lₜ₁ lₜLen₁ lₕₜMinRep₁ refl)) =
  begin (l ∷ lₕ ∷ lₜ   ≡⟨ cong (_∷ lₕ ∷ lₜ) (‼ l≡) ⟩
        l₁ ∷ lₕ ∷ lₜ   ≡⟨ cong (λ x → l₁ ∷ x ∷ lₜ) (‼ lₕ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ  ≡⟨ cong (λ x → l₁ ∷ lₕ₁ ∷ x) (‼ lₜ≡) ⟩
        l₁ ∷ lₕ₁ ∷ lₜ₁ ∎)
  where
  open ≡-Reasoning

  @0 l≡ : l ≡ l₁
  l≡ = ∷-injectiveˡ xs₁++ys₁≡xs₂++ys₂

  @0 lₕ≡ : lₕ ≡ lₕ₁
  lₕ≡ = ∷-injectiveˡ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ++ys₁≡ : lₜ ++ _ ≡ lₜ₁ ++ _
  lₜ++ys₁≡ = ∷-injectiveʳ (∷-injectiveʳ xs₁++ys₁≡xs₂++ys₂)

  @0 lₜ≡ : lₜ ≡ lₜ₁
  lₜ≡ =
    proj₁ $ Lemmas.length-++-≡ _ _ _ _ lₜ++ys₁≡
              (trans lₜLen (trans (cong (λ x → toℕ x ∸ 129) l≡) (sym lₜLen₁)))
