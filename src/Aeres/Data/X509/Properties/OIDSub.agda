{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.OIDSub where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.OIDSub
nonempty (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
nonempty (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

postulate
  nonnesting : NonNesting Generic.OIDSub
-- nonnesting {_} {ys₁} {_} {ys₂} x (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs refl) (Generic.mkOIDSub [] lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ refl)
--   = proj₁ (Lemmas.length-++-≡ _ ys₁ _ ys₂ x refl)
-- nonnesting {_} {ys₁} {_} {ys₂} x (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs refl) (Generic.mkOIDSub (x₁ ∷ lₚ₁) (px All.∷ lₚ≥129) lₑ₁ lₑ<129 leastDigs₁ refl)
--   = contradiction (begin 128 ≤⟨ px ⟩
--                   toℕ x₁ ≡⟨ cong toℕ (sym (∷-injectiveˡ x)) ⟩ toℕ lₑ ∎) (<⇒≱ lₑ<128)
--   where open ≤-Reasoning -- comes from Data.Nat.Properties
-- nonnesting {_} {ys₁} {_} {ys₂} x (Generic.mkOIDSub (x₁ ∷ lₚ) (px All.∷ lₚ≥128) lₑ lₑ<128 leastDigs refl) (Generic.mkOIDSub [] lₚ≥129 lₑ₁ lₑ<129 leastDigs₁ refl)
--   = contradiction (begin 128 ≤⟨ px ⟩
--                   toℕ x₁ ≡⟨ cong toℕ (∷-injectiveˡ x) ⟩ toℕ lₑ₁ ∎) (<⇒≱ lₑ<129)
--   where open ≤-Reasoning
-- nonnesting {_} {ys₁} {_} {ys₂} x (Generic.mkOIDSub (x₁ ∷ lₚ) (px₁ All.∷ lₚ≥128) lₑ lₑ<128 leastDigs refl) (Generic.mkOIDSub (x₂ ∷ lₚ₁) (px₂ All.∷ lₚ≥129) lₑ₁ lₑ<129 leastDigs₁ refl)
--   with nonnesting {!!} (Generic.mkOIDSub lₚ lₚ≥128 lₑ lₑ<128 {!!} refl) (Generic.mkOIDSub lₚ₁ lₚ≥129 lₑ₁ lₑ<129 {!!} refl) 
-- ... | foo = {!!}
