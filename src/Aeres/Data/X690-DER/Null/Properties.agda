{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Length.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties     as Nat

module Aeres.Data.X690-DER.Null.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous Null
unambiguous = TLV.unambiguous λ where refl refl → refl

instance
  eq≋ : Eq≋ (_≡ [])
  Eq≋._≋?_ eq≋ refl refl = yes ≋-refl

-- {-# TERMINATING #-}
-- nullBS : ∀ {@0 bs} → Null bs → bs ≡ Tag.Null ∷ [ # 0 ]
-- nullBS (mkTLV (short (mkShort Fin.zero l<128 refl)) refl len≡ refl) = refl
-- nullBS (mkTLV (long (mkLong l l>128 lₕ lₕ≢0 lₜ lₜLen lₕₜMinRepLong refl)) refl len≡ refl) = {!!}
--   where
--   @0 go : ∀ lₜ → getLengthRaw (reverse (lₕ ∷ lₜ)) ≥ 1
--   go lₜ
--     with reverse (lₕ ∷ lₜ) | inspect reverse (lₕ ∷ lₜ)
--   go lₜ | [] | [ eq ]R =
--     contradiction{P = length (reverse (lₕ ∷ lₜ)) ≡ 0}
--       (cong (length{A = UInt8}) eq)
--       (Nat.>⇒≢ (Nat.≤-trans (s≤s z≤n) (Lemmas.≡⇒≤ (sym (length-reverse (lₕ ∷ lₜ))))))
--   go [] | x ∷ [] | [ refl ]R = Nat.≤-trans lₕ≢0 (Lemmas.≡⇒≤ (sym (Nat.+-identityʳ _)))
--   go (x₁ ∷ lₜ) | x ∷ bs | [ eq ]R = ≤.begin
--     1 ≤.≤⟨ ih ⟩
--     getLengthRaw (reverse (lₕ ∷ lₜ')) ≤.≡⟨ {!!} ⟩
--     getLengthRaw bs ≤.≤⟨ {!!} ⟩
--     256 * getLengthRaw bs ≤.≤⟨ {!!} ⟩
--     toℕ x + 256 * getLengthRaw bs ≤.∎
--     where
--     open ≡-Reasoning
--     module ≤ = Nat.≤-Reasoning

--     lₜ' = take (length lₜ) (x₁ ∷ lₜ)

--     ih = go lₜ'

--     eq' : reverse (lₕ ∷ lₜ') ≡ bs
--     eq' = begin
--       (reverse (lₕ ∷ lₜ') ≡⟨⟩
--       reverse (lₕ ∷ take (length lₜ) (x₁ ∷ lₜ)) ≡⟨⟩
--       reverse (take (1 + length lₜ) (lₕ ∷ x₁ ∷ lₜ))
--         ≡⟨ Lemmas.reverse-take (1 + length lₜ) (lₕ ∷ x₁ ∷ lₜ) ⟩
--       drop ((2 + length lₜ) - (1 + length lₜ)) (reverse (lₕ ∷ x₁ ∷ lₜ))
--         ≡⟨ cong (λ y → drop y (reverse (lₕ ∷ x₁ ∷ lₜ)))
--              (begin (2 + length lₜ) - (1 + length lₜ)
--                       ≡⟨ sym (Nat.∸-+-assoc (2 + length lₜ) 1 (length lₜ)) ⟩
--                     (2 + length lₜ - 1) - length lₜ
--                       ≡⟨ cong (λ y → y ∸ length lₜ) (Nat.+-∸-comm (length lₜ) (1 ≤ 2 ∋ s≤s z≤n)) ⟩
--                     (1 + length lₜ - length lₜ) ≡⟨ Nat.+-∸-assoc 1{n = length lₜ} Nat.≤-refl ⟩
--                     1 + (length lₜ - length lₜ) ≡⟨ cong (1 +_) (Nat.n∸n≡0 (length lₜ)) ⟩
--                     1 + 0 ≡⟨⟩
--                     1 ∎) ⟩
--       drop 1 (reverse (lₕ ∷ x₁ ∷ lₜ)) ≡⟨ cong (drop 1) eq ⟩
--       drop 1 (x ∷ bs) ≡⟨⟩
--       bs ∎)
    
