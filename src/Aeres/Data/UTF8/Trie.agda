{-# OPTIONS --subtyping --sized-types --inversion-max-depth=1000 #-}

open import Aeres.Binary
open import Aeres.Prelude
  hiding (tabulate)
import      Data.Fin.Properties as Fin
open import      Aeres.Grammar.IList
import      Data.List.Relation.Binary.Equality.Propositional as List
import      Data.Nat.Properties as Nat

module Aeres.Data.UTF8.Trie  where

open Base256

open import Data.Trie (Fin.<-strictTotalOrder 256) public
open import Data.Tree.AVL.Value (List.≋-setoid{A = UInt8})
-- (List.≋-setoid (Fin.≡-setoid 256))
  as Value public
  hiding (const)

open import Aeres.Data.UTF8.TCB

tabulate : ∀ {ℓ} {n} {V : Value ℓ} → (Fin n → ∃ (Value.family V)) → Trie V _
tabulate f = fromList (Vec.toList (Vec.tabulate f))

UTF8Trie : Set
UTF8Trie = Trie (Value.const (Exists─ (List UInt8) UTF8)) _

private
  V₁ : Value Level.zero
  V₁ = Value.const (List UInt8)

  test₁ : Trie V₁ _
  test₁ = tabulate mkEntry
    where
    mkEntry : Fin 26 → List UInt8 × List UInt8
    proj₁ (mkEntry i) = [ Fin.inject+ 165 (Fin.raise 65 i) ]
    proj₂ (mkEntry i) = [ Fin.inject+ 133 (Fin.raise 97 i) ]

  open import Aeres.Grammar.Sum UInt8

  V₂ : Value Level.zero
  V₂ = Value.const (Exists─ (List UInt8) UTF8)


  -- Value.family V₂ = UTF8Char1
  -- Value.respects V₂ bs₁≡bs₂ u₁ =
  --   subst UTF8Char1 (List.≋⇒≡ bs₁≡bs₂) u₁

  -- test₂ : Trie V₂ _
  -- test₂ = tabulate mkEntry
  --   where
  --   mkEntry : Fin 26 → List UInt8 × Exists─ (List UInt8) UTF8Char
  --   proj₁ (mkEntry i) = [ Fin.inject+ 165 (Fin.raise 65 i) ]
  --   proj₂ (mkEntry i) =
  --     ─ [ j ] , utf81 (mkUTF8Char1 _ pf refl)
  --     where
  --     open Nat.≤-Reasoning
  --     j = Fin.inject+ 133 (Fin.raise 97 i)
  --     pf : toℕ j < 128
  --     pf = s≤s $ begin
  --       (toℕ (Fin.inject+ 133 (Fin.raise 97 i)) ≡⟨ sym (Fin.toℕ-inject+ 133 ((Fin.raise 97 i)))  ⟩
  --       toℕ (Fin.raise 97 i) <⟨ Fin.toℕ<n (Fin.raise 97 i) ⟩
  --       26 + 97 ≤⟨ toWitness{Q = 123 ≤? 127} tt ⟩
  --       127 ∎)


  -- private
  --   inRangeLemmaᵤ : ∀ {l u} (p : Σ[ n ∈ ℕ ] InRange l u n) → {wit : True (u <? 256)} → proj₁ p < 256
  --   inRangeLemmaᵤ p {wit} = Nat.≤-trans (s≤s $ proj₂ (proj₂ p)) (toWitness wit)

  -- translate2-2Map : (p₁ p₂ : Σ[ n ∈ ℕ ] InRange 192 223 n)
  --                   → (r o : Fin 32)
  --                   → (l : Σ[ n ∈ ℕ ] InRange 128 (191 - toℕ r - toℕ o) n)
  --                   → Trie V₂ _
  -- translate2-2Map p₁ p₂ r o l = tabulate mkEntry
  --   where
  --   open Nat.≤-Reasoning
  --   mkEntry : Fin (toℕ r) → List UInt8 × Exists─ (List UInt8) UTF8Char
  --   proj₁ (mkEntry i) =
  --     Fin.fromℕ< (inRangeLemmaᵤ p₁)
  --     ∷ [ Fin.fromℕ<{m = proj₁ l + toℕ i}
  --           (s≤s $ begin
  --             (proj₁ l + toℕ i)
  --               ≤⟨ Nat.+-monoˡ-≤ (toℕ i) (proj₂ (proj₂ l)) ⟩
  --             (191 - toℕ r - toℕ o) + toℕ i
  --               ≤⟨ Nat.+-monoʳ-≤ (191 - toℕ r - toℕ o) (Fin.toℕ≤n i) ⟩
  --             191 - toℕ r - toℕ o + toℕ r
  --               ≤⟨ Nat.+-monoˡ-≤ (toℕ r) (begin
  --                 191 - toℕ r - toℕ o ≤⟨ Nat.∸-monoʳ-≤ {n = toℕ o} (191 - toℕ r) z≤n ⟩
  --                 191 - toℕ r          ≤⟨ Nat.m∸n≤m 191 (toℕ r) ⟩
  --                 191 ∎) ⟩
  --             191 + toℕ r
  --               ≤⟨ Nat.+-monoʳ-≤ 191 (Fin.toℕ≤n r) ⟩
  --             191 + 32
  --               ≤⟨ toWitness{Q = 191 + 32 ≤? 255} tt ⟩
  --             255 ∎) ]
        
  --   proj₂ (mkEntry i) = (─ bs) , utf82 (mkUTF8Char2 _ _ ({!!} , {!!}) {!!} refl)
  --     where
  --     pf : InRange 128 191 (proj₁ l + toℕ o + toℕ i)
  --     proj₁ pf = {!!}
  --     proj₂ pf = begin
  --       proj₁ l + toℕ o + toℕ i ≡⟨ Nat.+-assoc (proj₁ l) (toℕ o) (toℕ i) ⟩
  --       proj₁ l + (toℕ o + toℕ i) ≤⟨ Nat.+-monoˡ-≤ (toℕ o + toℕ i) (proj₂ (proj₂ l)) ⟩
  --       (191 - toℕ r - toℕ o) + (toℕ o + toℕ i) ≡⟨ cong (_+ (toℕ o + toℕ i)) (Nat.∸-+-assoc 191 (toℕ r) (toℕ o)) ⟩
  --       191 - (toℕ r + toℕ o) + (toℕ o + toℕ i) ≡⟨ cong (λ x → 191 - x + (toℕ o + toℕ i)) (Nat.+-comm (toℕ r) (toℕ o)) ⟩
  --       191 - (toℕ o + toℕ r) + (toℕ o + toℕ i) ≤⟨ Nat.+-monoʳ-≤ (191 - (toℕ o + toℕ r))
  --                                                    (Nat.+-monoʳ-≤ (toℕ o) (Fin.toℕ≤n i)) ⟩
  --       191 - (toℕ o + toℕ r) + (toℕ o + toℕ r)
  --         ≡⟨ sym (Nat.+-∸-comm (toℕ o + toℕ r)
  --              (begin
  --                toℕ o + toℕ r ≤⟨ Nat.+-mono-≤ (Fin.toℕ≤n o) (Fin.toℕ≤n r) ⟩
  --                32 + 32 ≤⟨ toWitness{Q = 64 ≤? 191} tt ⟩
  --                191 ∎))
  --          ⟩
  --       191 + (toℕ o + toℕ r) - (toℕ o + toℕ r) ≡⟨ Nat.+-∸-assoc 191 (Nat.≤-refl{x = toℕ o + toℕ r}) ⟩
  --       191 + ((toℕ o + toℕ r) - (toℕ o + toℕ r)) ≡⟨ cong (191 +_) (Nat.n∸n≡0 (toℕ o + toℕ r)) ⟩
  --       191 - 0 ≡⟨ Nat.+-identityʳ 191 ⟩
  --       191 ∎

  --     b₂ : UInt8
  --     b₂ = Fin.fromℕ<{m = proj₁ l + toℕ o + toℕ i} (s≤s (Nat.≤-trans (proj₂ pf) (toWitness{Q = 191 ≤? 255} tt)))

  --     @0 bs : List UInt8
  --     bs = Fin.fromℕ< (inRangeLemmaᵤ p₂) ∷ [ b₂ ]

  --               ∷ {!!})

