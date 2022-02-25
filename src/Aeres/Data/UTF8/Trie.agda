{-# OPTIONS --subtyping --sized-types --inversion-max-depth=1000 #-}

open import Aeres.Binary
open import Aeres.Prelude
import      Data.Fin.Properties as Fin
import      Data.List.Relation.Binary.Equality.Propositional as List
import      Data.Nat.Properties as Nat

module Aeres.Data.UTF8.Trie (A : Set) where

open Base256

open import Data.Trie (Fin.<-strictTotalOrder 256) public
open import Data.Tree.AVL.Value (List.≋-setoid{A = UInt8})
-- (List.≋-setoid (Fin.≡-setoid 256))
  as Value public
  hiding (const)

private
  V₁ : Value Level.zero
  V₁ = Value.const (List UInt8)

  test₁ : Trie V₁ _
  test₁ = fromList (Vec.toList (Vec.tabulate mkEntry))
    where
    mkEntry : Fin 26 → List UInt8 × List UInt8
    proj₁ (mkEntry i) = [ Fin.inject+ 165 (Fin.raise 65 i) ]
    proj₂ (mkEntry i) = [ Fin.inject+ 133 (Fin.raise 97 i) ]

  open import Aeres.Data.UTF8.TCB
  open import Aeres.Grammar.Sum UInt8

  V₂ : Value Level.zero
  V₂ = Value.const (Exists─ (List UInt8) UTF8Char)
  -- Value.family V₂ = UTF8Char1
  -- Value.respects V₂ bs₁≡bs₂ u₁ =
  --   subst UTF8Char1 (List.≋⇒≡ bs₁≡bs₂) u₁

  test₂ : Trie V₂ _
  test₂ = fromList (Vec.toList (Vec.tabulate mkEntry))
    where
    mkEntry : Fin 26 → List UInt8 × Exists─ (List UInt8) UTF8Char
    proj₁ (mkEntry i) = [ Fin.inject+ 165 (Fin.raise 65 i) ]
    proj₂ (mkEntry i) =
      ─ [ j ] , Sum.inj₁ (mkUTF8Char1 _ pf refl)
      where
      open Nat.≤-Reasoning
      j = Fin.inject+ 133 (Fin.raise 97 i)
      pf : toℕ j < 128
      pf = s≤s $ begin
        (toℕ (Fin.inject+ 133 (Fin.raise 97 i)) ≡⟨ sym (Fin.toℕ-inject+ 133 ((Fin.raise 97 i)))  ⟩
        toℕ (Fin.raise 97 i) <⟨ Fin.toℕ<n (Fin.raise 97 i) ⟩
        26 + 97 ≤⟨ toWitness{Q = 123 ≤? 127} tt ⟩
        127 ∎)
