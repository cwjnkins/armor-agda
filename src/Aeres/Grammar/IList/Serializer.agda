{-# OPTIONS --subtyping #-}

import      Aeres.Grammar.IList.TCB
import      Aeres.Grammar.Serializer
open import Aeres.Prelude

module Aeres.Grammar.IList.Serializer (Σ : Set) where

open Aeres.Grammar.IList.TCB  Σ
open Aeres.Grammar.Serializer Σ

serializeIList : ∀ {@0 A} → Serializer A → Serializer (IList A)
serializeIList s nil = self
serializeIList s (consIList{bs₁}{bs₂} head tail bs≡) =
  let tl@(singleton t t≡) = serializeIList s tail
  in
  singleton ((↑ s head) ++ t)
    (begin ↑ s head ++ t ≡⟨ cong₂ _++_ (Singleton.x≡ (s head)) t≡ ⟩
           bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
           _ ∎)
  where open ≡-Reasoning
