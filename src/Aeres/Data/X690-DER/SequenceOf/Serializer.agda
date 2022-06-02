{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open        Base256
open import Aeres.Data.X690-DER.SequenceOf.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Grammar.IList
open import Aeres.Prelude

open Aeres.Grammar.Definitions UInt8

module Aeres.Data.X690-DER.SequenceOf.Serializer
  {@0 A : List UInt8 → Set} (ser : ∀ {@0 bs} → A bs → Singleton bs)
  where

serializeSequenceOf
  : ∀ {@0 bs} → SequenceOf A bs → Singleton bs
serializeSequenceOf nil = self
serializeSequenceOf {bs} (cons (mkIListCons{bs₁}{bs₂} head₁ tail₁ bs≡))
  with ser head₁
  |    serializeSequenceOf tail₁
... | singleton h h≡ | singleton t t≡ =
  singleton (h ++ t)
    (begin h ++ t ≡⟨ cong₂ _++_ h≡ t≡ ⟩
           bs₁ ++ bs₂ ≡⟨ sym bs≡ ⟩
           bs ∎)
  where open ≡-Reasoning

serializeNonEmptySequenceOf
  : ∀ {@0 bs} → NonEmptySequenceOf A bs → Singleton bs
serializeNonEmptySequenceOf (mk×ₚ fstₚ sndₚ refl) = serializeSequenceOf fstₚ
