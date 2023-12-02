open import Aeres.Binary
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X690-DER.TLV.Properties as TLV
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties     as Nat

module Aeres.Data.X690-DER.Null.Properties where

open Aeres.Grammar.Definitions              UInt8

@0 unambiguous : Unambiguous Null
unambiguous = TLV.unambiguous λ where (─ refl) (─ refl) → refl

@0 nonmalleable : NonMalleable RawNull
nonmalleable = TLV.nonmalleable{t = Tag.Null} (subsingleton⇒nonmalleable (λ where (─ _ , (─ refl)) (─ _ , (─ refl)) → refl))

instance
  eq≋ : Eq≋ (λ x → Erased (x ≡ []))
  Eq≋._≋?_ eq≋ (─ refl) (─ refl) = yes ≋-refl
