{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.Properties where

open Aeres.Grammar.Definitions              UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

@0 unambiguous : Unambiguous OctetStringValue
unambiguous (singleton x refl) (singleton .x refl) = refl

@0 nonmalleableValue : NonMalleable OctetStringValue RawOctetStringValue
NonMalleable.unambiguous nonmalleableValue = unambiguous
NonMalleable.injective nonmalleableValue (─ _ , singleton bytes₁ refl) (─ _ , singleton bytes₂ refl) refl = refl

@0 nonmalleable : NonMalleable OctetString RawOctetString
nonmalleable = TLV.nonmalleable nonmalleableValue

instance
  OctetstringValueEq≋ : Eq≋ OctetStringValue
  Eq≋._≋?_ OctetstringValueEq≋{._}{._} (singleton bs₁ refl) (singleton bs₂ refl)
    with bs₁ ≟ bs₂
  ... | yes refl = yes ≋-refl
  ... | no ¬bs₁≡bs₂ = no λ where
    ≋-refl → contradiction refl ¬bs₁≡bs₂

  OctetStringValueEq : Eq (Exists─ (List UInt8) OctetStringValue)
  OctetStringValueEq = Eq≋⇒Eq it
