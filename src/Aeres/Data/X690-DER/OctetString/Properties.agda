open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.Properties where

open Aeres.Grammar.Definitions              UInt8

@0 unambiguousValue : Unambiguous OctetStringValue
unambiguousValue (singleton x refl) (singleton .x refl) = refl

@0 unambiguous : Unambiguous OctetString
unambiguous = TLV.unambiguous unambiguousValue

@0 nonmalleableValue : NonMalleable RawOctetStringValue
nonmalleableValue (singleton bytes₁ refl) (singleton bytes₂ refl) refl = refl

@0 nonmalleable : NonMalleable RawOctetString
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
