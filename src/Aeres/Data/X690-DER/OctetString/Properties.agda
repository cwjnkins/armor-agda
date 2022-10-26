{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.OctetString.Properties where

open Base256
open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous OctetStringValue
unambiguous (singleton x refl) (singleton .x refl) = refl

instance
  OctetstringValueEq≋ : Eq≋ OctetStringValue
  Eq≋._≋?_ OctetstringValueEq≋{._}{._} (singleton bs₁ refl) (singleton bs₂ refl)
    with bs₁ ≟ bs₂
  ... | yes refl = yes ≋-refl
  ... | no ¬bs₁≡bs₂ = no λ where
    ≋-refl → contradiction refl ¬bs₁≡bs₂
