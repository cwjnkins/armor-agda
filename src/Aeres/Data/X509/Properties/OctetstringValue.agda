{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
import      Aeres.Grammar.Definitions
open import Aeres.Data.X509

module Aeres.Data.X509.Properties.OctetstringValue where

open Base256
open Aeres.Grammar.Definitions Dig


@0 unambiguous : Unambiguous Generic.OctetstringValue
unambiguous (singleton x refl) (singleton .x refl) = refl

instance
  OctetstringValueEq≋ : Eq≋ Generic.OctetstringValue
  Eq≋._≋?_ OctetstringValueEq≋{._}{._} (singleton bs₁ refl) (singleton bs₂ refl)
    with bs₁ ≟ bs₂
  ... | yes refl = yes ≋-refl
  ... | no ¬bs₁≡bs₂ = no λ where
    ≋-refl → contradiction refl ¬bs₁≡bs₂
