open import Armor.Binary
open import Armor.Data.X690-DER.Boool.Properties
open import Armor.Data.X690-DER.Boool.TCB
import      Armor.Grammar.Definitions
open import Armor.Prelude

module Armor.Data.X690-DER.Boool.Eq where

open Armor.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ BoolValue
  Eq≋._≋?_ eq≋ (mkBoolValue true .(# 255) trueᵣ refl) (mkBoolValue true .(# 255) trueᵣ refl) = yes ≋-refl
  Eq≋._≋?_ eq≋ (mkBoolValue true .(# 255) trueᵣ refl) (mkBoolValue false .(# 0) falseᵣ refl) = no (λ ())
  Eq≋._≋?_ eq≋ (mkBoolValue false .(# 0) falseᵣ refl) (mkBoolValue true .(# 255) trueᵣ refl) = no (λ ())
  Eq≋._≋?_ eq≋ (mkBoolValue false .(# 0) falseᵣ refl) (mkBoolValue false .(# 0) falseᵣ refl) = yes ≋-refl
