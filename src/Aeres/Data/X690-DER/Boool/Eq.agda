open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool.Properties
open import Aeres.Data.X690-DER.Boool.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.Boool.Eq where

open Aeres.Grammar.Definitions UInt8

instance
  eq≋ : Eq≋ BoolValue
  Eq≋._≋?_ eq≋ (mkBoolValue true b trueᵣ refl) (mkBoolValue true b' trueᵣ refl) =
    yes ≋-refl
  Eq≋._≋?_ eq≋ (mkBoolValue true b vᵣ refl) (mkBoolValue false b' vᵣ' refl) =
    no λ where (mk≋ refl ())
  Eq≋._≋?_ eq≋ (mkBoolValue false b vᵣ refl) (mkBoolValue true b' vᵣ' refl) =
    no λ where (mk≋ refl ()) 
  Eq≋._≋?_ eq≋ (mkBoolValue false b falseᵣ refl) (mkBoolValue false b' falseᵣ refl) =
    yes ≋-refl
