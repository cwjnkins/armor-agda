{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Boool.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X690-DER.Boool.Properties where

open Aeres.Grammar.Definitions UInt8

nonempty : NonEmpty BoolValue
nonempty () refl

@0 nonnesting : NonNesting BoolValue
nonnesting x (mkBoolValue v b vᵣ bs≡) (mkBoolValue v₁ b₁ vᵣ₁ bs≡₁) =
  proj₁ $ Lemmas.length-++-≡ _ _ _ _ x (trans (cong length bs≡) (cong length (sym bs≡₁)))

@0 unambiguous : Unambiguous BoolValue
unambiguous (mkBoolValue .#0 .(# 0) falseᵣ refl) (mkBoolValue .#0 .(# 0) falseᵣ refl) = refl
unambiguous (mkBoolValue .#0 .(# 0) falseᵣ refl) (mkBoolValue .#1 .(# 255) trueᵣ ())
unambiguous (mkBoolValue .#1 .(# 255) trueᵣ refl) (mkBoolValue .#0 .(# 0) falseᵣ ())
unambiguous (mkBoolValue .#1 .(# 255) trueᵣ refl) (mkBoolValue .#1 .(# 255) trueᵣ refl) = refl