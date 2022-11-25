{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA.AccessDesc.AccessMethod
open import Aeres.Data.X509.Extension.AIA.AccessDesc.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.Properties where

open Aeres.Grammar.Definitions UInt8

Rep = &ₚ AccessMethod GeneralName

equivalent : Equivalent Rep AccessDescFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkAccessDescFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkAccessDescFields acmethod aclocation bs≡) = mk&ₚ acmethod aclocation bs≡

iso : Iso Rep AccessDescFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkAccessDescFields acmethod aclocation bs≡) = refl

@0 nonnesting : NonNesting AccessDescFields
nonnesting x x₁ x₂ = NonNesting&ₚ TLV.nonnesting GeneralName.nonnesting x (proj₂ equivalent x₁) (proj₂ equivalent x₂)

@0 unambiguous : Unambiguous AccessDescFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ (TLV.unambiguous AccessMethod.unambiguous)
      TLV.nonnesting GeneralName.unambiguous)

