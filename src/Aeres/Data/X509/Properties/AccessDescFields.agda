{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.AccessMethod as AccessMethodProps
import Aeres.Data.X509.Properties.GeneralName as GeneralNameProps

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.AccessDescFields where

open Base256
open import Aeres.Grammar.Definitions Dig


equivalent : Equivalent (&ₚ (X509.AccessMethod) (X509.GeneralName)) X509.AccessDescFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkAccessDescFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (X509.mkAccessDescFields acmethod aclocation bs≡) = mk&ₚ acmethod aclocation bs≡

@0 nonnesting : NonNesting X509.AccessDescFields
nonnesting x x₁ x₂ = NonNesting&ₚ AccessMethodProps.nonnesting GeneralNameProps.nonnesting x (proj₂ equivalent x₁) (proj₂ equivalent x₂)
