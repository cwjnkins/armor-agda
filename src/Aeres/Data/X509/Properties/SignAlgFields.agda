{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
import Aeres.Data.X509.Properties.OID as OIDProps
import Aeres.Data.X509.Properties.TLV as TLVProps

module Aeres.Data.X509.Properties.SignAlgFields where

open Base256
open import Aeres.Grammar.Definitions Dig

iso : Iso (&ₚ Generic.OID (Option Generic.OctetstringValue)) X509.SignAlgFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkSignAlgFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkSignAlgFields signOID param bs≡) = mk&ₚ signOID param bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkSignAlgFields signOID param bs≡) = refl

postulate
  @0 unambiguous : Unambiguous X509.SignAlgFields
-- unambiguous = isoUnambiguous iso (unambiguous&ₚ OIDProps.unambiguous TLVProps.nonnesting {!!} {!!})


