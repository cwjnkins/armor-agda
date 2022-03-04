{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.Primitives    as PrimProps
import      Aeres.Data.X509.Properties.SignAlgFields as SignAlgFieldsProps
import      Aeres.Data.X509.Properties.TBSCertFields as TBSCertFieldsProps
import      Aeres.Data.X509.Properties.TLV           as TLVProps
open import Aeres.Prelude
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CertFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

equivalent : Equivalent (&ₚ X509.TBSCert (&ₚ X509.SignAlg BitString)) X509.CertFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) = X509.mkCertFields fstₚ₁ fstₚ₂ sndₚ₁ bs≡
proj₂ equivalent (X509.mkCertFields tbs signAlg signature bs≡) = mk&ₚ tbs (mk&ₚ signAlg signature refl) bs≡

iso : Iso (&ₚ X509.TBSCert (&ₚ X509.SignAlg BitString)) X509.CertFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) = refl
proj₂ (proj₂ iso) (X509.mkCertFields tbs signAlg signature bs≡) = refl

@0 unambiguous : Unambiguous X509.CertFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ (TLVProps.unambiguous TBSCertFieldsProps.unambiguous) TLVProps.nonnesting
      (unambiguous&ₚ (TLVProps.unambiguous SignAlgFieldsProps.unambiguous) TLVProps.nonnesting
        (TLVProps.unambiguous PrimProps.BitstringValue.unambiguous)))
