{-# OPTIONS --subtyping #-}


open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OID                       as OIDProps
import      Aeres.Data.X509.Properties.PolicyQualifierInfoFields as PQIProps
import      Aeres.Data.X509.Properties.SequenceOf                as SeqProps
import      Aeres.Data.X509.Properties.TLV                       as TLVProps
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Properties.PolicyInformationFields where

open ≡-Reasoning
open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig

iso : Iso (&ₚ Generic.OID (Option X509.PolicyQualifiersSeq))
          X509.PolicyInformationFields
proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = X509.mkPolicyInformationFields fstₚ₁ sndₚ₁ bs≡
proj₂ (proj₁ iso) (X509.mkPolicyInformationFields cpid cpqls bs≡) = mk&ₚ cpid cpqls bs≡
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (X509.mkPolicyInformationFields cpid cpqls bs≡) = refl

@0 unambiguous : Unambiguous X509.PolicyInformationFields
unambiguous =
  isoUnambiguous iso
    (Unambiguous.unambiguous-&₁option₁
      OIDProps.unambiguous TLVProps.nonnesting
      (TLVProps.unambiguous
        (SeqProps.BoundedSequenceOf.unambiguous
          (TLVProps.unambiguous PQIProps.unambiguous) TLVProps.nonempty TLVProps.nonnesting))
      TLVProps.nonempty)
