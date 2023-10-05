{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.PM.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.Extension.PM.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Seq         UInt8

iso : Iso PolicyMapFieldsRep PolicyMapFields
proj₁ iso = equivalentPolicyMapFields
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ refl) = refl
proj₂ (proj₂ iso) (mkPolicyMapFields issuerDomainPolicy subjectDomainPolicy refl) = refl

@0 unambiguousPolicyMapFields : Unambiguous PolicyMapFields
unambiguousPolicyMapFields =
  Iso.unambiguous iso
    (Seq.unambiguous OID.unambiguous TLV.nosubstrings OID.unambiguous)

@0 nonmalleablePolicyMapFields : NonMalleable RawPolicyMapFields
nonmalleablePolicyMapFields = Iso.nonmalleable iso RawPolicyMapFieldsRep nm
  where
  nm : NonMalleable RawPolicyMapFieldsRep
  nm = Seq.nonmalleable OID.nonmalleable OID.nonmalleable

@0 nosubstrings : NoSubstrings PolicyMapFields
nosubstrings x x₁ x₂ = Seq.nosubstrings TLV.nosubstrings TLV.nosubstrings x (proj₂ equivalentPolicyMapFields x₁) (proj₂ equivalentPolicyMapFields x₂)

@0 unambiguous : Unambiguous PMFields
unambiguous = TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous
  (TLV.unambiguous unambiguousPolicyMapFields) TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawPMFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (SequenceOf.Bounded.nonmalleable
  TLV.nonempty TLV.nosubstrings (TLV.nonmalleable nonmalleablePolicyMapFields)))
