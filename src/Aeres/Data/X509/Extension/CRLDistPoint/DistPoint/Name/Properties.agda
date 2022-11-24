{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.TCB
open import Aeres.Data.X509.GeneralName
open import Aeres.Data.X509.RDN
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CRLDistPoint.DistPoint.Name.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

nonnesting : NonNesting DistPointNameChoice
nonnesting x (fullname x₁) (fullname x₂) = ‼ TLV.nonnesting x x₁ x₂
nonnesting x (fullname x₁) (nameRTCrlissr x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (nameRTCrlissr x₁) (fullname x₂) = ⊥-elim (TLV.noconfusion (λ where ()) x x₁ x₂)
nonnesting x (nameRTCrlissr x₁) (nameRTCrlissr x₂) = ‼ TLV.nonnesting x x₁ x₂

Rep = Sum FullName NameRTCrlIssuer

equivalent : Equivalent Rep DistPointNameChoice
proj₁ equivalent (Sum.inj₁ x) = fullname x
proj₁ equivalent (Sum.inj₂ x) = nameRTCrlissr x
proj₂ equivalent (fullname x) = Sum.inj₁ x
proj₂ equivalent (nameRTCrlissr x) = Sum.inj₂ x

iso : Iso Rep DistPointNameChoice
proj₁ iso = equivalent
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (fullname x) = refl
proj₂ (proj₂ iso) (nameRTCrlissr x) = refl

@0 unambiguous : Unambiguous DistPointNameChoice
unambiguous =
  isoUnambiguous iso
    (unambiguousSum
      (TLV.unambiguous GeneralName.GeneralNamesElems.unambiguous)
      (TLV.unambiguous
        (SequenceOf.Bounded.unambiguous (TLV.unambiguous RDN.ATV.unambiguous)
          TLV.nonempty TLV.nonnesting))
      (TLV.noconfusion λ ()))
