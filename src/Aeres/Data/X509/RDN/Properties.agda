{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString
open import Aeres.Data.X509.RDN.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.Nat.Properties as Nat

module Aeres.Data.X509.RDN.Properties where

open Aeres.Grammar.Definitions UInt8

module ATV where
  Rep = &ₚ OID DirectoryString

  iso : Iso Rep RDNATVFields
  proj₁ (proj₁ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkRDNATVFields fstₚ₁ sndₚ₁ bs≡
  proj₂ (proj₁ iso) (mkRDNATVFields oid val bs≡) = mk&ₚ oid val bs≡
  proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
  proj₂ (proj₂ iso) (mkRDNATVFields oid val bs≡) = refl

  @0 unambiguous : Unambiguous RDNATVFields
  unambiguous = isoUnambiguous iso (unambiguous&ₚ OID.unambiguous TLV.nonnesting DirectoryString.unambiguous)

module RDN where
  @0 unambiguous : Unambiguous RDN
  unambiguous =
    TLV.unambiguous
      (unambiguousΣₚ
        (SequenceOf.unambiguous
          (TLV.unambiguous ATV.unambiguous)
          TLV.nonempty
          TLV.nonnesting)
        (λ _ → Nat.≤-irrelevant))

module Seq where
  @0 unambiguous : Unambiguous RDNSeq
  unambiguous =
    TLV.unambiguous
      (SequenceOf.unambiguous
        RDN.unambiguous TLV.nonempty TLV.nonnesting)

open RDN public
