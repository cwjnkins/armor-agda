open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X509.CRL.RevokedCertificates.TCB
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension
open import Armor.Data.X690-DER.Int
open import Armor.Data.X509.Validity.Time
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.IList.TCB
import      Armor.Grammar.Option
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.Properties where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel     UInt8

iso : Iso RevokedCertificateFieldsRep RevokedCertificateFields
proj₁ iso = equivalentRevokedCertificateFields
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ fstₚ₂ sndₚ₁ refl) fstₚ₁ bs≡) =
  subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkRevokedCertificateFields cserial rdate entryextensions bs≡) =
  subst₀ (λ eq → mkRevokedCertificateFields cserial rdate entryextensions eq ≡ mkRevokedCertificateFields _ _ _ bs≡) (≡-unique bs≡ _) refl

@0 unambiguous : Unambiguous RevokedCertificates
unambiguous = TLV.unambiguous (SequenceOf.Bounded.unambiguous
  (TLV.unambiguous
    (Iso.unambiguous iso
      (Seq.unambiguous
        (Seq.unambiguous
          Int.unambiguous
          TLV.nosubstrings
          Time.unambiguous)
        (Seq.nosubstrings TLV.nosubstrings Time.nosubstrings)
        (Option.unambiguous EntryExtension.unambiguous TLV.nonempty))))
  TLV.nonempty TLV.nosubstrings)

@0 nonmalleable : NonMalleable RawRevokedCertificates
nonmalleable = TLV.nonmalleable (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings
                 (TLV.nonmalleable
                   (Iso.nonmalleable iso RawRevokedCertificateFieldsRep nm)))
               where
               @0 nm :  NonMalleable RawRevokedCertificateFieldsRep
               nm = Seq.nonmalleable (Seq.nonmalleable Int.nonmalleable Time.nonmalleable) (Option.nonmalleable _ EntryExtension.nonmalleable)

