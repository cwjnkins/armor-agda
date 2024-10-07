open import Armor.Binary
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X509.CRL.Version
open import Armor.Data.X509.CRL.Extension
open import Armor.Data.X509.CRL.RevokedCertificates
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.Name
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

module Armor.Data.X509.CRL.TBSCertList.Properties where

open Armor.Grammar.Seq    UInt8
open Armor.Grammar.IList.TCB    UInt8
open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel     UInt8

iso : Iso TBSCertListFieldsRep TBSCertListFields
proj₁ iso = equivalentTBSCertListFields
proj₁ (proj₂ iso) (mk&ₚ(mk&ₚ version signAlg refl)
      (mk&ₚ issuer
        (mk&ₚ thisUpdate
          (mk&ₚ nextUpdate
            (mk&ₚ revokedCertificates crlExtensions refl) refl) refl) refl) bs≡)
      = subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions bs≡)
   = subst₀ (λ eq → mkTBSCertListFields version signAlg issuer thisUpdate nextUpdate revokedCertificates crlExtensions eq
     ≡ mkTBSCertListFields _ _ _ _ _ _ _ bs≡) (≡-unique bs≡ _) refl

postulate
  @0 unambiguous : Unambiguous TBSCertList
-- unambiguous = TLV.unambiguous (Iso.unambiguous iso
--   (Seq.unambiguous (Seq.unambiguous (Option.unambiguous Version.unambiguous {!!}) {!Seq.nosubstrings!} SignAlg.unambiguous)
--                    (Seq.nosubstrings {!!} {!!})
--     (Seq.unambiguous Name.unambiguous TLV.nosubstrings (Seq.unambiguous Time.unambiguous Time.nosubstrings
--       (Seq.unambiguous (Option.unambiguous Time.unambiguous {!!}) {!!}
--         (Seq.unambiguous (Option.unambiguous RevokedCertificates.unambiguous TLV.nonempty) {!!}
--           (Option.unambiguous Extension.unambiguous TLV.nonempty)))))))
-- unambiguous = TLV.unambiguous (SequenceOf.Bounded.unambiguous
--   (TLV.unambiguous
--     (Iso.unambiguous iso
--       (Seq.unambiguous
--         (Seq.unambiguous
--           Int.unambiguous
--           TLV.nosubstrings
--           Time.unambiguous)
--         (Seq.nosubstrings TLV.nosubstrings Time.nosubstrings)
--         (Option.unambiguous EntryExtension.unambiguous TLV.nonempty))))
--   TLV.nonempty TLV.nosubstrings)

postulate
  @0 nonmalleable : NonMalleable RawTBSCertList
-- nonmalleable = TLV.nonmalleable (Iso.nonmalleable iso RawTBSCertListFieldsRep nm)
--   where
--   @0 nm :  NonMalleable RawTBSCertListFieldsRep
--   nm = Seq.nonmalleable (Seq.nonmalleable (Option.nonmalleable _ Version.nonmalleable) SignAlg.nonmalleable)
--      (Seq.nonmalleable Name.nonmalleable
--        (Seq.nonmalleable Time.nonmalleable
--          (Seq.nonmalleable (Option.nonmalleable _ Time.nonmalleable)
--            (Seq.nonmalleable (Option.nonmalleable _ RevokedCertificates.nonmalleable)
--              (Option.nonmalleable _ Extension.nonmalleable)))))
