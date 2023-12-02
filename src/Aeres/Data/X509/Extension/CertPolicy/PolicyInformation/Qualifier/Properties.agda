open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
import      Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.Strings.IA5String
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties where

open Aeres.Data.X690-DER.OID
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Seq         UInt8
open Aeres.Grammar.Sum         UInt8

module CPSURIQualifier where

  @0 unambiguous : Unambiguous CPSURIQualifier
  unambiguous =
    DefinedByOID.unambiguous CPSURIQualifierParam
      λ o → Parallel.unambiguous×ₚ (TLV.unambiguous IA5String.unambiguous) λ where ≋-refl ≋-refl → refl

  @0 nosubstrings : NoSubstrings CPSURIQualifier
  nosubstrings = DefinedByOID.nosubstrings _ (λ _ → Parallel.nosubstrings₁ TLV.nosubstrings)

  @0 nonmalleable : NonMalleable RawCPSURIQualifier
  nonmalleable = DefinedByOID.nonmalleableFields CPSURIQualifierParam λ {bs} {a} {bs₁} {bs₂} → nm{bs}{a}{bs₁}{bs₂}
    where
    nm : NonMalleable₁ RawCPSURIQualifierParam
    nm p₁ p₂ eq =
      Parallel.nonmalleable₁ RawIA5String IA5String.nonmalleable (λ where _ ≋-refl ≋-refl → refl)
        p₁ p₂ eq

module UserNoticeQualifier where
  @0 unambiguous : Unambiguous UserNoticeQualifier
  unambiguous =
    DefinedByOID.unambiguous UserNoticeQualifierParam
      λ o → Parallel.unambiguous×ₚ (UserNotice.unambiguous) λ where ≋-refl ≋-refl → refl

  @0 nosubstrings : NoSubstrings UserNoticeQualifier
  nosubstrings = DefinedByOID.nosubstrings _ (λ _ → Parallel.nosubstrings₁ TLV.nosubstrings)

  @0 nonmalleable : NonMalleable RawUserNoticeQualifier
  nonmalleable = DefinedByOID.nonmalleableFields UserNoticeQualifierParam λ {bs}{a}{bs₁}{bs₂} → nm{bs}{a}{bs₁}{bs₂}
    where
    nm : NonMalleable₁ RawUserNoticeQualifierParam
    nm p₁ p₂ eq =
      Parallel.nonmalleable₁ RawUserNotice UserNotice.nonmalleable (λ where _ ≋-refl ≋-refl → refl)
        p₁ p₂ eq

iso : Iso PolicyQualifierInfoFieldsRep PolicyQualifierInfoFields
proj₁ iso = equivalentPolicyQualifierInfoFields
proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
proj₁ (proj₂ iso) (Sum.inj₂ x) = refl
proj₂ (proj₂ iso) (cpsURI x) = refl
proj₂ (proj₂ iso) (userNotice x) = refl

@0 nosubstrings : NoSubstrings PolicyQualifierInfoFields
nosubstrings =
  Iso.nosubstrings equivalentPolicyQualifierInfoFields
    (Sum.nosubstrings
      CPSURIQualifier.nosubstrings
      UserNoticeQualifier.nosubstrings
      (DefinedByOID.noConfusionFieldsParam CPSURIQualifierParam
        (λ where o (mk×ₚ fstₚ₁ ≋-refl) (mk×ₚ fstₚ₂ ()))))

@0 unambiguous : Unambiguous PolicyQualifiersSeq
unambiguous = TLV.unambiguous (SequenceOf.Bounded.unambiguous
  (TLV.unambiguous
    (Iso.unambiguous iso
   (Sum.unambiguous CPSURIQualifier.unambiguous UserNoticeQualifier.unambiguous
      (DefinedByOID.noConfusionFieldsParam CPSURIQualifierParam
        λ where
          o (mk×ₚ _ ≋-refl) (mk×ₚ fstₚ₂ (mk≋ () _))))))
    TLV.nonempty
    TLV.nosubstrings)

@0 nonmalleable : NonMalleable RawPolicyQualifiersSeq
nonmalleable =
  TLV.nonmalleable
    (SequenceOf.Bounded.nonmalleable TLV.nonempty TLV.nosubstrings
      (TLV.nonmalleable (Iso.nonmalleable iso RawPolicyQualifierInfoFieldsRep nm)))
  where
  nm : NonMalleable RawPolicyQualifierInfoFieldsRep
  nm = Sum.nonmalleable CPSURIQualifier.nonmalleable UserNoticeQualifier.nonmalleable
