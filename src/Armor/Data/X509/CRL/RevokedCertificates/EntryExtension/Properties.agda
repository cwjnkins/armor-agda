open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode
import      Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB.OIDs as OIDs
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
import      Armor.Grammar.Sum
open import Armor.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Properties where

open ≡-Reasoning

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Seq         UInt8
open Armor.Grammar.Sum         UInt8

module Fields where
  iso : ∀ {@0 P} {A : @0 List UInt8 → Set}
        → Iso (ExtensionFieldsRep P A) (ExtensionFields P A)
  proj₁ iso = equivalentExtensionFields
  proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) = refl
  proj₂ (proj₂ iso) (mkExtensionFields extnId extnId≡ crit extension refl) = refl

  @0 unambiguous : ∀ {@0 P} {A : @0 List UInt8 → Set} → (∀ {x} → Unique (P x)) → Unambiguous A → NoConfusion Boool A → Unambiguous (ExtensionFields P A)
  unambiguous{P}{A} uaₚ ua₁ nc =
    Iso.unambiguous iso
      (Seq.unambiguous{A = Σₚ OID λ _ x → Erased (P (TLV.v x))}{B = &ₚ (Default Boool falseBoool) A}
        (Parallel.unambiguous OID.unambiguous λ a → erased-unique uaₚ )
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Sequence.unambiguousDefault₁ _ Boool.unambiguous TLV.nosubstrings ua₁ nc))

  @0 nonmalleable : ∀ {@0 P : List UInt8 → Set}{A : @0 List UInt8 → Set} {ra : Raw A} → (∀ {x} → Unique (P x)) → NonMalleable ra → NonMalleable (RawExtensionFields{P} ra)
  nonmalleable{ra = ra} x x₁ =
    Iso.nonmalleable iso (RawExtensionFieldsRep ra)
    (Seq.nonmalleable
     (Parallel.nonmalleable₁ RawOID OID.nonmalleable λ a p₁ p₂ → erased-unique x p₁ p₂)
     (Seq.nonmalleable
       (Default.nonmalleable _ Boool.nonmalleable) x₁))

module Select where
  iso : Iso SelectEntryExtnRep SelectEntryExtn
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))) = refl
  proj₂ (proj₂ iso) (crlrsnextn x) = refl
  proj₂ (proj₂ iso) (invdateextn x) = refl
  proj₂ (proj₂ iso) (certissextn x)  = refl
  proj₂ (proj₂ iso) (other _ _)   = refl

  @0 unambiguous : Unambiguous SelectEntryExtn
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous
        (Fields.unambiguous ≡-unique ReasonCode.unambiguous (TLV.noconfusion λ ()))
        (Sum.unambiguous
          (Fields.unambiguous ≡-unique InvalidityDate.unambiguous (TLV.noconfusion λ ()))
          (Sum.unambiguous
            (Fields.unambiguous ≡-unique CertIssuer.unambiguous (TLV.noconfusion λ ()))
                                  (Parallel.unambiguous
                                    (Fields.unambiguous T-unique
                                      OctetString.unambiguous (TLV.noconfusion λ ()))
                                    (λ _ → T-unique))
                              noconfusion₀)
                    noconfusion₂)
                  noconfusion₁)
    where
    noconfusionOIDS : ∀ {@0 A B oid₁ oid₂} → oid₁ ≢ oid₂ → NoConfusion (ExtensionFields (_≡ oid₁) A) (ExtensionFields (_≡ oid₂) B)
    noconfusionOIDS oid≢ {xs₁}{ys₁}{xs₂}{ys₂}++≡ (mkExtensionFields{oex = oex}{cex}{ocex} extnId extnId≡ crit extension bs≡) (mkExtensionFields{oex = oex₁}{cex₁}{ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
      contradiction oid≡ λ where refl → oid≢ (trans₀ (sym extnId≡) (trans v≡ extnId≡₁) {- extnId≡₁ -})
      where
      @0 bs≡' : oex ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oex ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oex ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oex ≡ oex₁
      oid≡ = TLV.nosubstrings bs≡' extnId extnId₁

      @0 oidT≡ : _≋_{A = OID} extnId extnId₁
      oidT≡ = mk≋ oid≡ (OID.unambiguous _ _)

      @0 v≡ : TLV.v extnId ≡ TLV.v extnId₁
      v≡ = caseErased oidT≡ ret (const _) of λ where
        ≋-refl → ─ refl

    noconfusionOIDN
      : ∀ {@0 A B oid} → (oid ∈ supportedExtensions)
        → NoConfusion (ExtensionFields (_≡ oid) A)
                      (Σₚ (ExtensionFields (False ∘ (_∈? supportedExtensions)) B) (λ _ u → T (not (ExtensionFields.getCrit u))))
    noconfusionOIDN{oid = oid} supported {xs₁} {ys₁} {xs₂} {ys₂} ++≡ (mkExtensionFields {oex = oex} {cex} {ocex} extnId refl crit extension bs≡) (mk×ₚ (mkExtensionFields {oex = oex₁} {cex₁} {ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) _) =
      contradiction (subst (_∈ supportedExtensions) v≡ supported) (toWitnessFalse extnId≡₁) {- (toWitnessFalse extnId≡₁ )-}
      where
      @0 bs≡' : oex ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oex ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oex ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) {- (sym bs≡) -} ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oex ≡ oex₁
      oid≡ = TLV.nosubstrings bs≡' extnId extnId₁

      @0 oidT≡ : _≋_{A = OID} extnId extnId₁
      oidT≡ = mk≋ oid≡ (OID.unambiguous _ _)

      @0 v≡ : TLV.v extnId ≡ TLV.v extnId₁
      v≡ = caseErased oidT≡ ret (const _) of λ where
        ≋-refl → ─ refl

    noconfusion₁ : NoConfusion (ExtensionFields (_≡ OIDs.REASONLit) ReasonCodeFields) (Sum _ _)
    noconfusion₁ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.REASONLit) ReasonCodeFields}
        (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.REASONLit) ReasonCodeFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₂ : NoConfusion (ExtensionFields (_≡ OIDs.INVALIDITYLit) InvalidityDateFields) (Sum _ _)
    noconfusion₂ = 
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.INVALIDITYLit) InvalidityDateFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₀ : NoConfusion
                     (ExtensionFields (_≡ OIDs.CERTISSUERLit) CertIssuerFields)
                     (Σₚ (ExtensionFields (False ∘ (_∈? supportedExtensions)) _) _)
    noconfusion₀ = noconfusionOIDN (toWitness{Q = _ ∈? _} tt)

  @0 nonmalleable : NonMalleable RawSelectEntryExtn
  nonmalleable = Iso.nonmalleable iso RawSelectEntryExtnRep nm
    where
    RawRep₀ = RawSum (RawExtensionFields RawCertIssuerFields)
                     (RawΣₚ₁ (RawExtensionFields RawOctetString) (λ _ u → T (not (ExtensionFields.getCrit u))))
    RawRep₁ = RawSum (RawExtensionFields RawInvalidityDateFields) RawRep₀
    RawRep = RawSum (RawExtensionFields{P = (_≡ OIDs.CERTISSUERLit)} RawReasonCodeFields) RawRep₁
                           
    nm : NonMalleable RawSelectEntryExtnRep
    nm = Sum.nonmalleable{ra = RawExtensionFields RawReasonCodeFields}{rb = RawRep₁} ((Fields.nonmalleable ≡-unique ReasonCode.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawInvalidityDateFields}{rb = RawRep₀} ((Fields.nonmalleable ≡-unique InvalidityDate.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawCertIssuerFields}{rb = (RawΣₚ₁ (RawExtensionFields RawOctetString) (λ _ u → T (not (ExtensionFields.getCrit u))))}
        (Fields.nonmalleable ≡-unique CertIssuer.nonmalleable)
        (Parallel.nonmalleable₁ (RawExtensionFields RawOctetString)
           (Fields.nonmalleable T-unique OctetString.nonmalleable)
           (λ _ → T-unique))))

@0 unambiguous : Unambiguous EntryExtensions
unambiguous =
    (TLV.unambiguous
      (SequenceOf.Bounded.unambiguous
        (TLV.unambiguous Select.unambiguous)
        TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawEntryExtensions
nonmalleable = TLV.nonmalleable
                 (SequenceOf.Bounded.nonmalleable
                   TLV.nonempty TLV.nosubstrings (TLV.nonmalleable
                     Select.nonmalleable))
