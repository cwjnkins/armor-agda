open import Armor.Binary
open import Armor.Data.X509.Extension.AIA
open import Armor.Data.X509.Extension.AKI
open import Armor.Data.X509.Extension.IAN
open import Armor.Data.X509.Extension.CRLDistPoint
open import Armor.Data.X509.CRL.Extension.CRLN
open import Armor.Data.X509.CRL.Extension.DCRLI
open import Armor.Data.X509.CRL.Extension.IDP
import      Armor.Data.X509.CRL.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.CRL.Extension.TCB
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

module Armor.Data.X509.CRL.Extension.Properties where

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
  iso : Iso SelectExtnRep SelectExtn
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x))))))) = refl
  proj₂ (proj₂ iso) (akiextn x) = refl
  proj₂ (proj₂ iso) (ianextn x) = refl
  proj₂ (proj₂ iso) (crlnextn x)  = refl
  proj₂ (proj₂ iso) (dcrliextn x) = refl
  proj₂ (proj₂ iso) (idpextn x)  = refl
  proj₂ (proj₂ iso) (fcrlextn x) = refl
  proj₂ (proj₂ iso) (aiaextn x) = refl
  proj₂ (proj₂ iso) (other _ _)   = refl

  @0 unambiguous : Unambiguous SelectExtn
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous
        (Fields.unambiguous ≡-unique AKI.unambiguous (TLV.noconfusion λ ()))
        (Sum.unambiguous
          (Fields.unambiguous ≡-unique IAN.unambiguous (TLV.noconfusion λ ()))
          (Sum.unambiguous
            (Fields.unambiguous ≡-unique CRLN.unambiguous (TLV.noconfusion λ ()))
            (Sum.unambiguous
              (Fields.unambiguous ≡-unique DCRLI.unambiguous (TLV.noconfusion λ ()))
              (Sum.unambiguous
                (Fields.unambiguous ≡-unique IDP.unambiguous (TLV.noconfusion λ ()))
                (Sum.unambiguous
                  (Fields.unambiguous ≡-unique CRLDistPoint.unambiguous (TLV.noconfusion λ ()))
                  (Sum.unambiguous
                    (Fields.unambiguous ≡-unique AIA.unambiguous (TLV.noconfusion λ ()))
                                  (Parallel.unambiguous
                                    (Fields.unambiguous T-unique
                                      OctetString.unambiguous (TLV.noconfusion λ ()))
                                    (λ _ → T-unique))
                              noconfusion₀)
                            noconfusion₆)
                          noconfusion₅)
                        noconfusion₄)
                      noconfusion₃)
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

    noconfusion₁ : NoConfusion (ExtensionFields (_≡ OIDs.AKILit) AKIFields) (Sum _ _)
    noconfusion₁ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
              (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))

    noconfusion₂ : NoConfusion (ExtensionFields (_≡ OIDs.IANLit) IANFields) (Sum _ _)
    noconfusion₂ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
            (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
              (noconfusionOIDS λ ())
                (Sum.noconfusion{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))


    noconfusion₃ : NoConfusion (ExtensionFields (_≡ OIDs.CRLNLit) CRLNFields) (Sum _ _)
    noconfusion₃ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLNLit) CRLNFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLNLit) CRLNFields}
          (noconfusionOIDS λ ())
          (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLNLit) CRLNFields}
            (noconfusionOIDS λ ())
              (Sum.noconfusion{ExtensionFields (_≡ OIDs.CRLNLit) CRLNFields}
                 (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))


    noconfusion₄ : NoConfusion (ExtensionFields (_≡ OIDs.DCRLILit) DCRLIFields) (Sum _ _)
    noconfusion₄ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.DCRLILit) DCRLIFields}
        (noconfusionOIDS λ ())
        (Sum.noconfusion{ExtensionFields (_≡ OIDs.DCRLILit) DCRLIFields}
          (noconfusionOIDS λ ())
             (Sum.noconfusion{ExtensionFields (_≡ OIDs.DCRLILit) DCRLIFields}
               (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))


    noconfusion₅ : NoConfusion (ExtensionFields (_≡ OIDs.IDPLit) IDPFields) (Sum _ _)
    noconfusion₅ = 
      Sum.noconfusion{ExtensionFields (_≡ OIDs.IDPLit) IDPFields}
        (noconfusionOIDS λ ())
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.IDPLit) IDPFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₆ : NoConfusion (ExtensionFields (_≡ OIDs.FCRLLit) CRLDistFields) (Sum _ _)
    noconfusion₆ = 
            (Sum.noconfusion{ExtensionFields (_≡ OIDs.FCRLLit) CRLDistFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₀ : NoConfusion
                     (ExtensionFields (_≡ OIDs.AIALit) AIAFields)
                     (Σₚ (ExtensionFields (False ∘ (_∈? supportedExtensions)) _) _)
    noconfusion₀ = noconfusionOIDN (toWitness{Q = _ ∈? _} tt)

  @0 nonmalleable : NonMalleable RawSelectExtn
  nonmalleable = Iso.nonmalleable iso RawSelectExtnRep nm
    where
    RawRep₀ = RawSum (RawExtensionFields RawAIAFields)
                     (RawΣₚ₁ (RawExtensionFields RawOctetString) (λ _ u → T (not (ExtensionFields.getCrit u))))
    RawRep₁ = RawSum (RawExtensionFields RawCRLDistFields) RawRep₀
    RawRep₂ = RawSum (RawExtensionFields RawIDPFields) RawRep₁
    RawRep₃ = RawSum (RawExtensionFields RawDCRLIFields) RawRep₂
    RawRep₄ = RawSum (RawExtensionFields RawCRLNFields) RawRep₃
    RawRep₅ = RawSum (RawExtensionFields RawIANFields) RawRep₄
    RawRep = RawSum (RawExtensionFields{P = (_≡ OIDs.AKILit)} RawAKIFields) RawRep₅
                           
    nm : NonMalleable RawSelectExtnRep
    nm = Sum.nonmalleable{ra = RawExtensionFields RawAKIFields}{rb = RawRep₅} ((Fields.nonmalleable ≡-unique AKI.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawIANFields}{rb = RawRep₄} ((Fields.nonmalleable ≡-unique IAN.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawCRLNFields}{rb = RawRep₃} ((Fields.nonmalleable ≡-unique CRLN.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawDCRLIFields}{rb = RawRep₂} ((Fields.nonmalleable ≡-unique DCRLI.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawIDPFields}{rb = RawRep₁} ((Fields.nonmalleable ≡-unique IDP.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawCRLDistFields}{rb = RawRep₀} ((Fields.nonmalleable ≡-unique CRLDistPoint.nonmalleable))
      (Sum.nonmalleable{ra = RawExtensionFields RawAIAFields}{rb = (RawΣₚ₁ (RawExtensionFields RawOctetString) (λ _ u → T (not (ExtensionFields.getCrit u))))}
        (Fields.nonmalleable ≡-unique AIA.nonmalleable)
        (Parallel.nonmalleable₁ (RawExtensionFields RawOctetString)
           (Fields.nonmalleable T-unique OctetString.nonmalleable)
           (λ _ → T-unique))))))))

@0 unambiguous : Unambiguous Extensions
unambiguous =
    TLV.unambiguous (TLV.unambiguous
      (SequenceOf.Bounded.unambiguous
        (TLV.unambiguous Select.unambiguous)
        TLV.nonempty TLV.nosubstrings))

@0 nonmalleable : NonMalleable RawExtensions
nonmalleable = TLV.nonmalleable (TLV.nonmalleable
                 (SequenceOf.Bounded.nonmalleable
                   TLV.nonempty TLV.nosubstrings (TLV.nonmalleable
                     Select.nonmalleable)))
