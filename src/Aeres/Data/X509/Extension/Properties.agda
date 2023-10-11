{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA
open import Aeres.Data.X509.Extension.AKI
open import Aeres.Data.X509.Extension.BC
open import Aeres.Data.X509.Extension.CRLDistPoint
open import Aeres.Data.X509.Extension.CertPolicy
open import Aeres.Data.X509.Extension.EKU
open import Aeres.Data.X509.Extension.IAN
open import Aeres.Data.X509.Extension.INAP
open import Aeres.Data.X509.Extension.KU
open import Aeres.Data.X509.Extension.NC
open import Aeres.Data.X509.Extension.PC
open import Aeres.Data.X509.Extension.PM
open import Aeres.Data.X509.Extension.SAN
open import Aeres.Data.X509.Extension.SKI
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Extension.Properties where

open ≡-Reasoning

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8
open Aeres.Grammar.Sum         UInt8

module Fields where
  iso : ∀ {@0 P} {@0 A : @0 List UInt8 → Set}
        → Iso (ExtensionFieldsRep P A) (ExtensionFields P A)
  proj₁ iso = equivalentExtensionFields
  proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) = refl
  proj₂ (proj₂ iso) (mkExtensionFields extnId extnId≡ crit extension refl) = refl

  @0 unambiguous : ∀ {@0 P}{@0 A : @0 List UInt8 → Set} → Unambiguous P → Unambiguous A → NoConfusion Boool A → Unambiguous (ExtensionFields P A)
  unambiguous ua₁ ua₂ nc =
    Iso.unambiguous iso
      (Seq.unambiguous
        (Parallel.unambiguous OID.unambiguous λ a → erased-unique ua₁)
        (Parallel.nosubstrings₁ TLV.nosubstrings)
        (Unambiguous.unambiguous-option₁&₁ (TLV.unambiguous Boool.unambiguous) TLV.nosubstrings ua₂ nc))

  @0 nonmalleable : ∀ {P}{A : @0 List UInt8 → Set} {ra : Raw A} → Unambiguous P → NonMalleable ra → NonMalleable (RawExtensionFields{P} ra)
  nonmalleable{ra = ra} x x₁ = Iso.nonmalleable iso (RawExtensionFieldsRep ra)
    (Seq.nonmalleable
     (Parallel.nonmalleable₁ RawOID OID.nonmalleable λ a p₁ p₂ → erased-unique x p₁ p₂)
     (Seq.nonmalleable
       (Option.nonmalleable RawBoool Boool.nonmalleable) x₁))

module Select where
  iso : Iso SelectExtnRep SelectExtn
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (Sum.inj₁ x) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₁ x)) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))                                                        = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))                                             = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))                                  = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))                       = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))            = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))) = refl
  proj₁ (proj₂ iso) (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))) = refl
  proj₂ (proj₂ iso) (akiextn x) = refl
  proj₂ (proj₂ iso) (skiextn x) = refl
  proj₂ (proj₂ iso) (kuextn x)  = refl
  proj₂ (proj₂ iso) (ekuextn x) = refl
  proj₂ (proj₂ iso) (bcextn x)  = refl
  proj₂ (proj₂ iso) (ianextn x) = refl
  proj₂ (proj₂ iso) (sanextn x) = refl
  proj₂ (proj₂ iso) (cpextn x)  = refl
  proj₂ (proj₂ iso) (crlextn x) = refl
  proj₂ (proj₂ iso) (ncextn x) = refl
  proj₂ (proj₂ iso) (pcextn x) = refl
  proj₂ (proj₂ iso) (pmextn x) = refl
  proj₂ (proj₂ iso) (inapextn x) = refl
  proj₂ (proj₂ iso) (aiaextn x) = refl
  proj₂ (proj₂ iso) (other x)   = refl

  @0 unambiguous : Unambiguous SelectExtn
  unambiguous =
    Iso.unambiguous iso
      (Sum.unambiguous
        (Fields.unambiguous ≡-unique AKI.unambiguous (TLV.noconfusion λ ()))
        (Sum.unambiguous
          (Fields.unambiguous ≡-unique SKI.unambiguous (TLV.noconfusion λ ()))
          (Sum.unambiguous
            (Fields.unambiguous ≡-unique KU.unambiguous (TLV.noconfusion λ ()))
            (Sum.unambiguous
              (Fields.unambiguous ≡-unique EKU.unambiguous (TLV.noconfusion λ ()))
              (Sum.unambiguous
                (Fields.unambiguous ≡-unique BC.unambiguous (TLV.noconfusion λ ()))
                (Sum.unambiguous
                  (Fields.unambiguous ≡-unique IAN.unambiguous (TLV.noconfusion λ ()))
                  (Sum.unambiguous
                    (Fields.unambiguous ≡-unique SAN.unambiguous (TLV.noconfusion λ ()))
                    (Sum.unambiguous
                       (Fields.unambiguous ≡-unique CertPolicy.unambiguous  (TLV.noconfusion λ ()))
                      (Sum.unambiguous
                        (Fields.unambiguous ≡-unique CRLDistPoint.unambiguous (TLV.noconfusion λ ()))
                        (Sum.unambiguous
                          (Fields.unambiguous ≡-unique NC.unambiguous (TLV.noconfusion λ ()))
                          (Sum.unambiguous
                            (Fields.unambiguous ≡-unique PC.unambiguous (TLV.noconfusion λ ()))
                            (Sum.unambiguous
                              (Fields.unambiguous ≡-unique PM.unambiguous (TLV.noconfusion λ ()))
                              (Sum.unambiguous
                                (Fields.unambiguous ≡-unique INAP.unambiguous (TLV.noconfusion λ ()))
                                (Sum.unambiguous
                                  (Fields.unambiguous ≡-unique AIA.unambiguous (TLV.noconfusion λ ()))
                                (Fields.unambiguous ua
                                  (TLV.unambiguous OctetString.unambiguous) (TLV.noconfusion λ ()))
                              noconfusion₀)
                            noconfusion₁₃)
                          noconfusion₁₂)
                        noconfusion₁₁)
                      noconfusion₁₀)
                    noconfusion₉)
                  noconfusion₈)
                noconfusion₇)
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

    noconfusionOIDN : ∀ {@0 A B oid} → (oid ∈ supportedExtensions) → NoConfusion (ExtensionFields (_≡ oid) A) (ExtensionFields (False ∘ (_∈? supportedExtensions)) B)
    noconfusionOIDN{oid = oid} supported {xs₁} {ys₁} {xs₂} {ys₂} ++≡ (mkExtensionFields {oex = oex} {cex} {ocex} extnId refl crit extension bs≡) (mkExtensionFields {oex = oex₁} {cex₁} {ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
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
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                            (noconfusionOIDS λ ())
                            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                              (noconfusionOIDS λ ())
                              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.AKILit) AKIFields}
                                (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))))

    noconfusion₂ : NoConfusion (ExtensionFields (_≡ OIDs.SKILit) SKIFields) (Sum _ _)
    noconfusion₂ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                            (noconfusionOIDS λ ())
                            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SKILit) SKIFields}
                              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))))


    noconfusion₃ : NoConfusion (ExtensionFields (_≡ OIDs.KULit)  KUFields)  (Sum _ _)
    noconfusion₃ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.KULit) KUFields}
                            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))


    noconfusion₄ : NoConfusion (ExtensionFields (_≡ OIDs.EKULit) EKUFields) (Sum _ _)
    noconfusion₄ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.EKULit) EKUFields}
                          (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))


    noconfusion₅ : NoConfusion (ExtensionFields (_≡ OIDs.BCLit)  BCFields)  (Sum _ _)
    noconfusion₅ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.BCLit) BCFields}
                        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))


    noconfusion₆ : NoConfusion (ExtensionFields (_≡ OIDs.IANLit) IANFields) (Sum _ _)
    noconfusion₆ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.IANLit) IANFields}
                      (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))


    noconfusion₇ : NoConfusion (ExtensionFields (_≡ OIDs.SANLit) SANFields) (Sum _ _)
    noconfusion₇ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.SANLit) SANFields}
                    (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))

    noconfusion₈ : NoConfusion (ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields) (Sum _ _)
    noconfusion₈ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CPOLLit) CertPolFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))

    noconfusion₉ : NoConfusion (ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields) (Sum _ _)
    noconfusion₉ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
        (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
          (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.CRLDISTLit) CRLDistFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))

    noconfusion₁₀ : NoConfusion (ExtensionFields (_≡ OIDs.NCLit) NCFields) (Sum _ _)
    noconfusion₁₀ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.NCLit) NCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.NCLit) NCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.NCLit) NCFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.NCLit) NCFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))

    noconfusion₁₁ : NoConfusion (ExtensionFields (_≡ OIDs.PCLit) PCFields) (Sum _ _)
    noconfusion₁₁ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.PCLit) PCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.PCLit) PCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.PCLit) PCFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))

    noconfusion₁₂ : NoConfusion (ExtensionFields (_≡ OIDs.PMLit) PMFields) (Sum _ _)
    noconfusion₁₂ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.PMLit) PMFields}
        (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.PMLit) PMFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₁₃ : NoConfusion (ExtensionFields (_≡ OIDs.INAPLit) INAPFields) (Sum _ _)
    noconfusion₁₃ =
      NoConfusion.sumₚ{ExtensionFields (_≡ OIDs.INAPLit) INAPFields}
        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))

    noconfusion₀ : NoConfusion (ExtensionFields (_≡ OIDs.AIALit) AIAFields) (ExtensionFields _ _)
    noconfusion₀ = noconfusionOIDN (toWitness{Q = _ ∈? _} tt)

    ua : Unambiguous (False ∘ (_∈? supportedExtensions))
    ua = T-unique

  postulate
    @0 nonmalleable : NonMalleable RawSelectExtn
  -- nonmalleable = Iso.nonmalleable iso RawSelectExtnRep
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique AKI.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique SKI.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique KU.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique EKU.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique BC.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique IAN.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique SAN.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique CertPolicy.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique CRLDistPoint.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique NC.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique PC.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique PM.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique INAP.nonmalleable)
  --   (Sum.nonmalleable (Fields.nonmalleable ≡-unique AIA.nonmalleable)
  --                     (Fields.nonmalleable T-unique OctetString.nonmalleable)))))))))))))))

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
