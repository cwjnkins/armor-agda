{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.AccessDescFields   as ADProps
import      Aeres.Data.X509.Properties.BCFieldsSeqFields  as BCProps
import      Aeres.Data.X509.Properties.DistPointFields    as DistPointFieldsProps
import      Aeres.Data.X509.Properties.NCFieldsSeqFields  as NCProps
import      Aeres.Data.X509.Properties.PCFieldsSeqFields  as PCProps
import      Aeres.Data.X509.Properties.PolicyMapFields    as PMProps
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties 
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Extension where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

open ≡-Reasoning

module ExtensionFields where
  equivalent : ∀ {@0 P} {@0 A : @0 List UInt8 → Set}
               → Equivalent
                   (&ₚ (OID ×ₚ (Erased ∘ P))
                       (&ₚ (Option Boool)
                           A))
                   (X509.ExtensionFields P A)
  proj₁ equivalent (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) =
    X509.mkExtensionFields fstₚ₁ sndₚ₁ fstₚ₂ sndₚ₂ refl
  proj₂ equivalent (X509.mkExtensionFields extnId extnId≡ crit extension refl) =
    mk&ₚ (mk×ₚ extnId (─ extnId≡) refl) (mk&ₚ crit extension refl) refl

  iso : ∀ {@0 P} {@0 A : @0 List UInt8 → Set}
        → Iso
            (&ₚ (OID ×ₚ (Erased ∘ P))
                (&ₚ (Option Boool)
                    A))
            (X509.ExtensionFields P A)
  proj₁ iso = equivalent
  proj₁ (proj₂ iso) (mk&ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk&ₚ fstₚ₂ sndₚ₂ refl) refl) = refl
  proj₂ (proj₂ iso) (X509.mkExtensionFields extnId extnId≡ crit extension refl) = refl

  @0 unambiguous : ∀ {@0 P}{@0 A : @0 List UInt8 → Set} → Unambiguous P → Unambiguous A → NoConfusion Boool A → Unambiguous (X509.ExtensionFields P A)
  unambiguous ua₁ ua₂ nc =
    isoUnambiguous iso
      (unambiguous&ₚ
        (unambiguous×ₚ OID.unambiguous (erased-unique ua₁))
        (nonnesting×ₚ₁ TLV.nonnesting)
        (Unambiguous.unambiguous-option₁&₁ (TLV.unambiguous Boool.unambiguous) TLV.nonnesting ua₂ nc))

module SelectExtn where
  Rep = (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AKI      )            AKIFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SKI      )            SKIFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.KU       )            KUFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.EKU      )            EKUFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.BC       )            BCFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.IAN      )            IANFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN      )            SANFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL     )            X509.CertPolFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST  )            X509.CRLDistFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.NC       )            X509.NCFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.PC       )            X509.PCFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.PM       )            X509.PMFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.INAP     )            X509.INAPFields)
        (Sum (X509.ExtensionFields (_≡ X509.ExtensionOID.AIA      )            X509.AIAFields)
             (X509.ExtensionFields (False ∘ (_∈? X509.ExtensionOID.Supported)) OctetString)))))))))))))))
  equivalent : Equivalent Rep X509.SelectExtn
  proj₁ equivalent (Sum.inj₁ x) = X509.akiextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₁ x)) = X509.skiextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) = X509.kuextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) = X509.ekuextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) = X509.bcextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) = X509.ianextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) = X509.sanextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) = X509.cpextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))) = X509.crlextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) = X509.ncextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))) = X509.pcextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))) = X509.pmextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))) = X509.inapextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))) = X509.aiaextn x
  proj₁ equivalent (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))) = X509.other x
  proj₂ equivalent (X509.akiextn x) = Sum.inj₁ x
  proj₂ equivalent (X509.skiextn x) = Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.kuextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.ekuextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.bcextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.ianextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.sanextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.cpextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.crlextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.ncextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.pcextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.pmextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.inapextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.aiaextn x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₁ $ x
  proj₂ equivalent (X509.other x) = Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ ∘ Sum.inj₂ $ x

  iso : Iso Rep X509.SelectExtn
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
  proj₂ (proj₂ iso) (X509.akiextn x) = refl
  proj₂ (proj₂ iso) (X509.skiextn x) = refl
  proj₂ (proj₂ iso) (X509.kuextn x)  = refl
  proj₂ (proj₂ iso) (X509.ekuextn x) = refl
  proj₂ (proj₂ iso) (X509.bcextn x)  = refl
  proj₂ (proj₂ iso) (X509.ianextn x) = refl
  proj₂ (proj₂ iso) (X509.sanextn x) = refl
  proj₂ (proj₂ iso) (X509.cpextn x)  = refl
  proj₂ (proj₂ iso) (X509.crlextn x) = refl
  proj₂ (proj₂ iso) (X509.ncextn x) = refl
  proj₂ (proj₂ iso) (X509.pcextn x) = refl
  proj₂ (proj₂ iso) (X509.pmextn x) = refl
  proj₂ (proj₂ iso) (X509.inapextn x) = refl
  proj₂ (proj₂ iso) (X509.aiaextn x) = refl
  proj₂ (proj₂ iso) (X509.other x)   = refl

  @0 unambiguous : Unambiguous X509.SelectExtn
  unambiguous =
    isoUnambiguous iso
      (unambiguousSum
        (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous AKI.unambiguous)) (TLV.noconfusion λ ()))
        (unambiguousSum
          (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous OctetString.unambiguous)) (TLV.noconfusion λ ()))
          (unambiguousSum
            (ExtensionFields.unambiguous ≡-unique ((TLV.unambiguous (TLV.unambiguous BitString.unambiguous))) (TLV.noconfusion λ ()))
            (unambiguousSum
              (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous OID.unambiguous TLV.nonempty TLV.nonnesting))) (TLV.noconfusion λ ()))
              (unambiguousSum
                (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous BCProps.unambiguous)) (TLV.noconfusion λ ()))
                (unambiguousSum
                  (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous GeneralName.GeneralNames.unambiguous) (TLV.noconfusion λ ()))
                  (unambiguousSum
                    (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous GeneralName.GeneralNames.unambiguous) (TLV.noconfusion λ ()))
                    (unambiguousSum
                       (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous (TLV.unambiguous PolicyInformation.unambiguous) TLV.nonempty TLV.nonnesting))) (TLV.noconfusion λ ()))
                      (unambiguousSum
                        (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous (TLV.unambiguous DistPointFieldsProps.unambiguous) TLV.nonempty TLV.nonnesting))) (TLV.noconfusion λ ()))
                        (unambiguousSum
                          (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous NCProps.unambiguous)) (TLV.noconfusion λ ()))
                          (unambiguousSum
                            (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous PCProps.unambiguous)) (TLV.noconfusion λ ()))
                            (unambiguousSum
                              (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous (SequenceOf.Bounded.unambiguous (TLV.unambiguous PMProps.unambiguous) TLV.nonempty TLV.nonnesting)) ) (TLV.noconfusion λ ()))
                              (unambiguousSum
                                (ExtensionFields.unambiguous ≡-unique (TLV.unambiguous (TLV.unambiguous λ {xs} → Int.unambiguous {xs})) (TLV.noconfusion λ ()))
                                (unambiguousSum
                                  (ExtensionFields.unambiguous ≡-unique
                                    (TLV.unambiguous
                                      (TLV.unambiguous
                                        (SequenceOf.Bounded.unambiguous
                                          (TLV.unambiguous ADProps.unambiguous) TLV.nonempty TLV.nonnesting)))
                                    (TLV.noconfusion λ ()))
                                (ExtensionFields.unambiguous ua
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
    noconfusionOIDS : ∀ {@0 A B oid₁ oid₂} → oid₁ ≢ oid₂ → NoConfusion (X509.ExtensionFields (_≡ oid₁) A) (X509.ExtensionFields (_≡ oid₂) B)
    noconfusionOIDS oid≢ {xs₁}{ys₁}{xs₂}{ys₂}++≡ (X509.mkExtensionFields{oex = oex}{cex}{ocex} extnId extnId≡ crit extension bs≡) (X509.mkExtensionFields{oex = oex₁}{cex₁}{ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
      contradiction oid≡ λ where refl → oid≢ (trans₀ (sym extnId≡) extnId≡₁)
      where
      @0 bs≡' : oex ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oex ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oex ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oex ≡ oex₁
      oid≡ = TLV.nonnesting bs≡' extnId extnId₁

    noconfusionOIDN : ∀ {@0 A B oid} → (oid ∈ X509.ExtensionOID.Supported) → NoConfusion (X509.ExtensionFields (_≡ oid) A) (X509.ExtensionFields (False ∘ (_∈? X509.ExtensionOID.Supported)) B)
    noconfusionOIDN{oid = oid} supported {xs₁} {ys₁} {xs₂} {ys₂} ++≡ (X509.mkExtensionFields {oex = _} {cex} {ocex} extnId refl crit extension bs≡) (X509.mkExtensionFields {oex = oex₁} {cex₁} {ocex₁} extnId₁ extnId≡₁ crit₁ extension₁ bs≡₁) =
      contradiction (subst (_∈ X509.ExtensionOID.Supported) oid≡ supported) (toWitnessFalse extnId≡₁)
      where
      @0 bs≡' : oid ++ cex ++ ocex ++ ys₁ ≡ oex₁ ++ cex₁ ++ ocex₁ ++ ys₂
      bs≡' = begin oid ++ cex ++ ocex ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
                   (oid ++ cex ++ ocex) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                   xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                   xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                   (oex₁ ++ cex₁ ++ ocex₁) ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
                   oex₁ ++ cex₁ ++ ocex₁ ++ ys₂ ∎

      @0 oid≡ : oid ≡ oex₁
      oid≡ = TLV.nonnesting bs≡' extnId extnId₁

    noconfusion₁ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields) (Sum _ _)
    noconfusion₁ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                            (noconfusionOIDS λ ())
                            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                              (noconfusionOIDS λ ())
                              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.AKI) AKIFields}
                                (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))))

    noconfusion₂ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields) (Sum _ _)
    noconfusion₂ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                            (noconfusionOIDS λ ())
                            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SKI) SKIFields}
                              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))))


    noconfusion₃ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.KU)  KUFields)  (Sum _ _)
    noconfusion₃ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                          (noconfusionOIDS λ ())
                          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.KU) KUFields}
                            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))))


    noconfusion₄ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields) (Sum _ _)
    noconfusion₄ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                        (noconfusionOIDS λ ())
                        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.EKU) EKUFields}
                          (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))))


    noconfusion₅ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.BC)  BCFields)  (Sum _ _)
    noconfusion₅ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
                      (noconfusionOIDS λ ())
                      (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.BC) BCFields}
                        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))))


    noconfusion₆ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields) (Sum _ _)
    noconfusion₆ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
                    (noconfusionOIDS λ ())
                    (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.IAN) IANFields}
                      (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))))


    noconfusion₇ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields) (Sum _ _)
    noconfusion₇ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
                  (noconfusionOIDS λ ())
                  (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.SAN) SANFields}
                    (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))))

    noconfusion₈ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields) (Sum _ _)
    noconfusion₈ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CPOL) X509.CertPolFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))))

    noconfusion₉ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields) (Sum _ _)
    noconfusion₉ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields}
        (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields}
          (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields}
              (noconfusionOIDS λ ())
              (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields}
                (noconfusionOIDS λ ())
                (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.CRLDIST) X509.CRLDistFields}
                  (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))))

    noconfusion₁₀ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.NC) X509.NCFields) (Sum _ _)
    noconfusion₁₀ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.NC) X509.NCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.NC) X509.NCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.NC) X509.NCFields}
            (noconfusionOIDS λ ())
            (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.NC) X509.NCFields}
              (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))))

    noconfusion₁₁ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.PC) X509.PCFields) (Sum _ _)
    noconfusion₁₁ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.PC) X509.PCFields}
        (noconfusionOIDS λ ())
        (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.PC) X509.PCFields}
          (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.PC) X509.PCFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))))

    noconfusion₁₂ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.PM) X509.PMFields) (Sum _ _)
    noconfusion₁₂ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.PM) X509.PMFields}
        (noconfusionOIDS λ ())
          (NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.PM) X509.PMFields}
            (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt)))

    noconfusion₁₃ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.INAP) X509.INAPFields) (Sum _ _)
    noconfusion₁₃ =
      NoConfusion.sumₚ{X509.ExtensionFields (_≡ X509.ExtensionOID.INAP) X509.INAPFields}
        (noconfusionOIDS λ ()) (noconfusionOIDN (toWitness{Q = _ ∈? _} tt))

    noconfusion₀ : NoConfusion (X509.ExtensionFields (_≡ X509.ExtensionOID.AIA) X509.AIAFields) (X509.ExtensionFields _ _)
    noconfusion₀ = noconfusionOIDN (toWitness{Q = _ ∈? _} tt)

    ua : Unambiguous (False ∘ (_∈? X509.ExtensionOID.Supported))
    ua = T-unique

module ExtensionsSeq where
  @0 unambiguous : Unambiguous X509.ExtensionsSeq
  unambiguous =
    TLV.unambiguous
      (SequenceOf.Bounded.unambiguous
        (TLV.unambiguous SelectExtn.unambiguous)
        TLV.nonempty TLV.nonnesting)


