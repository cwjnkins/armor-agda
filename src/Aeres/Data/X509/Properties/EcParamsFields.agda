{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Serializer
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.OctetstringValue  as OSProps
import      Aeres.Data.X509.Properties.CurveFields       as CurveFieldsProps
open import Aeres.Data.X690-DER
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.EcParamsFields where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Serializer  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning


Rep = &ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  X509.FieldID) X509.Curve) OctetString) Int) (Option Int)

private
  abstract
    @0 equiv≡₁ : ∀ {@0 bs₂ bs₃ bs₄ bs₅ bs₆} → (@0 xs : _)
               → xs ≡ (# 2 ∷ # 1 ∷ # 1 ∷ (((bs₂ ++ bs₃) ++ bs₄) ++ bs₅) ++ bs₆)
               → _≡_{A = List UInt8}
                   xs
                   (# 2 ∷ # 1 ∷ # 1 ∷ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆)
    equiv≡₁ xs xs≡ = trans xs≡ ((cong (λ x → # 2 ∷ # 1 ∷ # 1 ∷ x) (solve (++-monoid UInt8))))

    @0 equiv≡₂ : ∀ {@0 bs₂ bs₃ bs₄ bs₅ bs₆} → (@0 xs : _)
                 → xs ≡ (# 2 ∷ # 1 ∷ # 1 ∷ bs₂ ++ bs₃ ++ bs₄ ++ bs₅ ++ bs₆)
                 → _≡_{A = List UInt8}
                     xs
                   (# 2 ∷ # 1 ∷ # 1 ∷ (((bs₂ ++ bs₃) ++ bs₄) ++ bs₅) ++ bs₆)
    equiv≡₂ xs xs≡ = trans xs≡ (cong (λ x → # 2 ∷ # 1 ∷ # 1 ∷ x) (solve (++-monoid UInt8)))

equivalent : Equivalent Rep X509.EcParamsFields
proj₁ equivalent{xs} (mk&ₚ{bs₂ = bs₆} (mk&ₚ{bs₂ = bs₅} (mk&ₚ{bs₂ = bs₄} (mk&ₚ{bs₂ = bs₃} (mk&ₚ{bs₂ = bs₂} refl fieldID refl) curve refl) base refl) order refl) cofactor bs≡) =
  X509.mkEcParamsFields self fieldID curve base order cofactor (equiv≡₁{bs₂}{bs₃} xs bs≡)
proj₂ equivalent{xs} (X509.mkEcParamsFields{f}{c}{b}{o}{cf} self fieldID curve base order cofactor bs≡) =
  mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor
    (equiv≡₂{f}{c} xs bs≡)

iso : Iso (&ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  X509.FieldID) X509.Curve) OctetString) Int) (Option Int)) X509.EcParamsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso){xs} a@(mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor refl) = ‼
  subst₀ (λ e → mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl fieldID refl) curve refl) base refl) order refl) cofactor e ≡ a) (≡-unique refl _) refl
proj₂ (proj₂ iso) a@(X509.mkEcParamsFields self fieldID curve base order cofactor refl) =
  subst₀ (λ e → X509.mkEcParamsFields self fieldID curve base order cofactor e ≡ a)
    (‼ (≡-unique refl _))
    refl

@0 unambiguous : Unambiguous X509.EcParamsFields
unambiguous = isoUnambiguous iso
  (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (λ where refl refl → refl) (λ where _ refl refl → refl)
    (TLV.unambiguous OSProps.unambiguous))
      (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting)
    (TLV.unambiguous CurveFieldsProps.unambiguous))
      (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting)
    (TLV.unambiguous OSProps.unambiguous))
      (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
    (TLV.unambiguous λ {xs} → Int.unambiguous{xs}))
      (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting) TLV.nonnesting)
    (Unambiguous.option₁ (TLV.unambiguous λ {xs} → Int.unambiguous{xs}) TLV.nonempty))

@0 equivalentEcPkAlgParams : Equivalent (Sum (Sum X509.EcParams OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = X509.ecparams x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = X509.namedcurve x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₂ x) = X509.implicitlyCA x
proj₂ equivalentEcPkAlgParams (X509.ecparams x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)
proj₂ equivalentEcPkAlgParams (X509.namedcurve x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)
proj₂ equivalentEcPkAlgParams (X509.implicitlyCA x) = Aeres.Grammar.Sum.inj₂ x


@0 nonnestingEcPkAlgParams : NonNesting X509.EcPkAlgParams
nonnestingEcPkAlgParams =
  equivalent-nonnesting equivalentEcPkAlgParams
    (nonnestingSum
      (nonnestingSum TLV.nonnesting TLV.nonnesting
        (TLV.noconfusion (λ ())))
      (λ where _ refl refl → refl)
      (symNoConfusion{A = _≡ X509.ExpNull}{B = Sum X509.EcParams OID}
        (NoConfusion.sumₚ{A = _≡ X509.ExpNull}{B = X509.EcParams}{C = OID}
          (λ where
            {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ refl (mkTLV{l = l}{v} len val len≡ bs≡) →
              contradiction{P = # Tag.Null ≡ # Tag.Sequence}
                (∷-injectiveˡ (begin X509.ExpNull ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                                     xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡ ⟩
                                     (Tag.Sequence ∷ l ++ v) ++ ys₂ ∎))
                (λ ()))
          λ where
            {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ refl (mkTLV{l = l}{v} len val len≡ bs≡) →
              contradiction{P = # Tag.Null ≡ # Tag.ObjectIdentifier}
                (∷-injectiveˡ (begin X509.ExpNull ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
                                     xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡ ⟩
                                     (# Tag.ObjectIdentifier ∷ l ++ v) ++ ys₂ ∎))
                λ ())))

@0 isoEcPkAlgParams : Iso  (Sum (Sum X509.EcParams OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams
proj₁ (proj₁ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = X509.ecparams x
proj₁ (proj₁ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = X509.namedcurve x
proj₁ (proj₁ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₂ x) = X509.implicitlyCA x
proj₂ (proj₁ isoEcPkAlgParams) (X509.ecparams x) = Sum.inj₁ (Sum.inj₁ x)
proj₂ (proj₁ isoEcPkAlgParams) (X509.namedcurve x) = Sum.inj₁ (Sum.inj₂ x)
proj₂ (proj₁ isoEcPkAlgParams) (X509.implicitlyCA x) = Sum.inj₂ x
proj₁ (proj₂ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = refl
proj₁ (proj₂ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = refl
proj₁ (proj₂ isoEcPkAlgParams) (Aeres.Grammar.Sum.inj₂ x) = refl
proj₂ (proj₂ isoEcPkAlgParams) (X509.ecparams x) = refl
proj₂ (proj₂ isoEcPkAlgParams) (X509.namedcurve x) = refl
proj₂ (proj₂ isoEcPkAlgParams) (X509.implicitlyCA x) = refl


@0 unambiguousEcPkAlgParams : Unambiguous X509.EcPkAlgParams
unambiguousEcPkAlgParams =
  isoUnambiguous isoEcPkAlgParams
    (unambiguousSum
      (unambiguousSum (TLV.unambiguous unambiguous) (OID.unambiguous) (TLV.noconfusion (λ ())))
      (λ where refl refl → refl)
      (symNoConfusion{A = _≡ X509.ExpNull}{B = Sum _ _}
        (NoConfusion.sumₚ{A = _≡ X509.ExpNull}
          (λ where
            {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ refl (mkTLV len val len≡ bs≡) →
              contradiction{P = Tag.Sequence ≡ Tag.Null}
                (∷-injectiveˡ (trans (cong (_++ ys₂) (sym bs≡)) (sym xs₁++ys₁≡xs₂++ys₂)))
                λ ())
           λ where
             {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ refl (mkTLV{l = l}{v} len val len≡ bs≡) →
               contradiction{P = Tag.ObjectIdentifier ≡ Tag.Null}
                 (∷-injectiveˡ
                   (begin (Tag.ObjectIdentifier ∷ l ++ v) ++ ys₂ ≡⟨ cong (_++ ys₂) (sym bs≡) ⟩
                          xs₂ ++ ys₂ ≡⟨ sym xs₁++ys₁≡xs₂++ys₂ ⟩
                          xs₁ ++ ys₁ ∎))
                 (λ ()))))

serialize : Serializer X509.EcParamsFields
serialize =
  serializeEquivalent equivalent
    (serialize&ₚ
      (serialize&ₚ
        (serialize&ₚ
          (serialize&ₚ
            (serialize&ₚ
              (λ where refl → self)
              (TLV.serialize id))
            (TLV.serialize CurveFieldsProps.serialize))
          (TLV.serialize id))
        Int.serialize)
      (Option.serialize Int.serialize))
