{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.TLV as TLVprops
import      Aeres.Data.X509.Properties.OctetstringValue as OSprops
import      Aeres.Data.X509.Properties.OID as OIDprops
import      Aeres.Data.X509.Properties.CurveFields as CurveFieldsprops
import      Aeres.Data.X509.Properties.Primitives as Primprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.EcParamsFields where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open ≡-Reasoning



postulate
  equivalent : Equivalent (&ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  X509.FieldID) X509.Curve) OctetString) Int) (Option Int)) X509.EcParamsFields

@0 iso : Iso (&ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  X509.FieldID) X509.Curve) OctetString) Int) (Option Int)) X509.EcParamsFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl sndₚ₅ refl) sndₚ₄ refl) sndₚ₃ refl) sndₚ₂ refl) sndₚ₁ bs≡) = {!!}
proj₂ (proj₂ iso) (X509.mkEcParamsFields version fieldID curve base order cofactor bs≡) = {!!}


@0 unambiguous : Unambiguous X509.EcParamsFields
unambiguous = isoUnambiguous iso
  (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (unambiguous&ₚ (λ where refl refl → refl) (λ where _ refl refl → refl)
    (TLVprops.unambiguous OSprops.unambiguous))
      (NonNesting&ₚ (λ where _ refl refl → refl) TLVprops.nonnesting)
    (TLVprops.unambiguous CurveFieldsprops.unambiguous))
      (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLVprops.nonnesting) TLVprops.nonnesting)
    (TLVprops.unambiguous OSprops.unambiguous))
      (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLVprops.nonnesting) TLVprops.nonnesting) TLVprops.nonnesting)
    (TLVprops.unambiguous λ {xs} → Primprops.IntegerValue.unambiguous{xs}))
      (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (NonNesting&ₚ (λ where _ refl refl → refl) TLVprops.nonnesting) TLVprops.nonnesting) TLVprops.nonnesting) TLVprops.nonnesting)
    {!!})

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
      (nonnestingSum TLVprops.nonnesting TLVprops.nonnesting
        (TLVprops.noconfusion (λ ())))
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
      (unambiguousSum (TLVprops.unambiguous unambiguous) (OIDprops.unambiguous) (TLVprops.noconfusion (λ ())))
      (λ where refl refl → refl) {!!})
