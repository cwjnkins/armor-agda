{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.EcPkAlg.Params.Properties as Params
open import Aeres.Data.X509.EcPkAlg.Params.TCB
open import Aeres.Data.X509.EcPkAlg.TCB
import      Aeres.Data.X509.PkOID as PkOID
import      Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.EcPkAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open import Aeres.Grammar.Sum UInt8
open ≡-Reasoning

equivalent : Equivalent (&ₚ (_≡ PkOID.EcPk) EcPkAlgParams) EcPkAlgFields
proj₁ equivalent (mk&ₚ refl (ecparams x) refl)     = mkEcPkAlgFields self (ecparams x) refl
proj₁ equivalent (mk&ₚ refl (namedcurve x) refl)   = mkEcPkAlgFields self (namedcurve x) refl
proj₁ equivalent (mk&ₚ refl (implicitlyCA x) refl) = mkEcPkAlgFields self (implicitlyCA x) refl
proj₂ equivalent (mkEcPkAlgFields self (ecparams x₁) refl)     = mk&ₚ refl (ecparams x₁) refl
proj₂ equivalent (mkEcPkAlgFields self (namedcurve x₁) refl)   = mk&ₚ refl (namedcurve x₁) refl
proj₂ equivalent (mkEcPkAlgFields self (implicitlyCA x₁) refl) = mk&ₚ refl (implicitlyCA x₁) refl


@0 nonnesting : NonNesting EcPkAlgFields
nonnesting =
  equivalent-nonnesting equivalent
    (NonNesting&ₚ (λ where _ refl refl → refl) Params.nonnesting)


@0 iso : Iso (&ₚ (_≡ PkOID.EcPk) EcPkAlgParams) EcPkAlgFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ refl (ecparams x) refl) = refl
proj₁ (proj₂ iso) (mk&ₚ refl (namedcurve x) refl) = refl
proj₁ (proj₂ iso) (mk&ₚ refl (implicitlyCA x) refl) = refl
proj₂ (proj₂ iso) (mkEcPkAlgFields self (ecparams x) refl) = refl
proj₂ (proj₂ iso) (mkEcPkAlgFields self (namedcurve x) refl) = refl
proj₂ (proj₂ iso) (mkEcPkAlgFields self (implicitlyCA x) refl) = refl

@0 unambiguous : Unambiguous EcPkAlgFields
unambiguous =
  isoUnambiguous iso
    (unambiguous&ₚ (λ where refl refl  → refl) (λ where _ refl refl → refl)
      Params.unambiguous)
