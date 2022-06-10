{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.EcParamsFields          as EcPkAlgParamsProps
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.EcPkAlgFields where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
open ≡-Reasoning

equivalent : Equivalent (&ₚ (_≡ X509.PKOID.EcPk) X509.EcPkAlgParams) X509.EcPkAlgFields
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ refl (X509.ecparams x) refl) = X509.mkEcPkAlgFields self (X509.ecparams x) refl
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ refl (X509.namedcurve x) refl) = X509.mkEcPkAlgFields self (X509.namedcurve x) refl
proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ refl (X509.implicitlyCA x) refl) = X509.mkEcPkAlgFields self (X509.implicitlyCA x) refl
proj₂ equivalent (X509.mkEcPkAlgFields self (X509.ecparams x₁) refl) = Aeres.Grammar.Definitions.mk&ₚ refl (X509.ecparams x₁) refl
proj₂ equivalent (X509.mkEcPkAlgFields self (X509.namedcurve x₁) refl) = Aeres.Grammar.Definitions.mk&ₚ refl (X509.namedcurve x₁) refl
proj₂ equivalent (X509.mkEcPkAlgFields self (X509.implicitlyCA x₁) refl) = Aeres.Grammar.Definitions.mk&ₚ refl (X509.implicitlyCA x₁) refl


@0 nonnesting : NonNesting X509.EcPkAlgFields
nonnesting = equivalent-nonnesting equivalent (NonNesting&ₚ (λ where _ refl refl → refl) EcPkAlgParamsProps.nonnestingEcPkAlgParams)

postulate
  @0 unambiguous : Unambiguous X509.EcPkAlgFields
