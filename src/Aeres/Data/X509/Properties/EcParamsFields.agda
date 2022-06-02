{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.EcParamsFields where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Sum         Dig
open ≡-Reasoning


equivalent : Equivalent (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ]) (&ₚ X509.FieldID (&ₚ X509.Curve (&ₚ OctetString (&ₚ Int (Option Int)))))) X509.EcParamsFields
proj₁ equivalent (mk&ₚ refl (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡) = X509.mkEcParamsFields self fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡
proj₂ equivalent (X509.mkEcParamsFields self fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡) = mk&ₚ refl (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡


equivalentEcPkAlgParams : Equivalent (Sum (Sum X509.EcParams OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = X509.ecparams x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = X509.namedcurve x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₂ x) = X509.implicitlyCA x
proj₂ equivalentEcPkAlgParams (X509.ecparams x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)
proj₂ equivalentEcPkAlgParams (X509.namedcurve x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)
proj₂ equivalentEcPkAlgParams (X509.implicitlyCA x) = Aeres.Grammar.Sum.inj₂ x


postulate
  @0 noconfusionEcPkAlgParams : NoConfusion (Sum (Sum X509.EcParams OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams

  @0 nonnestingEcPkAlgParams : NonNesting X509.EcPkAlgParams -- prove equivalent for EcPkAlgParams first, also need noconfusion
-- nonnestingEcPkAlgParams = equivalent-nonnesting equivalentEcPkAlgParams
--   (nonnestingSum (nonnestingSum TLVprops.nonnesting TLVprops.nonnesting (TLVprops.noconfusion λ ())) (λ where _ refl refl → refl) {!!})
