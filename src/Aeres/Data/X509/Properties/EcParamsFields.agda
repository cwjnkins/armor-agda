{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.TLV            as TLVprops
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
