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


-- equivalent : Equivalent (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ]) (&ₚ X509.FieldID (&ₚ X509.Curve (&ₚ OctetString (&ₚ Int (Option Int)))))) X509.EcParamsFields
-- proj₁ equivalent (mk&ₚ refl (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡) = X509.mkEcParamsFields self fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡
-- proj₂ equivalent (X509.mkEcParamsFields self fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ sndₚ₁ bs≡) = mk&ₚ refl (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ sndₚ₁ refl) refl) refl) refl) bs≡


equivalentEcPkAlgParams : Equivalent (Sum (Sum X509.EcParams OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)) = X509.ecparams x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)) = X509.namedcurve x
proj₁ equivalentEcPkAlgParams (Aeres.Grammar.Sum.inj₂ x) = X509.implicitlyCA x
proj₂ equivalentEcPkAlgParams (X509.ecparams x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₁ x)
proj₂ equivalentEcPkAlgParams (X509.namedcurve x) = Aeres.Grammar.Sum.inj₁ (Aeres.Grammar.Sum.inj₂ x)
proj₂ equivalentEcPkAlgParams (X509.implicitlyCA x) = Aeres.Grammar.Sum.inj₂ x


<<<<<<< HEAD
@0 noconfusionEcPkAlgParams : NoConfusion (Sum (Sum X509.EcParams Generic.OID) (_≡ X509.ExpNull)) X509.EcPkAlgParams
noconfusionEcPkAlgParams = {!!}

@0 nonnestingEcPkAlgParams : NonNesting X509.EcPkAlgParams -- prove equivalent for EcPkAlgParams first, also need noconfusion
nonnestingEcPkAlgParams = equivalent-nonnesting equivalentEcPkAlgParams
  (nonnestingSum (nonnestingSum TLVprops.nonnesting TLVprops.nonnesting (TLVprops.noconfusion λ ())) (λ where _ refl refl → refl) {!!})


-- equivalent : Equivalent (&ₚ (&ₚ OctetString OctetString) (Option BitString)) X509.CurveFields

postulate
  equivalent : Equivalent (&ₚ (&ₚ (&ₚ (&ₚ (&ₚ (_≡ # 2 ∷ # 1 ∷ [ # 1 ])  X509.FieldID) X509.Curve) OctetString) Int) (Option Int))  X509.EcParamsFields
-- proj₁ equivalent (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ refl sndₚ₅ refl) sndₚ₄ refl) sndₚ₃ refl) sndₚ₂ refl) sndₚ₁ bs≡)
--   = X509.mkEcParamsFields (mkIntegerValue ( # 2 ∷ # 1 ∷ [ # 1 ]) refl) sndₚ₅ sndₚ₄ sndₚ₃ sndₚ₂ sndₚ₁
--     (begin (_ ≡⟨ bs≡ ⟩ {!!}))


-- proj₂ equivalent (X509.mkEcParamsFields version fieldID curve base order cofactor bs≡) = mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ (mk&ₚ {!!} fieldID refl) curve refl) base refl) order refl) cofactor {!!}




-- proj₁ equivalent (Aeres.Grammar.Definitions.mk&ₚ (Aeres.Grammar.Definitions.mk&ₚ{bs₁}{bs₂} fstₚ₁ sndₚ₂ refl) sndₚ₁ bs≡) = X509.mkCurveFields fstₚ₁ sndₚ₂ sndₚ₁
--   (begin (_ ≡⟨ bs≡ ⟩ ++-assoc bs₁ bs₂ _))
-- proj₂ equivalent (X509.mkCurveFields{p}{q} a b seed bs≡) = Aeres.Grammar.Definitions.mk&ₚ (Aeres.Grammar.Definitions.mk&ₚ a b refl) seed
--   (begin (_ ≡⟨ bs≡ ⟩ sym (++-assoc p q _)))
=======
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
>>>>>>> 6e97ac58367f119c43d4d0e11379d4ad56bf2646
