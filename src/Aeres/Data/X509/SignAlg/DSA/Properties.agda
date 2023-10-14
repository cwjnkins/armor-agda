{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA.TCB
open import Aeres.Data.X690-DER.Null
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.SignAlg.DSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module DSA-Like where
  @0 unambiguous : ∀ {@0 bs} → (o : OIDValue bs) → Unambiguous (DSA-Like o)
  unambiguous o =
    TLV.unambiguous
      (DefinedByOID.unambiguous
        _
        λ o' →
          Parallel.unambiguous×ₚ
            (TLV.unambiguous (λ where refl refl → refl))
            λ where ≋-refl ≋-refl → refl)

  @0 noConfusion : ∀ {@0 bs₁ bs₂} → (o₁ : OIDValue bs₁) (o₂ : OIDValue bs₂)
                → {t : False (o₁ ≋? o₂)}
                → NoConfusion (DSA-Like o₁) (DSA-Like o₂)
  noConfusion o₁ o₂ {t} =
    TLV.noconfusionVal λ where
     {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkOIDDefinedFields{bs₁}{p} o (mk×ₚ _ o≡) bs≡) (mkOIDDefinedFields{bs₁'}{p'} o' (mk×ₚ _ o'≡) bs'≡) →
       let
         @0 ++≡ : Erased (bs₁ ++ p ++ ys₁ ≡ bs₁' ++ p' ++ ys₂)
         ++≡ = ─ (begin
           bs₁ ++ p ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
           (bs₁ ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
           xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
           xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs'≡ ⟩
           (bs₁' ++ p') ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
           bs₁' ++ p' ++ ys₂ ∎)

         @0 bs₁≡ : Erased (bs₁ ≡ bs₁')
         bs₁≡ = ─ TLV.nosubstrings (¡ ++≡) o o'

         @0 o≋o' : _≋_{OID} o o'
         o≋o' = mk≋ (¡ bs₁≡) (OID.unambiguous _ o')
       in
       contradiction
         (trans≋ (sym≋ o≡) (trans≋ (cong≋ (λ x → -, TLV.val x) o≋o') o'≡))
         (toWitnessFalse t)
    where
    open ≡-Reasoning

  @0 nonmalleableParam : ∀ {@0 bs} (o : OIDValue bs) → NonMalleable₁ (RawDSALikeParams o)
  nonmalleableParam o p₁ p₂ eq =
    Parallel.nonmalleable₁ RawNull Null.nonmalleable (λ where _ ≋-refl ≋-refl → refl)
      p₁ p₂ eq

  @0 nonmalleable : ∀ {@0 bs} (o : OIDValue bs) → NonMalleable (RawDSALike o)
  nonmalleable o =
    DefinedByOID.nonmalleable (DSA-Like-Params o) _
      (λ {bs} {o'} → nonmalleableParam o{bs}{o'})


@0 unambiguous : Unambiguous Supported
unambiguous =
  Sum.unambiguous (DSA-Like.unambiguous _)
    (Sum.unambiguous (DSA-Like.unambiguous _)
      (DSA-Like.unambiguous _)
      (DSA-Like.noConfusion _ _))
    (Sum.noconfusion{A = SHA1}
      (DSA-Like.noConfusion _ _)
      (DSA-Like.noConfusion _ _))

@0 nonmalleable : NonMalleable RawSupported
nonmalleable =
   Sum.nonmalleable (DSA-Like.nonmalleable OIDs.DSA.SHA1)
  (Sum.nonmalleable (DSA-Like.nonmalleable OIDs.DSA.SHA224)
                    (DSA-Like.nonmalleable OIDs.DSA.SHA256))
