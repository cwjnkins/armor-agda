{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.Null
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.HashAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Option      UInt8

module SHA-Like where

  @0 noConfusion : ∀ {@0 bs₁ bs₂} → (o₁ : OIDValue bs₁) (o₂ : OIDValue bs₂)
                → {t : False (o₁ ≋? o₂)}
                → NoConfusion (SHA-Like o₁) (SHA-Like o₂)
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

  @0 unambiguous : ∀ {@0 bs} → (o : OIDValue bs) → Unambiguous (SHA-Like o)
  unambiguous o =
    TLV.unambiguous
      (DefinedByOID.unambiguous
        _
        (λ o₁ →
         Parallel.unambiguous×ₚ
            (Option.unambiguous
              (TLV.unambiguous (λ where refl refl → refl))
              TLV.nonempty)
            (λ where ≋-refl ≋-refl → refl)))

  @0 nonmalleableParam : ∀ {bs} (o : OIDValue bs) → NonMalleable₁ (RawSHALikeParam o)
  nonmalleableParam o p₁ p₂ eq =
    Parallel.nonmalleable₁
      (RawOption RawNull)
      (Option.nonmalleable _ Null.nonmalleable)
      (λ where _ ≋-refl ≋-refl → refl)
      p₁ p₂ eq

  @0 nonmalleable : ∀ {bs} (o : OIDValue bs) → NonMalleable (RawSHALike o)
  nonmalleable o = DefinedByOID.nonmalleable (SHA-Like-Param o) _ λ {bs} {a} → nonmalleableParam o {bs}{a}

  instance
    eq≋ : ∀ {@0 bs} → {o : OIDValue bs} → Eq≋ (DefinedByOIDFields (SHA-Like-Param o))
    eq≋ =
      DefinedByOID.eq≋ _
        λ o' →
          Parallel.eq≋Σₚ it
            λ _ → record { _≟_ = λ where ≋-refl ≋-refl → yes refl }

    eq : ∀ {@0 bs} → {o : OIDValue bs} → Eq (Exists─ _ (DefinedByOIDFields (SHA-Like-Param o)))
    eq = Eq≋⇒Eq eq≋
