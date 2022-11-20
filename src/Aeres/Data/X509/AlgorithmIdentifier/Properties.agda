{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.AlgorithmIdentifier.Properties
  (@0 P : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set)
  where

open Aeres.Grammar.Definitions UInt8

Rep : @0 List UInt8 → Set
Rep = &ₚᵈ OID λ bs → P {bs}

equiv : Equivalent Rep (AlgorithmIdentifierFields P)
proj₁ equiv (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkAlgIDFields fstₚ₁ sndₚ₁ bs≡
proj₂ equiv (mkAlgIDFields algOID param bs≡) = mk&ₚ algOID param bs≡

iso : Iso Rep (AlgorithmIdentifierFields P)
proj₁ iso = equiv
proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = refl
proj₂ (proj₂ iso) (mkAlgIDFields algOID param bs≡) = refl

@0 unambiguous
  : (∀ {@0 bs} → (o : OID bs) → Unambiguous (P o))
    → Unambiguous (AlgorithmIdentifierFields P)
unambiguous ua =
  isoUnambiguous iso
    (unambiguous&ₚᵈ OID.unambiguous TLV.nonnesting ua)

@0 noConfusionParam
  : {@0 P' : {@0 bs : List UInt8} → OID bs → @0 List UInt8 → Set}
    → (∀ {@0 bs bs' bs“} → (o : OID bs) → P o bs' → ¬ P' o bs“)
    → NoConfusion (AlgorithmIdentifier P) (AlgorithmIdentifier P')
noConfusionParam{P'} excl =
  TLV.noconfusionVal λ where
   {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkAlgIDFields{bs₁}{p} o para bs≡) (mkAlgIDFields{bs₁'}{p'} o' para' bs'≡) →
     let
       @0 ++≡ : bs₁ ++ p ++ ys₁ ≡ bs₁' ++ p' ++ ys₂
       ++≡ = begin
         bs₁ ++ p ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
         (bs₁ ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
         xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
         xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs'≡ ⟩
         (bs₁' ++ p') ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
         bs₁' ++ p' ++ ys₂ ∎
  
       @0 bs₁≡ : bs₁ ≡ bs₁'
       bs₁≡ = TLV.nonnesting ++≡ o o'
  
       o≋o' : _≋_{OID} o o'
       o≋o' = mk≋ bs₁≡ (OID.unambiguous _ o')
     in
     contradiction
       (case o≋o' ret (const _) of λ where
         ≋-refl → para')
       (excl o para)
  where
  open ≡-Reasoning

eq≋ : (∀ {@0 bs} → (o : OID bs) → Eq≋ (P o)) → Eq≋ (AlgorithmIdentifierFields P)
eq≋ eqP = Eq⇒Eq≋ (isoEq iso (eq&ₚᵈ it λ a → Eq≋⇒Eq (eqP a)))
