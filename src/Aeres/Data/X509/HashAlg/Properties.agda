{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
import      Aeres.Data.X509.HashAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.HashAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

module SHA-Like where

  noConfusion : ∀ {@0 bs₁ bs₂} → (o₁ : OIDValue bs₁) (o₂ : OIDValue bs₂)
                → {t : False (o₁ ≋? o₂)}
                → NoConfusion (SHA-Like o₁) (SHA-Like o₂)
  noConfusion o₁ o₂ {t}{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂
    (mkTLV{l}{v}   len  (mkAlgIDFields{bs₁}{p}   o  (mk×ₚ _ o≡  refl) refl) len≡  bs≡)
    (mkTLV{l'}{v'} len₁ (mkAlgIDFields{bs₁'}{p'} o' (mk×ₚ _ o'≡ refl) refl) len≡₁ bs≡₁) =
    contradiction
      (trans≋ (sym≋ o≡) (trans≋ (cong≋ (λ x → -, TLV.val x) o≋o') o'≡))
      (toWitnessFalse t)
    where
    open ≡-Reasoning

    @0 ++≡' : l ++ v ++ ys₁ ≡ l' ++ v' ++ ys₂
    ++≡' = ∷-injectiveʳ (begin
      Tag.Sequence ∷ l ++ v ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (sym (++-assoc l v ys₁)) ⟩
      (Tag.Sequence ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
      xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
      xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
      (Tag.Sequence ∷ l' ++ v') ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (++-assoc l' v' ys₂) ⟩
      Tag.Sequence ∷ l' ++ v' ++ ys₂ ∎)

    @0 l≡ : l ≡ l'
    l≡ = Length.nonnesting ++≡' len len₁

    @0 ++≡“ : bs₁ ++ p ++ ys₁ ≡ bs₁' ++ p' ++ ys₂
    ++≡“ = Lemmas.++-cancel≡ˡ _ _ l≡
      (begin l ++ bs₁ ++ p ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
             l ++ v ++ ys₁ ≡⟨ ++≡' ⟩
             l' ++ v' ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
             l' ++ bs₁' ++ p' ++ ys₂ ∎)

    @0 bs₁≡ : bs₁ ≡ bs₁'
    bs₁≡ = TLV.nonnesting ++≡“ o o'

    @0 o≋o' : _≋_{OID} o o'
    o≋o' = mk≋ bs₁≡ (OID.unambiguous _ o')
