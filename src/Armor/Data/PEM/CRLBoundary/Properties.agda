{-# OPTIONS --erasure #-}
open import Armor.Data.Base64.TCB
open import Armor.Data.PEM.CRLBoundary.TCB
open import Armor.Data.PEM.RFC5234
import      Armor.Grammar.Definitions
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.PEM.CRLBoundary.Properties where

open Armor.Grammar.Definitions Char
open Armor.Grammar.Seq         Char

Rep : (ctrl : String) → @0 List Char → Set
Rep ctrl = &ₚ (λ x → Erased (x ≡ (String.toList $ "-----" String.++ ctrl String.++ " X509 CRL-----")))
              (λ x → Erased (EOL x))

equiv : ∀ ctrl → Equivalent (Rep ctrl) (CRLBoundary ctrl)
proj₁ (equiv ctrl) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCRLBoundary (¡ fstₚ₁) (¡ sndₚ₁) bs≡
proj₂ (equiv ctrl) (mkCRLBoundary begin eol bs≡) = mk&ₚ (─ begin) (─ eol) bs≡

iso : ∀ ctrl → Iso (Rep ctrl) (CRLBoundary ctrl)
proj₁ (iso ctrl) = equiv ctrl
proj₁ (proj₂ (iso ctrl)) (mk&ₚ (─ refl) (─ l) bs≡) = refl
proj₂ (proj₂ (iso ctrl)) (mkCRLBoundary refl eol bs≡) = refl

@0 noOverlapTextEOL
  : ∀ {ctrl}
    → NoOverlap
        (λ x → Erased (x ≡ (String.toList $ "-----" String.++ ctrl String.++ " X509 CRL-----")))
        (λ x → Erased (EOL x))
noOverlapTextEOL ws xs₁ ys₁ xs₂ ys₂ x x₁ x₂ =
  inj₁ (++-cancelˡ ws _ _
    (begin
      (ws ++ xs₁ ≡⟨ (¡ x₁) ⟩
      _ ≡⟨ sym (¡ x₂) ⟩
      ws ≡⟨ sym (++-identityʳ ws) ⟩
      ws ++ [] ∎)))
  where
  open ≡-Reasoning

@0 unambiguous : (ctrl : String) → Unambiguous (CRLBoundary ctrl)
unambiguous ctrl =
  Iso.unambiguous (iso ctrl)
    (Seq.unambiguousNO (erased-unique ≡-unique) (erased-unique RFC5234.EOL.unambiguous) (noOverlapTextEOL{ctrl}))
