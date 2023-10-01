{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.CertBoundary.TCB
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.PEM.CertBoundary.Properties where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.Seq         Char

Rep : (ctrl : String) → @0 List Char → Set
Rep ctrl = &ₚ (_≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----"))
              (Erased ∘ EOL)

equiv : ∀ ctrl → Equivalent (Rep ctrl) (CertBoundary ctrl)
proj₁ (equiv ctrl) (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkCertBoundary fstₚ₁ (¡ sndₚ₁) bs≡
proj₂ (equiv ctrl) (mkCertBoundary begin eol bs≡) = mk&ₚ (‼ begin) (─ eol) bs≡

noOverlapTextEOL
  : ∀ {ctrl}
    → NoOverlap
        (_≡ (String.toList $ "-----" String.++ ctrl String.++ " CERTIFICATE-----"))
        EOL
noOverlapTextEOL ws xs₁ ys₁ xs₂ ys₂ x x₁ x₂ =
  inj₁ (++-cancelˡ ws
    (begin
      (ws ++ xs₁ ≡⟨ x₁ ⟩
      _ ≡⟨ sym x₂ ⟩
      ws ≡⟨ sym (++-identityʳ ws) ⟩
      ws ++ [] ∎)))
  where
  open ≡-Reasoning
