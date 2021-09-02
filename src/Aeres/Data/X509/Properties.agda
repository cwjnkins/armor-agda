open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509

module Aeres.Data.X509.Properties where

open Base256

Unambiguous : (A : List Dig → Set) → Set
Unambiguous A = ∀ {xs} → (a₁ a₂ : A xs) → a₁ ≡ a₂

NoNest : (A : List Dig → Set) → Set
NoNest A = ∀ {xs₁ ys₁ xs₂ ys₂} → xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → A xs₁ → A xs₂ → xs₁ ≡ xs₂

-- TODO: Prove
module Unambiguous where
  postulate
    Cert    : Unambiguous X509.Cert
    TBSCert : Unambiguous X509.TBSCert

module NoNest where
  postulate
    TBSCert : NoNest X509.TBSCert
    SignAlg : NoNest X509.SignAlg

-- postulate
--   unambiguous : ∀ {xs} → (c₁ c₂ : X509.Cert xs) → c₁ ≡ c₂
