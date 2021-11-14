{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CertFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

equivalent : Equivalent (&ₚ X509.TBSCert (&ₚ X509.SignAlg Generic.Bitstring)) X509.CertFields
proj₁ equivalent (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ sndₚ₁ refl) bs≡) = X509.mkCertFields fstₚ₁ fstₚ₂ sndₚ₁ bs≡
proj₂ equivalent (X509.mkCertFields tbs signAlg signature bs≡) = mk&ₚ tbs (mk&ₚ signAlg signature refl) bs≡
