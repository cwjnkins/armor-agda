{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.TBSCertFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

equivalent : Equivalent
               (&ₚ (&ₚ (Option X509.Version) Generic.Int)
               (&ₚ X509.SignAlg
               (&ₚ X509.RDNSeq
               (&ₚ X509.Validity
               (&ₚ X509.RDNSeq
               (&ₚ X509.PublicKey
               (&ₚ (Option X509.IssUID)
               (&ₚ (Option X509.SubUID) (Option X509.Extensions)))))))))
               X509.TBSCertFields
proj₁ equivalent (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ (mk&ₚ fstₚ₆ (mk&ₚ fstₚ₇ (mk&ₚ fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) refl) =
  X509.mkTBSCertFields fstₚ₁ sndₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ fstₚ₆ fstₚ₇ fstₚ₈ sndₚ₂
    (solve (++-monoid Dig))
proj₂ equivalent (X509.mkTBSCertFields version serial signAlg issuer validity subject pk issuerUID subjectUID extensions refl) =
  mk&ₚ (mk&ₚ version serial refl) (mk&ₚ signAlg (mk&ₚ issuer (mk&ₚ validity (mk&ₚ subject (mk&ₚ pk (mk&ₚ issuerUID (mk&ₚ subjectUID extensions refl) refl) refl) refl) refl) refl) refl)
    (solve (++-monoid Dig))
