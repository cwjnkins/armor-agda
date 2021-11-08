{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
-- open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.CertFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

postulate
  equivalent : Equivalent (&ₚ X509.TBSCert (&ₚ X509.SignAlg Generic.Bitstring)) X509.CertFields
