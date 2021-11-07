{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.RDNATVFields where

open Base256
open import Aeres.Grammar.Definitions Dig
open ≡-Reasoning

postulate
  unambiguous : Unambiguous X509.RDNATVFields
