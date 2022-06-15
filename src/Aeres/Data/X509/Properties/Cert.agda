{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Cert where

open Base256
open Aeres.Grammar.Definitions UInt8

instance
  postulate
    CertEq : Eq (Exists─ (List Dig) X509.Cert)
