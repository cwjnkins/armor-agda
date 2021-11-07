{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.Properties.Time as Timeprops
open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.ValidityFields where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 nonnesting : NonNesting X509.ValidityFields
nonnesting x x₁ x₂ = foo
  where
  v2& : ∀ {bs} → X509.ValidityFields bs → (&ₚ Generic.Time Generic.Time) bs
  v2& (X509.mkValidityFields start end bs≡) = mk&ₚ start end bs≡
  foo = NonNesting&ₚ Timeprops.nonnesting Timeprops.nonnesting x (v2& x₁) (v2& x₂)

postulate
  unambiguous : Unambiguous X509.ValidityFields
