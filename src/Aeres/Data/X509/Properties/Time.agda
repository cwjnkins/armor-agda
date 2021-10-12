{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Time where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.Time
nonempty (Generic.utctm ()) refl
nonempty (Generic.gentm ()) refl
