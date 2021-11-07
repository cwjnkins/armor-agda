{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
import Aeres.Data.X509.Properties.Length as LengthProps
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.Seq where

open Base256
open import Aeres.Grammar.Definitions Dig

postulate
  unambiguous : ∀ {@0 A} → Unambiguous A → Unambiguous (Generic.SeqElems A)

