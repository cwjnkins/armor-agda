{-# OPTIONS --subtyping #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Data.X509.Properties.TLV            as TLVprops
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PkAlg where

open Base256
open Aeres.Grammar.Definitions Dig
open import Aeres.Grammar.Sum Dig
open ≡-Reasoning

postulate
 @0 nonnesting : NonNesting X509.PkAlg
