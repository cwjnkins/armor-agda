{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.OIDSub where

open Base256
open import Aeres.Grammar.Definitions Dig

nonempty : NonEmpty Generic.OIDSub
nonempty (Generic.mkOIDSub [] lₚ≥128 lₑ lₑ<128 leastDigs ()) refl
nonempty (Generic.mkOIDSub (x ∷ lₚ) lₚ≥128 lₑ lₑ<128 leastDigs ()) refl

postulate
  nonnesting : NonNesting Generic.OIDSub
