{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open import Aeres.Grammar.Definitions Dig

postulate
  nonnesting : NonNesting X509.PublicKeyFields
