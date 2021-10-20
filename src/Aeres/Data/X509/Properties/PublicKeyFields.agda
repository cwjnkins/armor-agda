{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.PublicKeyFields where

open Base256
open import Aeres.Grammar.Definitions Dig

@0 nonnesting : NonNesting X509.PublicKeyFields
nonnesting {xs₁ = xs₁} {xs₂ = xs₂} x (X509.mkPublicKeyFields signalg pubkey bs≡) (X509.mkPublicKeyFields signalg₁ pubkey₁ bs≡₁)
  with Lemmas.length-++-≡ xs₁ _ xs₂ _ x {!!}
... | foo = {!!}
