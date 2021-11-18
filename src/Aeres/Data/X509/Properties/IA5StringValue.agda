{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Grammar.Definitions
open import Aeres.Data.X509
import      Aeres.Data.X509.Properties.OctetstringValue as OSProps
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Properties.IA5StringValue where

open Base256
open Aeres.Grammar.Definitions Dig

@0 unambiguous : Unambiguous X509.IA5StringValue
unambiguous (X509.mkIA5StringValue self all<128) (X509.mkIA5StringValue self all<129) =
  subst (λ x → _ ≡ X509.mkIA5StringValue self x)
    (All.irrelevant ≤-irrelevant all<128 all<129) refl
