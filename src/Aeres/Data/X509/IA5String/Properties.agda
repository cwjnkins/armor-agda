{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.IA5String.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.IA5String.Properties where

open Aeres.Grammar.Definitions UInt8

@0 unambiguous : Unambiguous IA5StringValue
unambiguous (mkIA5StringValue self all<128) (mkIA5StringValue self all<129) =
  subst (λ x → _ ≡ mkIA5StringValue self x)
    (All.irrelevant ≤-irrelevant all<128 all<129) refl
