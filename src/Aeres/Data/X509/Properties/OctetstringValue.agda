{-# OPTIONS --subtyping #-}

open import Aeres.Prelude
open import Aeres.Binary
open import Aeres.Data.X509

module Aeres.Data.X509.Properties.OctetstringValue where

open Base256
open import Aeres.Grammar.Definitions Dig


@0 unambiguous : Unambiguous Generic.OctetstringValue
unambiguous (singleton x refl) (singleton .x refl) = refl
