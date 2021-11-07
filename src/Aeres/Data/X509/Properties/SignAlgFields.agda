{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Prelude

module Aeres.Data.X509.Properties.SignAlgFields where

open Base256
open import Aeres.Grammar.Definitions Dig

postulate
  unambiguous : Unambiguous X509.SignAlgFields
