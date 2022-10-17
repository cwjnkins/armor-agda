
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers1
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers2
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers3

import      Aeres.Grammar.IList
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers where

open Base256
open Aeres.Grammar.IList UInt8

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupB2Map₁ x
... | ─ .[] , nil = {!!}
... | fst , cons x₁ = {!fst, cons x₁!}
