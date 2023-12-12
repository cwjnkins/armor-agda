{-# OPTIONS --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.Unicode
open import Aeres.Data.Unicode.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers1
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers2
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers3

import      Aeres.Grammar.IList
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers where

open Aeres.Grammar.IList UInt8

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupB2Map₁Flag x
... | true = lookupB2Map₁ x
... | false
  with lookupB2Map₂Flag x
... | true = lookupB2Map₂ x
... | false
  with lookupB2Map₃Flag x
... | true = lookupB2Map₃ x
... | false = _ , (cons (mkIListCons x nil refl))
