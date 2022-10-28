
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M71
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M72
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M8
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M9
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M10
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M11
import      Aeres.Grammar.IList
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers2 where

open Base256
open Aeres.Grammar.IList UInt8

abstract
  B2Map₂ : UTF8Trie
  B2Map₂ = fromList (trie₇₁ ++ trie₇₂ ++ trie₈ ++ trie₉ ++ trie₁₀ ++ trie₁₁)

lookupB2Map₂ : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map₂ x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₂
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂

lookupB2Map₂Flag : ∀ {@0 bs} → UTF8Char bs → Bool
lookupB2Map₂Flag x
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map₂
... | just x₁ = true
... | nothing = false
