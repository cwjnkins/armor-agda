
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.Serializer
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M1
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M2
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M3
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M4
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M5
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M6
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M71
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M72
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M8
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M9
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M10
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M11
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M12
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M13
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M141
open import Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M142
import      Aeres.Grammar.IList
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers where

open Base256
open Aeres.Grammar.IList UInt8

B2Map : UTF8Trie
B2Map = fromList (trie₁ ++ trie₂ ++ trie₃ ++ trie₄ ++ trie₅ ++ trie₆ ++ trie₇₁ ++ trie₇₂ ++ trie₈ ++ trie₉ ++ trie₁₀ ++ trie₁₁ ++ trie₁₂ ++ trie₁₃ ++ trie₁₄₁ ++ trie₁₄₂)

-- B2Map : UTF8Trie
-- B2Map = fromList (trie₁ ++ trie₂)

lookupB2Map : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
lookupB2Map x 
  with lookupUTF8Trie (serializeUTF8Char' x) B2Map
... | nothing = _ , (cons (mkIListCons x nil refl))
... | just x₁
  with x₁
... | this x₂ = x₂
... | that x₃ = _ , (cons (mkIListCons x nil refl))
... | these x₂ x₃ = x₂
