
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

import      Aeres.Grammar.IList
open import Data.These.Base

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.Helpers1 where

open Base256
open Aeres.Grammar.IList UInt8


-- B2Map₁ : UTF8Trie
-- B2Map₁ = fromList (trie₁ ++ trie₂ ++ trie₃ ++ trie₄ ++ trie₅ ++ trie₆)

-- lookupB2Map₁ : ∀ {@0 bs} → UTF8Char bs → Exists─ (List UInt8) UTF8
-- lookupB2Map₁ x 
--   with lookupUTF8Trie (serializeUTF8Char' x) B2Map₁
-- ... | nothing = _ , (cons (mkIListCons x nil refl))
-- ... | just x₁
--   with x₁
-- ... | this x₂ = x₂
-- ... | that x₃ = _ , (cons (mkIListCons x nil refl))
-- ... | these x₂ x₃ = x₂

-- lookupB2Map₁Flag : ∀ {@0 bs} → UTF8Char bs → Bool
-- lookupB2Map₁Flag x
--   with lookupUTF8Trie (serializeUTF8Char' x) B2Map₁
-- ... | just x₁ = true
-- ... | nothing = false
