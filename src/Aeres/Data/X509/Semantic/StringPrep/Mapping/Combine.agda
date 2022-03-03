
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M1
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M2
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M3
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M4
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M5
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M6
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M7
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M8
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M9
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M10
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M11
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M12
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M13
open import Aeres.Data.X509.Semantic.StringPrep.Mapping.M14
import      Aeres.Grammar.IList

module Aeres.Data.X509.Semantic.StringPrep.Mapping.Combine where

open Base256
open Aeres.Grammar.IList UInt8

trie : UTF8Trie
trie = fromList (trie₁ ++ trie₂ ++ trie₃ ++ trie₄ ++ trie₅ ++ trie₆ ++ trie₇ ++ trie₈ ++ trie₉ ++ trie₁₀ ++ trie₁₁ ++ trie₁₂ ++ trie₁₃ ++ trie₁₄)
