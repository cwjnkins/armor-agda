
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
open import Aeres.Test.UTF8Trie.M1
open import Aeres.Test.UTF8Trie.M2
open import Aeres.Test.UTF8Trie.M3
open import Aeres.Test.UTF8Trie.M4
open import Aeres.Test.UTF8Trie.M5
open import Aeres.Test.UTF8Trie.M6
open import Aeres.Test.UTF8Trie.M7
open import Aeres.Test.UTF8Trie.M8
open import Aeres.Test.UTF8Trie.M9
open import Aeres.Test.UTF8Trie.M10
open import Aeres.Test.UTF8Trie.M11
open import Aeres.Test.UTF8Trie.M12
open import Aeres.Test.UTF8Trie.M13
open import Aeres.Test.UTF8Trie.M14
import      Aeres.Grammar.IList

module Aeres.Test.UTF8Trie.Combine where

open Base256
open Aeres.Grammar.IList UInt8

trie : UTF8Trie
trie = fromList (trie₁ ++ trie₂ ++ trie₃ ++ trie₄ ++ trie₅ ++ trie₆ ++ trie₇ ++ trie₈ ++ trie₉ ++ trie₁₀ ++ trie₁₁ ++ trie₁₂ ++ trie₁₃ ++ trie₁₄)
