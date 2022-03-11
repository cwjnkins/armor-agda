{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Data.UTF8.Properties as UTF8Props
open import Aeres.Prelude
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.UTF8.Serializer where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Parser      UInt8

serializeUFT8Char : ∀ {@0 bs} → UTF8Char bs → Singleton bs
serializeUFT8Char (utf81 (mkUTF8Char1 b₁ b₁range refl)) = self
serializeUFT8Char (utf82 (mkUTF8Char2 b₁ b₂ b₁range b₂range refl)) = self
serializeUFT8Char (utf83 (mkUTF8Char3 b₁ b₂ b₃ b₁range b₂range b₃range refl)) = self
serializeUFT8Char (utf84 (mkUTF8Char4 b₁ b₂ b₃ b₄ b₁range b₂range b₃range b₄range refl)) = self

serializeUTF8Char' : ∀ {@0 bs} → UTF8Char bs → List UInt8
serializeUTF8Char' = Singleton.x ∘ serializeUFT8Char
