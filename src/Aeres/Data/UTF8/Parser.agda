{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
open import Aeres.Prelude
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parser

module Aeres.Data.UTF8.Parser where

open Base256
open Aeres.Grammar.IList  UInt8
open Aeres.Grammar.Parser UInt8

module parseUTF8 where
  hereChar = "parseUTF8Char"

