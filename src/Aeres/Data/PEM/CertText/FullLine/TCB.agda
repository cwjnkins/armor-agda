{-# OPTIONS --subtyping #-}


open import Aeres.Data.Base64.TCB
open import Aeres.Data.PEM.RFC5234.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.PEM.CertText.FullLine.TCB where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char

record CertFullLine (@0 bs : List Char) : Set where
  constructor mkCertFullLine
  field
    @0 {l e} : List Char
    line : ExactLength (IList Base64Char) 64 l
    eol  : EOL e
    @0 bs≡  : bs ≡ l ++ e

