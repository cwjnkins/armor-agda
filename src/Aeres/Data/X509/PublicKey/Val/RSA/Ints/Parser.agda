{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: RSA: Ints:"

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSAPkIntsFields n)
parseFields =
  parseExactLength nosubstrings (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent (parse& TLV.nosubstrings (Int.parse here') (Int.parse here')))

parse :  Parser (Logging ∘ Dec) RSAPkInts
parse = parseTLV _ here' _ parseFields
