{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Ints.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: PublicKey: Val: RSA: Ints:"

parseRSAPkIntsFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSAPkIntsFields n)
parseRSAPkIntsFields n =
  parseExactLength nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent (parse& TLV.nonnesting Int.parse Int.parse)) n

parseRSAPkInts :  Parser (Logging ∘ Dec) RSAPkInts
parseRSAPkInts = parseTLV _ here' _ parseRSAPkIntsFields
