{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints
open import Aeres.Data.X509.PublicKey.Val.RSA.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

private
  here' = "X509: PublicKey: Val: RSA" 

parseRSABitStringFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSABitStringFields n)
parseRSABitStringFields n =
  parseExactLength nonnesting (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent
      (parse& (λ where _ refl refl → refl)
        (parseLit 
          (tell $ here' String.++ ": zero bit: underflow")
          (tell $ here' String.++ ": zero bit: mismatch")
          [ # 0 ])
        parseRSAPkInts))
    n

parseRSABitString :  Parser (Logging ∘ Dec) RSABitString
parseRSABitString = parseTLV _ here' _ parseRSABitStringFields
