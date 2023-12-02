open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.RSA.Ints
open import Aeres.Data.X509.PublicKey.Val.RSA.Properties
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Seq
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.RSA.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: RSA" 

parseFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RSABitStringFields n)
parseFields n =
  parseExactLength nosubstrings (tell $ here' String.++ ": underflow")
    (parseEquivalent equivalent
      (parse& (λ where _ (─ refl) (─ refl) → refl)
        (parseLitE
          (tell $ here' String.++ ": zero bit: underflow")
          (tell $ here' String.++ ": zero bit: mismatch")
          [ # 0 ])
        Ints.parse))
    n

parse :  Parser (Logging ∘ Dec) RSABitString
parse = parseTLV _ here' _ parseFields
