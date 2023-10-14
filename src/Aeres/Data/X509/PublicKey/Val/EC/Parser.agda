{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OctetString
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq       
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.EC.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: PublicKey: Val: EC"

parseValue : ∀ n → Parser (Logging ∘ Dec) (ExactLength ECBitStringValue n)
parseValue n =
  parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
    (parse&ᵈ
      (Parallel.nosubstrings₁ λ where _ refl refl → refl)
      (Parallel.Length≤.unambiguous _ ≡-unique)
      (parse≤ n
        (parseLit (tell $ here' String.++ ": underflow") (tell $ here' String.++ ": mismatch") [ # 0 ])
        (λ where _ refl refl → refl)
        (tell $ here' String.++ ": length overflow"))
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength OctetStringValue (n ∸ x)))
              r≡ (OctetString.parseValue (n - r)))

parse : Parser (Logging ∘ Dec) ECBitString
parse = parseTLV _ here' _ parseValue
