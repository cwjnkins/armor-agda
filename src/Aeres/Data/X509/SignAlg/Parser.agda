open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.SignAlg.DSA
open import Aeres.Data.X509.SignAlg.ECDSA
open import Aeres.Data.X509.SignAlg.Properties
open import Aeres.Data.X509.SignAlg.RSA
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum

module Aeres.Data.X509.SignAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: SignAlg"

parseParam : ∀ n {@0 bs} (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam o) n)
parseParam n o =
  case isSupported o
  ret (λ o∈? → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam' o o∈?) n))
  of λ where
    (no ¬p) → parseN _ (tell $ here' String.++ " (param): underflow")
    (yes o∈) →
      case lookupSignAlg o o∈
      ret (λ o∈ → Parser (Logging ∘ Dec) (ExactLength (SignAlgParam“ o o∈) n))
      of λ where
        (inj₁ x) →
          parseExactLength
            (λ where _ (─ refl) (─ refl) → refl)
            silent
            (parseErased (parseLit silent silent []))
            _
        (inj₂ (inj₁ x)) →
          parseExactLength
            (λ where _ (─ refl) (─ refl) → refl)
            silent
            (parseErased (parseLit silent silent []))
            _
        (inj₂ (inj₂ y)) →
          RSA.parseParams n o (yes y)

parse : Parser (Logging ∘ Dec) SignAlg
parse =
  DefinedByOID.parse here' parseParam
