{-# OPTIONS --subtyping #-}

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

parseUnsupported : Parser (Logging ∘ Dec) UnsupportedSignAlg
parseUnsupported =
  DefinedByOID.parse (here' String.++ ": unsupported") p
  where
  p : ∀ n {@0 bs} → (o : OID bs) → Parser (Logging ∘ Dec) (ExactLength (UnsupportedParam o) n)
  runParser (p n o) xs =
    case (-, TLV.val o) ∈? supportedSignAlgOIDs of λ where
      (yes p₁) → do
        tell $ here' String.++ ": unsupported: OID is supported!"
        return ∘ no $ λ where
          (success prefix read read≡ (mk×ₚ (mk×ₚ str str∉) (─ uLen)) suffix ps≡) →
            contradiction p₁ (toWitnessFalse str∉)
      (no ¬p) → do
        (yes (success pre₁ r₁ r₁≡ (mk×ₚ os (─ osLen)) suf₁ ps≡₁)) ← runParser (OctetString.parseValue n) xs
          where no ¬p → do
            tell $ here' String.++ ": underflow parsing parameter"
            return ∘ no $ λ where
              (success prefix read read≡ (mk×ₚ (mk×ₚ str str∉) (─ uLen)) suffix ps≡) →
                contradiction (success prefix _ read≡ (mk×ₚ str (─ uLen)) suffix ps≡) ¬p
        return (yes
          (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ os (fromWitnessFalse{Q = (-, TLV.val o) ∈? supportedSignAlgOIDs} ¬p)) (─ osLen))
            suf₁ ps≡₁))
 
parseSignAlg : Parser (Logging ∘ Dec) SignAlg
parseSignAlg =
   parseEquivalent equiv
    (parseSum DSA.parseSupported
    (parseSum ECDSA.parseSupported
    (parseSum RSA.parseSupported
              parseUnsupported)))
