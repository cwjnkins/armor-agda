{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.EC
open import Aeres.Data.X509.PublicKey.Alg.RSA
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum

module Aeres.Data.X509.PublicKey.Alg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

parseUnsupported : Parser (Logging ∘ Dec) UnsupportedPublicKeyAlg
parseUnsupported =
  DefinedByOID.parse "X509: PublicKey: Alg: unsupported" λ n o →
    parseEquivalent{A = (ExactLength OctetStringValue n) ×ₚ const (False (((-, TLV.val o)) ∈? supportedPublicKeyAlgs))}
      (symEquivalent{B = (ExactLength OctetStringValue n) ×ₚ const (False (((-, TLV.val o)) ∈? supportedPublicKeyAlgs))}
        (proj₁ (Distribute.×ₚ-Σₚ-iso{A = OctetStringValue}{C = λ _ _ → False (((-, TLV.val o)) ∈? supportedPublicKeyAlgs)})))
      (parse×Dec{A = ExactLength OctetStringValue n}
        exactLength-nonnesting (tell $ "X509: PublicKey: Alg: supported failed to parse")
        (parseOctetStringValue n) λ x → T-dec)

parsePublicKeyAlg : Parser (Logging ∘ Dec) PublicKeyAlg
parsePublicKeyAlg =
   parseSum parseRSA
  (parseSum parseEC
            parseUnsupported)
