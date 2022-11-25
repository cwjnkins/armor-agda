{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.SignAlg.DSA
open import Aeres.Data.X509.SignAlg.ECDSA
open import Aeres.Data.X509.SignAlg.Properties
open import Aeres.Data.X509.SignAlg.RSA
open import Aeres.Data.X509.SignAlg.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum

module Aeres.Data.X509.SignAlg.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: SignAlg"

parseUnsupported : Parser (Logging ∘ Dec) UnsupportedSignAlg
parseUnsupported =
  parseAlgorithmIdentifier (here' String.++ ": unsupported")
    λ n o →
      parseEquivalent
        {A = ExactLength OctetStringValue n ×ₚ const (False ((-, TLV.val o) ∈? supportedSignAlgOIDs))}
        (symEquivalent
          (proj₁
            (Distribute.×ₚ-Σₚ-iso
              {A = OctetStringValue}
              {B = λ xs → Erased (length xs ≡ n)}
              {C = λ _ _ → False ((-, TLV.val o) ∈? supportedSignAlgOIDs)})))
        (parse×Dec exactLength-nonnesting (tell $ here' String.++ ": unsupported: OID is supported!")
          (parseOctetStringValue n)
          (λ _ → T-dec))
  
parseSignAlg : Parser (Logging ∘ Dec) SignAlg
parseSignAlg =
   parseEquivalent equiv
    (parseSum DSA.parseSupported
    (parseSum ECDSA.parseSupported
    (parseSum RSA.parseSupported
              parseUnsupported)))
