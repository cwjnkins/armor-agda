{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser  UInt8
open Aeres.Grammar.Properties  UInt8

private
  here' = "X509: Extension: CertPolicy: PolicyInformation"

open ≡-Reasoning

parsePolicyInformationFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PolicyInformationFields n)
parsePolicyInformationFields n =
  parseEquivalent{A = &ₚᵈ (WithinLength OID n) (λ (@0 bs) _ → ExactLength (Option PolicyQualifiersSeq) (n - length bs))}
    (transEquivalent (symEquivalent Distribute.exactLength-&) (equivalent×ₚ equiv))
    (parse&ᵈ
      (withinLength-nonnesting TLV.nonnesting)
      (withinLength-unambiguous OID.unambiguous)
      (parse≤ _ parseOID TLV.nonnesting (tell $ here' String.++ ": overflow"))
      λ where
        (singleton r r≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (Option PolicyQualifiersSeq) (n - x)))
            r≡
            (parseOption₁ExactLength TLV.nonnesting
              (tell $ here' String.++ ": underflow")
              parsePolicyQualifiersSeq (n - r)))
        
parsePolicyInformation : Parser (Logging ∘ Dec) PolicyInformation
parsePolicyInformation =
  parseTLV _ here' _ parsePolicyInformationFields

