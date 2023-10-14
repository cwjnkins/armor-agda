{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Properties
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB
import      Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.UserNotice
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.SequenceOf
open import Aeres.Data.X690-DER.Strings
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.Extension.CertPolicy.PolicyInformation.Qualifier.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: Extension: CertPolicy: PolicyInformation: Qualifier"

parseCPSURIQualifier : ∀ n → Parser (Logging ∘ Dec) (ExactLength CPSURIQualifier n)
parseCPSURIQualifier =
  DefinedByOID.parseFields here' λ n o →
    parseExactLength (Parallel.nosubstrings₁ TLV.nosubstrings)
      (tell $ here' String.++ ": CPSURI: length mismatch")
      (parse×Dec TLV.nosubstrings (tell $ here' String.++ ": CPSURI: wrong OID")
        parseIA5String
        (λ x → _ ≋? _))
      _

parseUserNoticeQualifier : ∀ n → Parser (Logging ∘ Dec) (ExactLength UserNoticeQualifier n)
parseUserNoticeQualifier =
  DefinedByOID.parseFields here' λ n o →
    parseExactLength (Parallel.nosubstrings₁ TLV.nosubstrings)
      (tell $ here' String.++ ": UserNoticeQualifier: length mismatch")
      (parse×Dec TLV.nosubstrings
        (tell $ here' String.++ ": UserNoticeQualifier: wrong OID")
        parseUserNotice
        (λ x → _ ≋? _))
      _

parsePolicyQualifierInfoFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength PolicyQualifierInfoFields n)
parsePolicyQualifierInfoFields n =
  parseEquivalent{A = Sum (ExactLength CPSURIQualifier n) (ExactLength UserNoticeQualifier n)}
    (Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-Sum) (Parallel.equivalent₁ equivalentPolicyQualifierInfoFields))
    (parseSum (parseCPSURIQualifier n) (parseUserNoticeQualifier n))

parsePolicyQualifierInfo : Parser (Logging ∘ Dec) PolicyQualifierInfo
parsePolicyQualifierInfo =
  parseTLV _ (here' String.++ " (fields)") _ parsePolicyQualifierInfoFields

parsePolicyQualifiersSeq : Parser (Logging ∘ Dec) PolicyQualifiersSeq
parsePolicyQualifiersSeq =
  parseNonEmptySeq here' _ TLV.nonempty TLV.nosubstrings
    parsePolicyQualifierInfo
