{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.GeneralName.Properties
open import Aeres.Data.X509.GeneralName.TCB
  hiding (module GeneralName)
open import Aeres.Data.X509.RDN
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.GeneralName.Parser where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: GeneralName"

parseOtherName : Parser (Logging ∘ Dec) OtherName
parseOtherName =
  parseTLV _ (here' String.++ ": other name") _ parseOctetStringValue

parseRfcName : Parser (Logging ∘ Dec) RfcName
parseRfcName = parseTLV _ (here' String.++ ": RFC") _ parseIA5StringValue

parseDnsName : Parser (Logging ∘ Dec) DnsName
parseDnsName = parseTLV _ (here' String.++ ": DNS") _ parseIA5StringValue

parseX400Address : Parser (Logging ∘ Dec) X400Address
parseX400Address = parseTLV _ (here' String.++ ": X400 address") _ parseOctetStringValue

parseDirName : Parser (Logging ∘ Dec) DirName
parseDirName =
  parseTLV _ (here' String.++ ": directory name") _
    λ n → parseExactLength TLV.nonnesting (tell $ here' String.++  "X509: RDN") parseRDNSeq n

parseEdipartyName : Parser (Logging ∘ Dec) EdipartyName
parseEdipartyName = parseTLV _ (here' String.++ ": EDI") _ parseOctetStringValue

parseURI : Parser (Logging ∘ Dec) URI
parseURI = parseTLV _ (here' String.++ ": URI") _ parseIA5StringValue

parseIpAddress : Parser (Logging ∘ Dec) IpAddress
parseIpAddress = parseTLV _ (here' String.++ ": IP") _ parseOctetStringValue

parseRegID : Parser (Logging ∘ Dec) RegID
parseRegID = parseTLV _ (here' String.++ ": registered name") _ parseOIDValue

module parseGeneralName where

  parseGeneralName : Parser (Logging ∘ Dec) GeneralName
  runParser parseGeneralName xs = do
    no ¬other ← runParser parseOtherName xs
      where yes other → do
        return (yes (mapSuccess (λ {bs} → oname{bs}) other))
    no ¬rfc ← runParser parseRfcName xs
      where yes rfc → do
        return (yes (mapSuccess (λ {bs} → rfcname{bs}) rfc))
    no ¬dns ← runParser parseDnsName xs
      where yes dns → do
        return (yes (mapSuccess (λ {bs} → dnsname{bs}) dns))
    no ¬x400add ← runParser parseX400Address xs
      where yes add → do
        return (yes (mapSuccess (λ {bs} → x400add{bs}) add))
    no ¬dir ← runParser parseDirName xs
      where yes dir → do
        return (yes (mapSuccess (λ {bs} → dirname{bs}) dir))
    no ¬edi ← runParser parseEdipartyName xs
      where yes edi → do
        return (yes (mapSuccess (λ {bs} → ediname{bs}) edi))
    no ¬uri ← runParser parseURI xs
      where yes uri' → do
        return (yes (mapSuccess (λ {bs} → uri{bs}) uri'))
    no ¬ipadd ← runParser parseIpAddress xs
      where yes ipad → do
        return (yes (mapSuccess (λ {bs} → ipadd{bs}) ipad))
    no ¬rid ← runParser parseRegID xs
      where yes rid' → do
        return (yes (mapSuccess (λ {bs} → rid{bs}) rid'))
    return ∘ no $ λ where
      (success _ _ read≡ (oname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬other
      (success _ _ read≡ (rfcname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬rfc
      (success _ _ read≡ (dnsname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬dns
      (success _ _ read≡ (x400add x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬x400add
      (success _ _ read≡ (dirname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬dir
      (success _ _ read≡ (ediname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬edi
      (success _ _ read≡ (uri x)     _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬uri
      (success _ _ read≡ (ipadd x)   _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬ipadd
      (success _ _ read≡ (rid x)     _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬rid

  parseGeneralNamesElems : ∀ n → Parser (Logging ∘ Dec) (ExactLength GeneralNamesElems n)
  parseGeneralNamesElems n =
    parseBoundedSequenceOf here' _ nonempty nonnesting parseGeneralName n 1

  parseGeneralNames : Parser (Logging ∘ Dec) GeneralNames
  parseGeneralNames = parseTLV _ here' _ parseGeneralNamesElems

open parseGeneralName public
  using (parseGeneralName ; parseGeneralNamesElems ; parseGeneralNames)
