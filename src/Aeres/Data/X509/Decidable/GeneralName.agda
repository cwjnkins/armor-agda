{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Length
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.RDN
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Decidable.GeneralName where

open Base256

parseOtherName : Parser Dig (Logging ∘ Dec) X509.OtherName
parseOtherName =
  parseTLV _ "other name" _ parseOctetstringValue

parseRfcName : Parser Dig (Logging ∘ Dec) X509.RfcName
parseRfcName = parseTLV _ "RFC name" _ parseIA5StringValue

parseDnsName : Parser Dig (Logging ∘ Dec) X509.DnsName
parseDnsName = parseTLV _ "DNS name" _ parseIA5StringValue

parseX400Address : Parser Dig (Logging ∘ Dec) X509.X400Address
parseX400Address = parseTLV _ "DNS name" _ parseOctetstringValue

parseDirName : Parser Dig (Logging ∘ Dec) X509.DirName
parseDirName =
  parseTLV _ "Dir. name" _
    (parseSeqElems "RDN" _ Props.TLV.nonempty Props.TLV.nonnesting parseRDN)

parseEdipartyName : Parser Dig (Logging ∘ Dec) X509.EdipartyName
parseEdipartyName = parseTLV _ "EDI party name" _ parseOctetstringValue

parseURI : Parser Dig (Logging ∘ Dec) X509.URI
parseURI = parseTLV _ "URI" _ parseIA5StringValue

parseIpAddress : Parser Dig (Logging ∘ Dec) X509.IpAddress
parseIpAddress = parseTLV _ "IP address" _ parseOctetstringValue

parseRegID : Parser Dig (Logging ∘ Dec) X509.RegID
parseRegID = parseTLV _ "registered name" _ parseOIDElems

module parseGeneralName where

  here' = "parseGeneralName"

  parseGeneralName : Parser Dig (Logging ∘ Dec) X509.GeneralName
  runParser parseGeneralName xs = do
    no ¬other ← runParser parseOtherName xs
      where yes other → do
        return (yes (mapSuccess _ (λ {bs} → X509.oname{bs}) other))
    no ¬rfc ← runParser parseRfcName xs
      where yes rfc → do
        return (yes (mapSuccess _ (λ {bs} → X509.rfcname{bs}) rfc))
    no ¬dns ← runParser parseDnsName xs
      where yes dns → do
        return (yes (mapSuccess _ (λ {bs} → X509.dnsname{bs}) dns))
    no ¬x400add ← runParser parseX400Address xs
      where yes x400add → do
        return (yes (mapSuccess _ (λ {bs} → X509.x400add{bs}) x400add))
    no ¬dir ← runParser parseDirName xs
      where yes dir → do
        return (yes (mapSuccess _ (λ {bs} → X509.dirname{bs}) dir))
    no ¬edi ← runParser parseEdipartyName xs
      where yes edi → do
        return (yes (mapSuccess _ (λ {bs} → X509.ediname{bs}) edi))
    no ¬uri ← runParser parseURI xs
      where yes uri → do
        return (yes (mapSuccess _ (λ {bs} → X509.uri{bs}) uri))
    no ¬ipadd ← runParser parseIpAddress xs
      where yes ipadd → do
        return (yes (mapSuccess _ (λ {bs} → X509.ipadd{bs}) ipadd))
    no ¬rid ← runParser parseRegID xs
      where yes rid → do
        return (yes (mapSuccess _ (λ {bs} → X509.rid{bs}) rid))
    return ∘ no $ λ where
      (success _ _ read≡ (X509.oname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬other
      (success _ _ read≡ (X509.rfcname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬rfc
      (success _ _ read≡ (X509.dnsname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬dns
      (success _ _ read≡ (X509.x400add x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬x400add
      (success _ _ read≡ (X509.dirname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬dir
      (success _ _ read≡ (X509.ediname x) _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬edi
      (success _ _ read≡ (X509.uri x)     _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬uri
      (success _ _ read≡ (X509.ipadd x)   _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬ipadd
      (success _ _ read≡ (X509.rid x)     _ ps≡) →
        contradiction (success _ _ read≡ x _ ps≡) ¬rid

  parseGeneralNamesElems : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength _ X509.GeneralNamesElems n)
  parseGeneralNamesElems =
    parseSeqElems "general name" _ NonEmpty.GeneralName NonNesting.GeneralName parseGeneralName

  parseGeneralNames : Parser Dig (Logging ∘ Dec) X509.GeneralNames
  parseGeneralNames = parseTLV _ "general names" _ parseGeneralNamesElems

-- module parseInt where
--   here' = "parseInt"

--   open ≡-Reasoning

--   parseInt : Parser Dig (Logging ∘ Dec) Generic.Int
--   parseInt = parseTLV Tag.Integer "Int" Generic.IntegerValue p
--     where
--     p : ∀ n → Parser Dig (Logging ∘ Dec) (ExactLength Dig Generic.IntegerValue n)
--     runParser (p n) xs = do
--       yes (success pre₀ r₀ r₀≡ (mk×ₚ (singleton v₀ refl) v₀Len refl) suf₀ ps≡₀)
--         ← runParser (parseN Dig n (tell $ here' String.++ ": underflow reading it")) xs
--         where no ¬parse → do
--           return ∘ no $ λ where
--             (success prefix read read≡ (mk×ₚ (Generic.mkIntegerValue val bs≡₁) sndₚ refl) suffix ps≡) →
--               contradiction
--                 (success prefix _ read≡
--                   (mk×ₚ (singleton prefix refl) sndₚ refl)
--                   suffix ps≡)
--                 ¬parse
--       return (yes
--         (success pre₀ _ r₀≡
--           (mk×ₚ (Generic.mkIntegerValue (twosComplement v₀) refl) v₀Len refl)
--           suf₀ ps≡₀))

-- open parseInt public using (parseInt)
