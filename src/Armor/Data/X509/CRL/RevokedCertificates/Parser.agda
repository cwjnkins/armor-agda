{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.TCB
open import Armor.Data.X509.Validity.Time
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq

open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.Parser where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Parser       UInt8
open Armor.Grammar.Properties   UInt8
open Armor.Grammar.Seq          UInt8


private
  here' = "X509: CRL: TBSCertList: RevokedCertificates"

parseRevokedCertificateFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength RevokedCertificateFields n)
parseRevokedCertificateFields n =
  parseEquivalent
    (Iso.transEquivalent
      (Iso.symEquivalent Distribute.exactLength-&)
      (Parallel.equivalent₁ equivalentRevokedCertificateFields))
    (parse&ᵈ{A = Length≤ (&ₚ Int Time) n}
      (Parallel.nosubstrings₁ (Seq.nosubstrings TLV.nosubstrings Time.nosubstrings))
      (Parallel.Length≤.unambiguous
        _
        (Seq.unambiguous Int.unambiguous TLV.nosubstrings Time.unambiguous))
      (parse≤
        n (parse& TLV.nosubstrings  (Int.parse here') Time.parse) (Seq.nosubstrings TLV.nosubstrings Time.nosubstrings)
          (tell $ here' String.++ " (fields): overflow"))
       λ where
        (singleton r₁ r₁≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength  _ (n - x)))
            r₁≡ (Option.parseOption₁ExactLength TLV.nosubstrings (tell $ here' String.++ " (fields): overflow") parseEntryExtensions (n - r₁)))

parseRevokedCertificatesElems : ∀ n → Parser (Logging ∘ Dec) (ExactLength (NonEmptySequenceOf RevokedCertificate) n)
parseRevokedCertificatesElems n =
  parseBoundedSequenceOf here' _ TLV.nonempty TLV.nosubstrings
    (parseTLV _ here' _
      parseRevokedCertificateFields)
    n 1

parseRevokedCertificates : Parser (Logging ∘ Dec) RevokedCertificates
parseRevokedCertificates =
  parseTLV _ here' _ parseRevokedCertificatesElems
