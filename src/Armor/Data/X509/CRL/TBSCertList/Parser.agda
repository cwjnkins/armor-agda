{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.CRL.TBSCertList.TCB
open import Armor.Data.X509.CRL.TBSCertList.Properties
open import Armor.Data.X509.Name as Name
open import Armor.Data.X509.Validity.Time as Time
open import Armor.Data.X509.CRL.Version as Version
open import Armor.Data.X509.CRL.Extension
open import Armor.Data.X509.CRL.RevokedCertificates
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq

open import Armor.Prelude

module Armor.Data.X509.CRL.TBSCertList.Parser where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Parser       UInt8
open Armor.Grammar.Properties   UInt8
open Armor.Grammar.Seq          UInt8

private
  here' = "X509: CRL: CertList: TBSCertList"

parseTBSCertListFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength TBSCertListFields n)
parseTBSCertListFields n =
  parseEquivalent equiv
    (parse&ᵈ {A = Length≤ (&ₚ (Option Version) SignAlg) n}
      (Parallel.nosubstrings₁{A = &ₚ (Option Version) SignAlg} nsRep₅)
      (Parallel.Length≤.unambiguous _ (Seq.unambiguousOption₁ Version.unambiguous Version.nosubstrings SignAlg.unambiguous ncVersionSignAlg))
      (parse≤ _
        (parseOption₁ here'
          Version.nosubstrings
          Version.parse
          SignAlg.parse)
        nsRep₅ overflow)
    λ where
        (singleton r₁ r₁≡) _ →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₄ (n - x)))
            r₁≡ (p₁ (n - r₁)))
  where
  equiv : Equivalent (&ₚᵈ (Length≤ (&ₚ (Option Version) SignAlg) n) (λ {bs'} _ → ExactLength Rep₄ (n - length bs'))) (ExactLength TBSCertListFields n)
  equiv = Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentTBSCertListFields)

  overflow : Logging (Level.Lift _ ⊤)
  overflow = tell $ here' String.++ ": overflow"

  p₃ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₂ n)
  p₃ n =
     parse₂Option₃{A = Time}{B = RevokedCertificates}{C = Extensions}
        here'
        Time.nosubstrings TLV.nosubstrings TLV.nosubstrings
        ncTimeRevokedCertificates ncTimeExtensions (TLV.noconfusion (λ ()))
        Time.parse parseRevokedCertificates parseExtensions
        _

  p₂ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₃ n)
  p₂ n =
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ Time n}
        (Parallel.nosubstrings₁{A = Time} Time.nosubstrings)
        (Parallel.Length≤.unambiguous _ Time.unambiguous)
        (parse≤ _  Time.parse Time.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₂  (n - x)))
              r≡ (p₃ (n - r)))

  p₁ : ∀ n → Parser (Logging ∘ Dec) (ExactLength Rep₄ n)
  p₁ n = 
    parseEquivalent (Iso.symEquivalent Distribute.exactLength-&)
      (parse&ᵈ{A = Length≤ Name n}
        (Parallel.nosubstrings₁{A = Name} TLV.nosubstrings)
        (Parallel.Length≤.unambiguous _ Name.unambiguous)
        (parse≤ _ Name.parse TLV.nosubstrings overflow)
        λ where
          (singleton r r≡) _ →
            subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength Rep₃  (n - x)))
              r≡ (p₂ (n - r)))

parseTBSCertList : Parser (Logging ∘ Dec) TBSCertList
parseTBSCertList =
  parseTLV _ here' _ parseTBSCertListFields
