open import Armor.Binary
open import Armor.Data.X509.CRL.CertList.Properties
open import Armor.Data.X509.CRL.CertList.TCB
open import Armor.Data.X509.SignAlg
open import Armor.Data.X509.CRL.TBSCertList
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.TLV
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.CRL.CertList.Parser where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.IList        UInt8
open Armor.Grammar.Option       UInt8
open Armor.Grammar.Parallel     UInt8
open Armor.Grammar.Parser       UInt8
open Armor.Grammar.Properties   UInt8
open Armor.Grammar.Seq          UInt8

private
  here' = "X509: CRL: CertList"

parseCertListFields : ∀ n → Parser (Logging ∘ Dec) (ExactLength CertListFields n)
parseCertListFields n =
  parseEquivalent eq p₁
  where
  A = Length≤ (TBSCertList ×ₚ Singleton) n
  B : {@0 bs : List UInt8} (a : A bs) → _
  B {bs} _ = ExactLength (&ₚ SignAlg (BitString ×ₚ Singleton)) (n - length bs)
  eq : Equivalent
         (&ₚᵈ A B)
         (ExactLength CertListFields n)
  eq = Iso.transEquivalent (Iso.symEquivalent Distribute.exactLength-&) (Parallel.equivalent₁ equivalentCertListFields)

  @0 nsₐ : NoSubstrings A
  nsₐ = Parallel.nosubstrings₁ (Parallel.nosubstrings₁ TLV.nosubstrings)

  @0 uaₐ : Unambiguous A
  uaₐ = Parallel.Length≤.unambiguous _ (Parallel.unambiguous×ₚ TBSCertList.unambiguous (λ where self self → refl))

  pₐ : Parser (Logging ∘ Dec) A
  pₐ = parse≤ n (parse×Singleton parseTBSCertList) (Parallel.nosubstrings₁ TLV.nosubstrings) (tell $ here' String.++ " (fields): overflow")

  @0 ns' : NoSubstrings (&ₚ SignAlg (BitString ×ₚ Singleton))
  ns' = Seq.nosubstrings{A = SignAlg}{B = BitString ×ₚ Singleton} SignAlg.nosubstrings (Parallel.nosubstrings₁ TLV.nosubstrings)

  pb : {@0 bs : List UInt8} → Singleton (length bs) → (a : A bs) → Parser (Logging ∘ Dec) (B a)
  pb (singleton r r≡) _ =
    subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength (&ₚ SignAlg (BitString ×ₚ Singleton)) (n ∸ x)))
      r≡
      (parseExactLength{A = &ₚ SignAlg (BitString ×ₚ Singleton)} ns'
        (tell $ here' String.++ " (fields): length mismatch")
        (parse& {A = SignAlg} {B = BitString ×ₚ Singleton}
          SignAlg.nosubstrings SignAlg.parse
          (parse×Singleton parseBitstring))
        (n - r))

  p₁ : Parser (Logging ∘ Dec) (&ₚᵈ A B)
  p₁ =
    parse&ᵈ{A = A} nsₐ uaₐ pₐ pb

parseCertList : Parser (Logging ∘ Dec) CertList
parseCertList =
  parseTLV _ here' _ parseCertListFields

parseCRLList : Parser (Logging ∘ Dec) CRLList
parseCRLList = LogDec.MaximalParser.parser (parseIListMax (mkLogged ["parseCRLList: underflow"] tt) _ TLV.nonempty TLV.nosubstrings  parseCertList)
