{-# OPTIONS --erasure #-}
open import Armor.Binary
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.InvalidityDate
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.CertIssuer
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode
import      Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB.OIDS as OIDS
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Properties
open import Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.TCB
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.Default
open import Armor.Data.X690-DER.Int
open import Armor.Data.X690-DER.OID
open import Armor.Data.X690-DER.OctetString
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.Sequence
open import Armor.Data.X690-DER.SequenceOf
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
import      Armor.Grammar.Parser
import      Armor.Grammar.Properties
import      Armor.Grammar.Sum
import      Armor.Grammar.Seq
open import Armor.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.Parser where

open ≡-Reasoning

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parser      UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Sum         UInt8
open Armor.Grammar.Seq         UInt8

private
  here' = "X509: CRL: CertList: TBSCertList: RevokedCertificates: EntryExtension"

  parseExtensionFields
    : ∀ {@0 P : List UInt8 → Set} {A : @0 List UInt8 → Set} (P? : ∀ bs → Dec (P bs))
    → @0 NoSubstrings A → @0 NoConfusion Boool A → (∀ {x} → Unique (P x))
    → Parser (Logging ∘ Dec) A
    → ∀ n → Parser (Logging ∘ Dec) (ExactLength (ExtensionFields P A) n)
  parseExtensionFields{P}{A} P? nn nc ua p n =
    parseEquivalent equiv
      (parse&ᵈ
        (Parallel.nosubstrings₁
          (Parallel.nosubstrings₁ TLV.nosubstrings))
        (Parallel.Length≤.unambiguous _
          (Parallel.unambiguous
            OID.unambiguous
            λ _ → erased-unique ua))
        pₐ pb)
    where
    B' = &ₚ (Default Boool falseBoool) A
    A' = (Length≤ (Σₚ OID (λ _ x → Erased (P (TLV.v x)))) n)
    B : {@0 bs : List UInt8} → A' bs → @0 List UInt8 → Set
    B {bs} _ = ExactLength B' (n - length bs)
    AB = (&ₚᵈ A' B)

    equiv : Equivalent AB (ExactLength (ExtensionFields P A) n)
    equiv =
      Iso.transEquivalent
       (Iso.symEquivalent Distribute.exactLength-&)
       (Parallel.equivalent₁ equivalentExtensionFields)

    pₐ : Parser (Logging ∘ Dec) A'
    pₐ = parse≤ n
           (parseSigma TLV.nosubstrings OID.unambiguous parseOID
             (λ x →
               let (singleton v v≡) = OID.serializeVal (TLV.val x)
               in subst₀! (λ x → Dec (Erased (P x))) {y = TLV.v x}v≡ (erased? (P? v))))
           (Parallel.nosubstrings₁ TLV.nosubstrings)
           (tell $ here' String.++ " underflow (OID)")

    pb : ∀ {@0 bs} → Singleton (length bs) → (a : A' bs) → Parser (Logging ∘ Dec) (B a)
    pb (singleton r r≡) _ =
      subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength B' (n ∸ x)))
        r≡
        (parseExactLength
          (Sequence.nosubstringsDefault₁ _ TLV.nosubstrings nn nc)
          (tell $ here' String.++ " (fields): length mismatch")
          (Sequence.parseDefault₁ _ here' Boool.unambiguous TLV.nosubstrings nc Boool.parse p) (n - r))

  parseUnsupportedExtensionField : ∀ n → Parser (Logging ∘ Dec) (ExactLength (Σₚ ExtensionFieldUnsupported (λ _ → T ∘ not ∘ ExtensionFields.getCrit)) n)
  runParser (parseUnsupportedExtensionField n) xs = do
    (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ v₁ v₁Len) ¬v₁Crit) suf₁ ps≡₁)) ← runParser
                 (parseSigma{B = λ _ → T ∘ not ∘ ExtensionFields.getCrit ∘ Σₚ.fstₚ}
                   (Parallel.ExactLength.nosubstrings _)
                   (Parallel.ExactLength.unambiguous _
                     (Fields.unambiguous T-unique OctetString.unambiguous (TLV.noconfusion λ ())))
                   (parseExtensionFields{P = False ∘ (_∈? supportedExtensions)} (λ bs → T-dec) TLV.nosubstrings (TLV.noconfusion λ ()) T-unique OctetString.parse n)
                   λ _ → T-dec)
                 xs
         where no ¬p → do
           return ∘ no $ λ where
             (success prefix read read≡ (mk×ₚ (mk×ₚ v₁ ¬v₁Crit) v₁Len) suffix ps≡) →
               contradiction
                 (success prefix read read≡ (mk×ₚ (mk×ₚ v₁ v₁Len) ¬v₁Crit) suffix ps≡)
                 ¬p
    return (yes (success pre₁ r₁ r₁≡ (mk×ₚ (mk×ₚ v₁ ¬v₁Crit) v₁Len) suf₁ ps≡₁))

parseSelectEntryExtn : ∀ n → Parser (Logging ∘ Dec) (ExactLength SelectEntryExtn n)
parseSelectEntryExtn n = 
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum)) (Parallel.equivalent₁ equivalent))
    (parseSum
      (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion (λ ())) (λ where refl refl → refl)  parseReasonCodeFields n)
      (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
        (parseSum
          (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion (λ ())) (λ where refl refl → refl) parseInvalidityDateFields n)
          (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
             (parseSum
               (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseCertIssuerFields n)
                                       (parseUnsupportedExtensionField n))))))

parseEntryExtension : Parser (Logging ∘ Dec) EntryExtension
parseEntryExtension = parseTLV _ (here' String.++ ": field") _ parseSelectEntryExtn

parseEntryExtensions : Parser (Logging ∘ Dec) EntryExtensions
parseEntryExtensions = parseNonEmptySeq (here' String.++ ": fields") _ TLV.nonempty TLV.nosubstrings parseEntryExtension
