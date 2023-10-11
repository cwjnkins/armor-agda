{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension.AIA
open import Aeres.Data.X509.Extension.AKI
open import Aeres.Data.X509.Extension.BC
open import Aeres.Data.X509.Extension.CRLDistPoint
open import Aeres.Data.X509.Extension.CertPolicy
open import Aeres.Data.X509.Extension.EKU
open import Aeres.Data.X509.Extension.IAN
open import Aeres.Data.X509.Extension.INAP
open import Aeres.Data.X509.Extension.KU
open import Aeres.Data.X509.Extension.NC
open import Aeres.Data.X509.Extension.PC
open import Aeres.Data.X509.Extension.PM
open import Aeres.Data.X509.Extension.SAN
open import Aeres.Data.X509.Extension.SKI
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Extension.Properties
open import Aeres.Data.X509.Extension.TCB
open import Aeres.Data.X509.GeneralNames
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Boool
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.SequenceOf
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Grammar.Seq
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Extension.Parser where

open ≡-Reasoning

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8
open Aeres.Grammar.Seq         UInt8

private
  here' = "X509: TBSCert: Extension"

  parseExtensionFields
    : ∀ {@0 P} {@0 A : @0 List UInt8 → Set} (P? : ∀ bs → Dec (P bs))
      → @0 NoSubstrings A → @0 NoConfusion Boool A → Unambiguous P
      → Parser (Logging ∘ Dec) A
      → ∀ n → Parser (Logging ∘ Dec) (ExactLength (ExtensionFields P A) n)
  parseExtensionFields{P} P? nn nc ua p n =
    parseEquivalent
      (Iso.transEquivalent
        (Iso.symEquivalent Distribute.exactLength-&)
        (Parallel.equivalent₁ equivalentExtensionFields))
      (parse&ᵈ
        (Parallel.nosubstrings₁ (Parallel.nosubstrings₁ TLV.nosubstrings))
        (Parallel.Length≤.unambiguous _ (Parallel.unambiguous OID.unambiguous λ _ → erased-unique ua))
        (parse≤ n
          (parseSigma TLV.nosubstrings OID.unambiguous
            parseOID λ x →
              let (singleton v v≡) = OID.serializeVal (TLV.val x)
              in
              subst₀ (Dec ∘ Erased ∘ P) v≡ (erased? (P? v)))
              -- erased? (P? {!!}))
          (Parallel.nosubstrings₁ TLV.nosubstrings) (tell $ here' String.++ " underflow (OID)"))
      λ where
        (singleton r r≡) (mk×ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁)) (─ bsLen)) →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n ∸ x))) r≡
            (Option.parseOption₁&₁ parseBool p TLV.nosubstrings nn nc ((tell $ here' String.++ ": length mismatch (bool)")) (n - r)))

parseSelectExtn : ∀ n → Parser (Logging ∘ Dec) (ExactLength SelectExtn n)
parseSelectExtn n =
  parseEquivalent
    (Iso.transEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum)) (Parallel.equivalent₁ equivalent))
    (parseSum
      (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion (λ ())) (λ where refl refl → refl)  parseAKIFields n)
      (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
        (parseSum
          (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion (λ ())) (λ where refl refl → refl) parseSKIFields n)
          (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
             (parseSum
               (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseKUFields n)
               (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                  (parseSum
                    (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseEKUFields n)
                    (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                       (parseSum
                         (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseBCFields n)
                         (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                            (parseSum
                              (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseIANFields n)
                              (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                 (parseSum
                                   (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseSANFields n)
                                   (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                      (parseSum
                                        (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseCertPolFields n)
                                        (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                           (parseSum
                                             (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseCRLDistFields n)
                                             (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                               (parseSum
                                                 (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseNCFields n)
                                                 (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                                   (parseSum
                                                     (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parsePCFields n)
                                                     (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                                       (parseSum
                                                         (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parsePMFields n)
                                                         (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                                           (parseSum
                                                             (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseINAPFields n)
                                                             (parseEquivalent (Iso.symEquivalent (Distribute.exactLength-Sum))
                                                               (parseSum
                                                                 (parseExtensionFields (_≟ _) TLV.nosubstrings (TLV.noconfusion λ ()) (λ where refl refl → refl) parseAIAFields n)
                                                                 (parseExtensionFields (λ bs → T-dec) TLV.nosubstrings (TLV.noconfusion (λ ())) (λ a₁ a₂ → T-unique a₁ a₂) parseOctetString n))))))))))))))))))))))))))))

parseExtension : Parser (Logging ∘ Dec) Extension
parseExtension = parseTLV _ (here' String.++ ": field") _ parseSelectExtn

parseExtensionsSeq : Parser (Logging ∘ Dec) ExtensionsSeq
parseExtensionsSeq = parseNonEmptySeq (here' String.++ ": fields") _ TLV.nonempty TLV.nosubstrings parseExtension

parseExtensions : Parser (Logging ∘ Dec) Extensions
parseExtensions =
  parseTLV _ here' _
    (parseExactLength TLV.nosubstrings (tell $ here' String.++ ": length mismatch") parseExtensionsSeq)

