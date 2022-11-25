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
open import Aeres.Data.X509.GeneralName
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
import      Aeres.Grammar.Parser
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Extension.Parser where

open ≡-Reasoning

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parser      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

private
  here' = "X509: Extension"

  parseExtensionFields
    : ∀ {@0 P} {@0 A : @0 List UInt8 → Set} (P? : ∀ bs → Dec (P bs))
      → @0  NonNesting A → @0 NoConfusion Boool A → Unambiguous P
      → Parser (Logging ∘ Dec) A
      → ExactLengthParser (Logging ∘ Dec) (ExtensionFields P A)
  parseExtensionFields P? nn nc ua p n =
    parseEquivalent
      (transEquivalent
        (symEquivalent Distribute.exactLength-&)
        (equivalent×ₚ Fields.equivalent))
      (parse&ᵈ
      (withinLength-nonnesting (nonnesting×ₚ₁ TLV.nonnesting))
      (λ where
        (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ fstₚ₂ (─ sndₚ₂) refl) → ‼
          subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ x (─ sndₚ₂) refl)
            (unambiguous×ₚ OID.unambiguous (λ where (─ pf₁) (─ pf₂) → ‼ cong ─_ (ua pf₁ pf₂) ) fstₚ₁ fstₚ₂)
              (subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ fstₚ₁ (─ x) refl) (≤-irrelevant sndₚ₁ sndₚ₂)
                refl))
      (parse≤ n
        (parse×Dec TLV.nonnesting (return (Level.lift tt)) parseOID λ x → erased? (P? x))
          (nonnesting×ₚ₁ TLV.nonnesting) (tell $ here' String.++ ": fields: overflow"))
      λ where
        (singleton r r≡) (mk×ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (─ bsLen) refl) →
          subst₀ (λ x → Parser (Logging ∘ Dec) (ExactLength _ (n ∸ x))) r≡
            (parseOption₁&₁ parseBool p TLV.nonnesting nn nc ((tell $ here' String.++ ": length mismatch (bool)")) (n - r)))

parseSelectExtn : ExactLengthParser (Logging ∘ Dec) SelectExtn
parseSelectExtn n =
  parseEquivalent
    (transEquivalent (symEquivalent (Distribute.exactLength-Sum)) (equivalent×ₚ Select.equivalent))
    (parseSum
      (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion (λ ())) (λ where refl refl → refl)  parseAKIFields n)
      (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
        (parseSum
          (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion (λ ())) (λ where refl refl → refl) parseSKIFields n)
          (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
             (parseSum
               (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseKUFields n)
               (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                  (parseSum
                    (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseEKUFields n)
                    (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                       (parseSum
                         (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseBCFields n)
                         (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                            (parseSum
                              (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseIANFields n)
                              (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                 (parseSum
                                   (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseSANFields n)
                                   (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                      (parseSum
                                        (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseCertPolFields n)
                                        (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                           (parseSum
                                             (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseCRLDistFields n)
                                             (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                               (parseSum
                                                 (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseNCFields n)
                                                 (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                                   (parseSum
                                                     (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parsePCFields n)
                                                     (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                                       (parseSum
                                                         (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parsePMFields n)
                                                         (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                                           (parseSum
                                                             (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseINAPFields n)
                                                             (parseEquivalent (symEquivalent (Distribute.exactLength-Sum))
                                                               (parseSum
                                                                 (parseExtensionFields (_≟ _) TLV.nonnesting (TLV.noconfusion λ ()) (λ where refl refl → refl) parseAIAFields n)
                                                                 (parseExtensionFields (λ bs → T-dec) TLV.nonnesting (TLV.noconfusion (λ ())) (λ a₁ a₂ → T-unique a₁ a₂) parseOctetString n))))))))))))))))))))))))))))

parseExtension : Parser (Logging ∘ Dec) Extension
parseExtension = parseTLV _ here' _ parseSelectExtn

parseExtensionsSeq : Parser (Logging ∘ Dec) ExtensionsSeq
parseExtensionsSeq = parseNonEmptySeq here' _ TLV.nonempty TLV.nonnesting parseExtension

parseExtensions : Parser (Logging ∘ Dec) Extensions
parseExtensions =
  parseTLV _ here' _
    (parseExactLength TLV.nonnesting (tell $ here' String.++ ": length mismatch") parseExtensionsSeq)

