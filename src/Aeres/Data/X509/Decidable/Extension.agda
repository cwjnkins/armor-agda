{-# OPTIONS --subtyping #-}

open import Aeres.Prelude

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.AIAFields
open import Aeres.Data.X509.Decidable.AKIFields
open import Aeres.Data.X509.Decidable.BCFields
open import Aeres.Data.X509.Decidable.Boool
open import Aeres.Data.X509.Decidable.CRLDistFields
open import Aeres.Data.X509.Decidable.CertPolFields
open import Aeres.Data.X509.Decidable.EKUFields
open import Aeres.Data.X509.Decidable.IANFields
open import Aeres.Data.X509.Decidable.KUFields
open import Aeres.Data.X509.Decidable.OID
open import Aeres.Data.X509.Decidable.SANFields
open import Aeres.Data.X509.Decidable.SKIFields
open import Aeres.Data.X509.Decidable.Seq
open import Aeres.Data.X509.Decidable.TLV
open import Aeres.Data.X509.Properties as Props
open import Aeres.Grammar.Definitions
open import Aeres.Grammar.Parser
open import Aeres.Grammar.Properties
open import Data.List.Properties
open import Data.Nat.Properties
  hiding (_≟_)

module Aeres.Data.X509.Decidable.Extension where

open Base256

module parseExtension where
  here' = "parseExtension"

  parseExtensionFields
    : ∀ {t} {@0 A : @0 List Dig → Set}
      → @0  NonNesting _ A → @0 NoConfusion _ Generic.Boool A
      → Parser _ (Logging ∘ Dec) A
      → ExactLengthParser _ (Logging ∘ Dec) (X509.ExtensionFields t A)
  parseExtensionFields{t}{A} nn nc p₁ n =
    parseEquivalent _
      (transEquivalent _
        (symEquivalent _ (Distribute.exactLength-& _))
        (equivalent×ₚ _ Props.Extension.equivalent))
      (parse&ᵈ _
        (withinLength-nonnesting _ (nonnesting×ₚ₁ _ Props.TLV.nonnesting))
        (λ where
          (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ fstₚ₂ (─ sndₚ₂) refl) → ‼
            subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ x (─ sndₚ₂) refl)
              (unambiguous×ₚ _ (TLV.unambiguous (Seq.unambiguous Props.OIDSub.unambiguous)) (λ where refl refl → refl) fstₚ₁ fstₚ₂)
                (subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ fstₚ₁ (─ x) refl) (≤-irrelevant sndₚ₁ sndₚ₂)
                  refl))
        (parse≤ _ n
          (parse× _ Props.TLV.nonnesting (λ where _ refl refl → refl) (tell $ here' String.++ ": fields: impossible")
            parseOID (parseLit _ (tell $ here' String.++ ": fields: underflow") (tell $ here' String.++ ": fields: literal mismatch" ) _))
          (nonnesting×ₚ₁ _ Props.TLV.nonnesting) (tell $ here' String.++ ": fields: overflow"))
        λ where
          {._} (mk×ₚ (mk×ₚ fstₚ₁ refl refl) (─ bsLen) refl) →
            parseOption₁&₁ _ parseBool p₁ Props.TLV.nonnesting nn nc (tell $ here' String.++ ": length mismatch (bool)") (n - length t))


  parseSelectExtn : ExactLengthParser _ (Logging ∘ Dec) X509.SelectExtn
  parseSelectExtn n =
    parseEquivalent _
      (transEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _)) (equivalent×ₚ _ Props.Extension.SelectExtn.equivalent))
      (parseSum _
        (parseExtensionFields Props.TLV.nonnesting (TLV.noconfusion (λ ())) parseAKIFields n)
        (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
          (parseSum _
            (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion (λ ())) parseSKIFields n)
            (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
               (parseSum _
                 (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseKUFields n)
                 (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                    (parseSum _
                      (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseEKUFields n)
                      (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                         (parseSum _
                           (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseBCFields n)
                           (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                              (parseSum _
                                (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseIANFields n)
                                (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                   (parseSum _
                                     (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseSANFields n)
                                     (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                        (parseSum _
                                          (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseCertPolFields n)
                                          (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                             (parseSum _
                                               (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseCRLDistFields n)
                                               (parseExtensionFields Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) parseAIAFields n))))))))))))))))))

  parseExtension : Parser _ (Logging ∘ Dec) X509.Extension
  parseExtension = parseTLV _ "extension" _ parseSelectExtn

  parseExtensionsSeq : Parser _ (Logging ∘ Dec) X509.ExtensionsSeq
  parseExtensionsSeq = parseSeq "extension" _ Props.TLV.nonempty Props.TLV.nonnesting parseExtension

  parseExtensions : Parser _ (Logging ∘ Dec) X509.Extensions
  parseExtensions =
    parseTLV _ "extensions" _
      (parseExactLength _ Props.TLV.nonnesting (tell "parseExtensions: length mismatch") parseExtensionsSeq)
