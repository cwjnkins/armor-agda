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
open import Aeres.Data.X509.Decidable.Octetstring
open import Aeres.Data.X509.Decidable.SANFields
open import Aeres.Data.X509.Decidable.SKIFields
open import Aeres.Data.X509.Decidable.SequenceOf
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
    : ∀ {@0 P} {@0 A : @0 List Dig → Set} (P? : ∀ bs → Dec (P bs))
      → @0  NonNesting _ A → @0 NoConfusion _ Generic.Boool A → Unambiguous _ P
      → Parser _ (Logging ∘ Dec) A
      → ExactLengthParser _ (Logging ∘ Dec) (X509.ExtensionFields P A)
  parseExtensionFields P? nn nc ua p n =
    parseEquivalent _
      (transEquivalent _
        (symEquivalent _ (Distribute.exactLength-& _))
        (equivalent×ₚ _ Props.Extension.ExtensionFields.equivalent))
      (parse&ᵈ _
        (withinLength-nonnesting _ (nonnesting×ₚ₁ _ Props.TLV.nonnesting))
        (λ where
          (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (mk×ₚ fstₚ₂ (─ sndₚ₂) refl) → ‼
            subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ x (─ sndₚ₂) refl)
              (unambiguous×ₚ _ OID.unambiguous (λ where (─ pf₁) (─ pf₂) → ‼ cong ─_ (ua pf₁ pf₂) ) fstₚ₁ fstₚ₂)
                (subst₀ (λ x → mk×ₚ fstₚ₁ (─ sndₚ₁) refl ≡ mk×ₚ fstₚ₁ (─ x) refl) (≤-irrelevant sndₚ₁ sndₚ₂)
                  refl))
        (parse≤ _ n
          (parse×Dec _ Props.TLV.nonnesting (return (Level.lift tt)) parseOID λ x → erased? (P? x))
            (nonnesting×ₚ₁ _ Props.TLV.nonnesting) (tell $ here' String.++ ": fields: overflow"))
        λ where
          (singleton r r≡) (mk×ₚ (mk×ₚ fstₚ₁ (─ sndₚ₁) refl) (─ bsLen) refl) →
            subst₀ (λ x → Parser _ (Logging ∘ Dec) (ExactLength _ _ (n ∸ x))) r≡
              (parseOption₁&₁ _ parseBool p Props.TLV.nonnesting nn nc ((tell $ here' String.++ ": length mismatch (bool)")) (n - r)))

  parseSelectExtn : ExactLengthParser _ (Logging ∘ Dec) X509.SelectExtn
  parseSelectExtn n =
    parseEquivalent _
      (transEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _)) (equivalent×ₚ _ Props.Extension.SelectExtn.equivalent))
      (parseSum _
        (parseExtensionFields (_≟ _) Props.TLV.nonnesting (TLV.noconfusion (λ ())) (λ where refl refl → refl)  parseAKIFields n)
        (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
          (parseSum _
            (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion (λ ())) (λ where refl refl → refl) parseSKIFields n)
            (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
               (parseSum _
                 (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseKUFields n)
                 (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                    (parseSum _
                      (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseEKUFields n)
                      (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                         (parseSum _
                           (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseBCFields n)
                           (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                              (parseSum _
                                (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseIANFields n)
                                (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                   (parseSum _
                                     (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseSANFields n)
                                     (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                        (parseSum _
                                          (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseCertPolFields n)
                                          (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                             (parseSum _
                                               (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseCRLDistFields n)
                                               (parseEquivalent _ (symEquivalent _ (Distribute.exactLength-Sum _))
                                                  (parseSum _
                                                    (parseExtensionFields (_≟ _) Props.TLV.nonnesting (Props.TLV.noconfusion λ ()) (λ where refl refl → refl) parseAIAFields n)
                                                    (parseExtensionFields (λ bs → T-dec) Props.TLV.nonnesting (TLV.noconfusion (λ ())) (λ a₁ a₂ → T-unique a₁ a₂) parseOctetstring n))))))))))))))))))))

  parseExtension : Parser _ (Logging ∘ Dec) X509.Extension
  parseExtension = parseTLV _ "extension" _ parseSelectExtn

  parseExtensionsSeq : Parser _ (Logging ∘ Dec) X509.ExtensionsSeq
  parseExtensionsSeq = parseNonEmptySeq "extension" _ Props.TLV.nonempty Props.TLV.nonnesting parseExtension

  parseExtensions : Parser _ (Logging ∘ Dec) X509.Extensions
  parseExtensions =
    parseTLV _ "extensions" _
      (parseExactLength _ Props.TLV.nonnesting (tell "parseExtensions: length mismatch") parseExtensionsSeq)

open parseExtension public using (parseExtensions)
