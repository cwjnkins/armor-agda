open import Aeres.Binary
open import Aeres.Data.X509.DirectoryString
import      Aeres.Data.X690-DER.OID.Properties as OID
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X509.Name.RDN.ATV.OIDs
open import Aeres.Data.X509.Name.RDN.ATV.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.Strings.IA5String
open import Aeres.Data.X690-DER.Strings.PrintableString
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
open import Aeres.Prelude
open import Data.Sum.Properties

module Aeres.Data.X509.Name.RDN.ATV.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8

@0 unambiguous : Unambiguous ATV
unambiguous = TLV.unambiguous (DefinedByOID.unambiguous _ λ o → u o ((-, TLV.val o) ∈? Supported))
  where
  u : ∀ {@0 bs} → (o : OID bs) (d : Dec ((-, TLV.val o) ∈ Supported)) → Unambiguous (ATVParam o d)
  u o (no ¬p) = DirectoryString.unambiguous
  u o (yes (here px)) = PrintableString.unambiguous
  u o (yes (there (here px))) = Parallel.unambiguous PrintableString.unambiguous (λ _ → inRange-unique{A = ℕ}{B = ℕ})
  u o (yes (there (there (here px)))) = PrintableString.unambiguous
  u o (yes (there (there (there (here px))))) = TLV.unambiguous IA5String.unambiguous
  u o (yes (there (there (there (there (here px)))))) = TLV.unambiguous IA5String.unambiguous
instance
  Eq≋ATV : Eq≋ (DefinedByOIDFields  λ o → ATVParam o ((-, TLV.val o) ∈? Supported))
  Eq≋ATV = DefinedByOID.eq≋ _ λ o → eq o ((-, TLV.val o) ∈? Supported)
    where
    eq : ∀ {@0 bs} (o : OID bs) (d : Dec ((-, TLV.val o) ∈ Supported)) → Eq≋ (ATVParam o d)
    eq o (no ¬p) = it
    eq o (yes (here px)) = it
    eq o (yes (there (here px))) = Parallel.eq≋Σₚ it (λ _ → record { _≟_ = λ x y → yes (inRange-unique{A = ℕ}{B = ℕ} x y) })
    eq o (yes (there (there (here px)))) = it
    eq o (yes (there (there (there (here px))))) = it
    eq o (yes (there (there (there (there (here px)))))) = it

@0 nonmalleable : NonMalleable RawATV
nonmalleable = DefinedByOID.nonmalleable ATVParam' _ {R = RawATVParam} nm 
  where
  nm : NonMalleable₁ RawATVParam
  nm {a = o}{bs₁}{bs₂} =
    case (-, TLV.val o) ∈? Supported
    ret (λ o? →
           (p₁ : ATVParam o o? bs₁) (p₂ : ATVParam o o? bs₂)
           → toRawATVParam o? p₁ ≡ toRawATVParam o? p₂
           → _≡_{A = Exists─ (List UInt8) (ATVParam o o?)} (─ bs₁ , p₁) (─ bs₂ , p₂))
    of λ where
      (no ¬p) p₁ p₂ eq →
        ‼ (DirectoryString.nonmalleable p₁ p₂ (inj₁-injective eq))
      (yes (here px)) p₁ p₂ eq →
        ‼ (PrintableString.nonmalleable p₁ p₂ (inj₁-injective (inj₂-injective eq)))
      (yes (there (here px))) p₁ p₂ eq →
        ‼ Parallel.nonmalleable₁ _ PrintableString.nonmalleable (λ _ → inRange-unique{A = ℕ}{B = ℕ}) p₁ p₂
            (inj₁-injective (inj₂-injective (inj₂-injective eq)))
      (yes (there (there (here px)))) p₁ p₂ eq →
        ‼ PrintableString.nonmalleable p₁ p₂
            (inj₁-injective (inj₂-injective (inj₂-injective (inj₂-injective eq))))
      (yes (there (there (there (here px))))) p₁ p₂ eq →
        ‼ IA5String.nonmalleable p₁ p₂
            (inj₁-injective (inj₂-injective (inj₂-injective (inj₂-injective eq))))
      (yes (there (there (there (there (here px)))))) p₁ p₂ eq →
        ‼ IA5String.nonmalleable p₁ p₂
            (inj₂-injective (inj₂-injective (inj₂-injective (inj₂-injective eq))))
