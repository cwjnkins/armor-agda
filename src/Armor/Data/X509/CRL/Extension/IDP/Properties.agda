open import Armor.Binary
open import Armor.Data.X509.GeneralNames
open import Armor.Data.X509.Extension.CRLDistPoint.DistPoint.Name
open import Armor.Data.X509.CRL.Extension.IDP.TCB
open import Armor.Data.X690-DER.BitString
open import Armor.Data.X690-DER.Boool
open import Armor.Data.X690-DER.TLV
open import Armor.Data.X690-DER.SequenceOf
open import Armor.Data.X690-DER.Sequence
import      Armor.Data.X690-DER.Tag as Tag
open import Armor.Data.X690-DER.Default
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
import      Armor.Grammar.Properties
import      Armor.Grammar.Parallel
import      Armor.Grammar.Seq
open import Armor.Prelude

module Armor.Data.X509.CRL.Extension.IDP.Properties where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Properties  UInt8
open Armor.Grammar.Parallel    UInt8
open Armor.Grammar.Seq         UInt8

iso : Iso IDPFieldsSeqFieldsRep IDPFieldsSeqFields
proj₁ iso = equivalentIDPFieldsSeqFields
proj₁ (proj₂ iso) (mk×ₚ(mk&ₚ (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₃ sndₚ₁ refl) refl) (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₄ sndₚ₂ refl) refl) bs≡) prop)
  with T-irrel prop
... | prop'
  with ‼ T-unique prop prop'
... | refl = (subst₀ (λ eq → mk×ₚ (mk&ₚ _ _ eq ) prop
                            ≡ mk×ₚ (mk&ₚ _ _ bs≡ ) prop) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl)
proj₂ (proj₂ iso) (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons indirectCRL onlyContainsAttributeCerts prop bs≡)
  with T-irrel prop
... | prop'
  with ‼ T-unique prop prop'
... | refl = (subst₀ (λ eq → mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons indirectCRL onlyContainsAttributeCerts prop eq
                            ≡ mkIDPFieldsSeqFields _ _ _ _ _ _ _  bs≡) (≡-unique bs≡ _) refl)

@0 unambiguous : Unambiguous IDPFields
unambiguous = TLV.unambiguous (TLV.unambiguous ua₃)
  where
  postulate
    ns : NoSubstrings Rep₁
  -- ns = Seq.nosubstringsOption₁{A = DistPointName}{B = &ₚ (Default [ Tag.A81 ]Boool [ Tag.A81 ]falseBoool)
  --                                                         (Default [ Tag.A82 ]Boool [ Tag.A82 ]falseBoool)}
  --        TLV.nosubstrings
  --          (Sequence.nosubstringsDefault₂ _ _ TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ()))
  --          (symNoConfusion {!Parallel.noconfusion₁!})


  ua₁ : Unambiguous Rep₁
  ua₁ = Sequence.unambiguousOptionDefaultDefault _ _ Name.unambiguous TLV.nosubstrings TLV.nonempty
                                                 (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
                                                 (TLV.unambiguous Boool.unambiguousValue) TLV.nonempty
                                                 (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
  ua₂ : Unambiguous Rep₂
  ua₂ = Sequence.unambiguousOptionDefaultDefault _ _ (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
                                                 (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
                                                 (TLV.unambiguous Boool.unambiguousValue) TLV.nonempty
                                                 (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion λ ())
  ua₃ : Unambiguous IDPFieldsSeqFields
  ua₃ = Iso.unambiguous iso
          (Parallel.unambiguous (Seq.unambiguous ua₁ ns ua₂) (λ _ → T-unique))

@0 nonmalleable : NonMalleable RawIDPFields
nonmalleable = TLV.nonmalleable
  (TLV.nonmalleable (Iso.nonmalleable iso RawIDPFieldsSeqFieldsRep
    (Parallel.nonmalleable₁ RawRep₃
      (Seq.nonmalleable
        (Seq.nonmalleable
          (Option.nonmalleable _ Name.nonmalleable)
            (Seq.nonmalleable
              (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
              (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))))
        (Seq.nonmalleable
          (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
          (Seq.nonmalleable
            (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
            (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue)))))
      λ a p₁ p₂ → T-unique p₁ p₂)))
