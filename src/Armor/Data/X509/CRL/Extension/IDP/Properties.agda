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
proj₁ (proj₂ iso) (mk×ₚ (mk&ₚ{bs₁ = bs₁} fstₚ₁ (mk&ₚ {bs₁ = bs₂} fstₚ₂ (mk&ₚ {bs₁ = bs₃} fstₚ₃ (mk&ₚ {bs₁ = bs₄} fstₚ₄ (mk&ₚ {bs₁ = bs₅}{bs₆} fstₚ₅ sndₚ₂ refl) refl) refl) refl) bs≡) prop)
  with T-irrel prop
... | prop'
  with ‼ T-unique prop prop'
... | refl = subst₀ (λ eq → mk×ₚ (mk&ₚ _ _ eq) prop ≡ mk×ₚ (mk&ₚ _ _ bs≡) prop)
           (≡-unique bs≡ (trans₀ bs≡
  (trans
  (sym
   (trans (sym (cong₂ _++_ (++-identityʳ bs₁) refl))
    (trans
     (cong₂ _++_ (++-identityʳ bs₁)
      (trans (sym (cong₂ _++_ (++-identityʳ bs₂) refl))
       (trans
        (cong₂ _++_ (++-identityʳ bs₂)
         (trans (sym (cong₂ _++_ (++-identityʳ bs₃) refl))
          (trans
           (cong₂ _++_ (++-identityʳ bs₃)
            (trans (sym (cong₂ _++_ (++-identityʳ bs₄) refl))
             (trans
              (cong₂ _++_ (++-identityʳ bs₄)
               (trans (sym (cong₂ _++_ (++-identityʳ bs₅) refl))
                (trans (cong₂ _++_ (++-identityʳ bs₅) (++-identityʳ bs₆)) refl)))
              refl)))
           refl)))
        refl)))
     refl)))
   (trans (sym (cong₂ _++_ (++-identityʳ bs₁) refl))
    (trans
     (cong₂ _++_ (++-identityʳ bs₁)
      (trans (sym (cong₂ _++_ (++-identityʳ bs₂) refl))
       (trans
        (cong₂ _++_ (++-identityʳ bs₂)
         (trans (sym (cong₂ _++_ (++-identityʳ bs₃) refl))
          (trans
           (cong₂ _++_ (++-identityʳ bs₃)
            (trans (sym (cong₂ _++_ (++-identityʳ bs₄) refl))
             (trans
              (cong₂ _++_ (++-identityʳ bs₄)
               (trans (sym (cong₂ _++_ (++-identityʳ bs₅) refl))
                (trans (cong₂ _++_ (++-identityʳ bs₅) (++-identityʳ bs₆)) refl)))
              refl)))
           refl)))
        refl)))
     refl)))))
           refl
proj₂ (proj₂ iso) (mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons indirectCRL onlyContainsAttributeCerts prop bs≡)
  with T-irrel prop
... | prop'
  with ‼ T-unique prop prop'
... | refl = (subst₀ (λ eq → mkIDPFieldsSeqFields distributionPoint onlyContainsUserCerts onlyContainsCACerts onlySomeReasons indirectCRL onlyContainsAttributeCerts prop eq
                            ≡ mkIDPFieldsSeqFields _ _ _ _ _ _ _  bs≡) (≡-unique bs≡ _) refl)

@0 uaRep : Unambiguous RepIDPField
uaRep = Sequence.unambiguous₂Option₂Default₄ _ _ _ _
       Name.unambiguous TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous BitString.unambiguousValue) TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous Boool.unambiguousValue) TLV.nosubstrings TLV.nonempty
       (TLV.unambiguous Boool.unambiguousValue) TLV.nonempty
       (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
       (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
       (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))
       (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ())) (TLV.noconfusion (λ ()))

@0 unambiguous : Unambiguous IDPFields
unambiguous = TLV.unambiguous (TLV.unambiguous (Iso.unambiguous iso
  (Parallel.unambiguous uaRep (λ a p₁ p₂ → T-unique p₁ p₂))))

@0 nonmalleable : NonMalleable RawIDPFields
nonmalleable = TLV.nonmalleable (TLV.nonmalleable (Iso.nonmalleable iso
                 RawIDPFieldsSeqFieldsRep
                 (Parallel.nonmalleable₁ RawRepIDPField
                 (Seq.nonmalleable (Option.nonmalleable _ Name.nonmalleable)
                   (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
                     (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
                       (Seq.nonmalleable (Option.nonmalleable _ (TLV.nonmalleable BitString.nonmalleableValue))
                         (Seq.nonmalleable (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue))
                                           (Default.nonmalleable _ (TLV.nonmalleable Boool.nonmalleableValue)))))))
                         (λ a p₁ p₂ → T-unique p₁ p₂))))
