{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.Extension
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey
open import Aeres.Data.X509.RDN
open import Aeres.Data.X509.SignAlg
open import Aeres.Data.X509.TBSCert.TCB
open import Aeres.Data.X509.TBSCert.UID.TCB
open import Aeres.Data.X509.TBSCert.Version
open import Aeres.Data.X509.Validity
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X690-DER.Time.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Parallel  
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Seq
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.TBSCert.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Seq         UInt8

Rep₁ = &ₚ (Option SubUID) (Option Extensions)
Rep₂ = &ₚ (Option IssUID) Rep₁
Rep₃ = &ₚ (PublicKey ×ₚ Singleton) Rep₂
Rep₄ = &ₚ Name Rep₃
Rep₅ = &ₚ Validity Rep₄
Rep₆ = &ₚ Name Rep₅
Rep₇ = &ₚ SignAlg Rep₆

Rep : @0 List UInt8 → Set
Rep = (&ₚ (&ₚ (Option Version) Int) Rep₇)

equivalent : Equivalent
               Rep
               TBSCertFields
proj₁ equivalent (mk&ₚ (mk&ₚ fstₚ₁ sndₚ₁ refl) (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ (mk&ₚ fstₚ₄ (mk&ₚ fstₚ₅ (mk&ₚ (mk×ₚ fstₚ₆ s) (mk&ₚ fstₚ₇ (mk&ₚ fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) bs≡) =
  mkTBSCertFields fstₚ₁ sndₚ₁ fstₚ₂ fstₚ₃ fstₚ₄ fstₚ₅ fstₚ₆ s fstₚ₇ fstₚ₈ sndₚ₂
    (trans₀ bs≡ (solve (++-monoid UInt8)))
proj₂ equivalent (mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions bs≡) =
  mk&ₚ (mk&ₚ version serial refl) (mk&ₚ signAlg (mk&ₚ issuer (mk&ₚ validity (mk&ₚ subject (mk&ₚ (mk×ₚ pk pkBytes) (mk&ₚ issuerUID (mk&ₚ subjectUID extensions refl) refl) refl) refl) refl) refl) refl)
    (trans₀ bs≡ (solve (++-monoid UInt8)))

iso : Iso Rep TBSCertFields
proj₁ iso = equivalent
proj₁ (proj₂ iso) (mk&ₚ (mk&ₚ{bs₁ = bs₁}{bs₂} fstₚ₁ sndₚ₁ refl) (mk&ₚ{bs₁ = bs₃} fstₚ₂ (mk&ₚ{bs₁ = bs₄} fstₚ₃ (mk&ₚ{bs₁ = bs₅} fstₚ₄ (mk&ₚ{bs₁ = bs₆} fstₚ₅ (mk&ₚ{bs₁ = bs₇} (mk×ₚ fstₚ₆ s) (mk&ₚ{bs₁ = bs₈} fstₚ₇ (mk&ₚ{bs₁ = bs₉}{bs₁₀} fstₚ₈ sndₚ₂ refl) refl) refl) refl) refl) refl) refl) bs≡) =
  subst₀ (λ eq → mk&ₚ _ _ eq ≡ mk&ₚ _ _ bs≡) (≡-unique bs≡ (trans₀ (trans₀ bs≡ _) _)) refl
proj₂ (proj₂ iso) (mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions bs≡) =
  subst₀ (λ eq → mkTBSCertFields version serial signAlg issuer validity subject pk pkBytes issuerUID subjectUID extensions eq ≡ mkTBSCertFields _ _ _ _ _ _ _ _ _ _ _ bs≡) (≡-unique bs≡ _) refl

-- postulate
--   instance
--     TBSEq : Eq (Exists─ (List UInt8) TBSCertFields)

@0 unambiguous : Unambiguous TBSCertFields
unambiguous =
  Iso.unambiguous iso
    (Seq.unambiguous
      (Unambiguous.unambiguous-option₁&₁
        (TLV.unambiguous (TLV.unambiguous λ {xs} → Int.unambiguous{xs}))
        TLV.nosubstrings
        (TLV.unambiguous Int.unambiguous)
        (TLV.noconfusion λ ()))
      (NonNesting.noconfusion-option&₁
        TLV.nosubstrings TLV.nosubstrings (TLV.noconfusion λ ()))
      (Seq.unambiguous SignAlg.unambiguous SignAlg.nosubstrings
        (Seq.unambiguous RDN.unambiguous TLV.nosubstrings
          (Seq.unambiguous (TLV.unambiguous Validity.unambiguous) TLV.nosubstrings
            (Seq.unambiguous RDN.unambiguous TLV.nosubstrings
              (Seq.unambiguous
                (Parallel.unambiguous×ₚ PublicKey.unambiguous (λ where self self → refl))
                  (Parallel.nosubstrings₁ TLV.nosubstrings)
                  (Unambiguous.option₃&₂
                    (TLV.unambiguous BitString.unambiguous) TLV.nosubstrings TLV.nonempty
                    (TLV.unambiguous BitString.unambiguous) TLV.nosubstrings TLV.nonempty
                    (TLV.unambiguous Extension.ExtensionSeq.unambiguous)
                    TLV.nonempty (TLV.noconfusion λ ()) (TLV.noconfusion λ ()) (TLV.noconfusion (λ ())))))))))
