{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X509.MaskGenAlg
open import Aeres.Data.X509.SignAlg.RSA.PSS.TCB
  renaming (module SupportedHashAlg to SH)
import      Aeres.Data.X509.SignAlg.TCB.OIDs        as OIDs
open import Aeres.Data.X690-DER.Int
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag                 as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.PSS.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module Fields where
  module SupportedHashAlg where
    @0 noConfusion-SHA1-
      : NoConfusion
          HashAlg.SHA1
          (Sum HashAlg.SHA224
          (Sum HashAlg.SHA256
          (Sum HashAlg.SHA384
               HashAlg.SHA512)))
    noConfusion-SHA1- =
      (NoConfusion.sumₚ {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _)
        (NoConfusion.sumₚ {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _)
          (NoConfusion.sumₚ {A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion _ _) (HashAlg.SHA-Like.noConfusion _ _))))

    @0 noConfusion-SHA224-
      : NoConfusion HashAlg.SHA224
          (Sum HashAlg.SHA256 (Sum HashAlg.SHA384 HashAlg.SHA512))
    noConfusion-SHA224- =
      NoConfusion.sumₚ {A = HashAlg.SHA224} (HashAlg.SHA-Like.noConfusion _ _)
       (NoConfusion.sumₚ{A = HashAlg.SHA224}
         (HashAlg.SHA-Like.noConfusion _ _) (HashAlg.SHA-Like.noConfusion _ _))

    @0 noConfusion-SHA256-
      : NoConfusion HashAlg.SHA256 (Sum HashAlg.SHA384 HashAlg.SHA512)
    noConfusion-SHA256- =
      NoConfusion.sumₚ{A = HashAlg.SHA256}
       (HashAlg.SHA-Like.noConfusion _ _)
       (HashAlg.SHA-Like.noConfusion _ _)

    @0 unambiguous : Unambiguous SupportedHashAlg
    unambiguous =
      unambiguousSum (HashAlg.SHA-Like.unambiguous _)
        (unambiguousSum (HashAlg.SHA-Like.unambiguous _)
          (unambiguousSum (HashAlg.SHA-Like.unambiguous _)
            (unambiguousSum
              (HashAlg.SHA-Like.unambiguous _)
              (HashAlg.SHA-Like.unambiguous _)
              (HashAlg.SHA-Like.noConfusion _ _))
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

    @0 nonnesting : NonNesting SupportedHashAlg
    nonnesting =
      nonnestingSum TLV.nonnesting
        (nonnestingSum TLV.nonnesting
          (nonnestingSum TLV.nonnesting
            (nonnestingSum TLV.nonnesting TLV.nonnesting
              (HashAlg.SHA-Like.noConfusion _ _))
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

    nonempty : NonEmpty SupportedHashAlg
    nonempty = TLV.nonempty ∘ SH.erase

  Rep : @0 List UInt8 → Set
  Rep =  &ₚ (TLV Tag.AA0 (Option SupportedHashAlg))
        (&ₚ (TLV Tag.AA1 (Option MGF1.MaskGenAlg))
        (&ₚ (TLV Tag.AA2 (Option Int))
            (TLV Tag.AA3 (Option (Σₚ Int λ _ i → Int.getVal i ≡ ℤ.1ℤ)))))

  equiv : Equivalent Rep PSSParamFields
  proj₁ equiv (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ sndₚ₁ refl) refl) bs≡) =
    mkPSSParam fstₚ₁ fstₚ₂ fstₚ₃ sndₚ₁ bs≡
  proj₂ equiv (mkPSSParam hashAlg maskGenAlgo saltLength trailerField bs≡) =
    mk&ₚ hashAlg (mk&ₚ maskGenAlgo (mk&ₚ saltLength trailerField refl) refl) bs≡

  iso   : Iso Rep PSSParamFields
  proj₁ iso = equiv
  proj₁ (proj₂ iso) (mk&ₚ fstₚ₁ (mk&ₚ fstₚ₂ (mk&ₚ fstₚ₃ sndₚ₁ refl) refl) bs≡) = refl
  proj₂ (proj₂ iso) (mkPSSParam hashAlg maskGenAlgo saltLength trailerField bs≡) = refl

  @0 unambiguous : Unambiguous PSSParamFields
  unambiguous =
    isoUnambiguous iso
      (unambiguous&ₚ
        (TLV.unambiguous
          (Unambiguous.option₁ SupportedHashAlg.unambiguous SupportedHashAlg.nonempty))
        TLV.nonnesting
        (unambiguous&ₚ
          (TLV.unambiguous
            (Unambiguous.option₁ MGF1.unambiguous TLV.nonempty))
          TLV.nonnesting
          (unambiguous&ₚ
            (TLV.unambiguous (Unambiguous.option₁ (TLV.unambiguous Int.unambiguous)
              TLV.nonempty))
            TLV.nonnesting
            (TLV.unambiguous
              (Unambiguous.option₁
                (unambiguousΣₚ (TLV.unambiguous Int.unambiguous)
                  (λ _ → ≡-unique))
                (nonemptyΣₚ₁ TLV.nonempty))))))

@0 unambiguous : Unambiguous PSS
unambiguous =
  TLV.unambiguous
    (DefinedByOID.unambiguous PSSParam
      λ o →
       unambiguous×ₚ Fields.unambiguous
         (λ where
           ≋-refl ≋-refl → refl))

