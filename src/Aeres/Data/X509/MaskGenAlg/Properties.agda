{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.HashAlg
open import Aeres.Data.X509.HashAlg.TCB.OIDs    as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB      as MaskGenAlg
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module MGF1 where
  open MaskGenAlg.MGF1
  module SupportedHashAlg where
    @0 noConfusion-SHA384- : NoConfusion HashAlg.SHA384 HashAlg.SHA512
    noConfusion-SHA384- = HashAlg.SHA-Like.noConfusion _ _
      
    @0 noConfusion-SHA256- :
      NoConfusion HashAlg.SHA256
                  (Sum HashAlg.SHA384 HashAlg.SHA512)
    noConfusion-SHA256- =
      Sum.noconfusion{A = HashAlg.SHA256}
       (HashAlg.SHA-Like.noConfusion _ _)
       (HashAlg.SHA-Like.noConfusion _ _)

    @0 noConfusion-SHA224- :
      NoConfusion HashAlg.SHA224
                  (Sum HashAlg.SHA256
                  (Sum HashAlg.SHA384
                       HashAlg.SHA512))
    noConfusion-SHA224- =
      Sum.noconfusion{A = HashAlg.SHA224}
       (HashAlg.SHA-Like.noConfusion _ _)
       (Sum.noconfusion{A = HashAlg.SHA224}
         (HashAlg.SHA-Like.noConfusion _ _)
         (HashAlg.SHA-Like.noConfusion _ _))

    @0 noConfusion-SHA1- :
      NoConfusion HashAlg.SHA1
                  (Sum HashAlg.SHA224
                  (Sum HashAlg.SHA256
                  (Sum HashAlg.SHA384
                       HashAlg.SHA512)))
    noConfusion-SHA1- =
      Sum.noconfusion{A = HashAlg.SHA1}
       (HashAlg.SHA-Like.noConfusion _ _)
       (Sum.noconfusion{A = HashAlg.SHA1}
         (HashAlg.SHA-Like.noConfusion _ _)
         (Sum.noconfusion{A = HashAlg.SHA1}
           (HashAlg.SHA-Like.noConfusion _ _)
           (HashAlg.SHA-Like.noConfusion _ _)))

    @0 nosubstrings : NoSubstrings SupportedHashAlg
    nosubstrings =
      Sum.nosubstrings TLV.nosubstrings
        (Sum.nosubstrings TLV.nosubstrings
          (Sum.nosubstrings TLV.nosubstrings
            (Sum.nosubstrings TLV.nosubstrings
              TLV.nosubstrings
              noConfusion-SHA384-)
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

    @0 unambiguous : Unambiguous SupportedHashAlg
    unambiguous =
      Sum.unambiguous
        (HashAlg.SHA-Like.unambiguous _)
        (Sum.unambiguous
          (HashAlg.SHA-Like.unambiguous _)
          (Sum.unambiguous
            (HashAlg.SHA-Like.unambiguous _)
            (Sum.unambiguous
              (HashAlg.SHA-Like.unambiguous _)
              (HashAlg.SHA-Like.unambiguous _)
              noConfusion-SHA384-)
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

    @0 nonmalleable : NonMalleable RawSupportedHashAlg
    nonmalleable =
       Sum.nonmalleable (HashAlg.SHA-Like.nonmalleable SHA1)
      (Sum.nonmalleable (HashAlg.SHA-Like.nonmalleable SHA224)
      (Sum.nonmalleable (HashAlg.SHA-Like.nonmalleable SHA256)
      (Sum.nonmalleable (HashAlg.SHA-Like.nonmalleable SHA384)
                        (HashAlg.SHA-Like.nonmalleable SHA512))))

  @0 unambiguous : Unambiguous MaskGenAlg
  unambiguous =
    TLV.unambiguous
      (DefinedByOID.unambiguous Param
        λ o →
         Parallel.unambiguous×ₚ SupportedHashAlg.unambiguous (λ where ≋-refl ≋-refl → refl))

  @0 nonmalleableParam : NonMalleable₁ RawParam
  nonmalleableParam p₁ p₂ eq =
    Parallel.nonmalleable₁ RawSupportedHashAlg SupportedHashAlg.nonmalleable
      (λ where _ ≋-refl ≋-refl → refl)
      p₁ p₂ eq

  @0 nonmalleable : NonMalleable RawMaskGenAlg
  nonmalleable = DefinedByOID.nonmalleable Param _ (λ {bs}{a} → nonmalleableParam{bs}{a})

  instance
    MG1Eq≋ : Eq≋ (DefinedByOIDFields Param)
    MG1Eq≋ =
      DefinedByOID.eq≋ Param λ o →
        Eq⇒Eq≋
          (Parallel.eqΣₚ
            (Sum.sumEq ⦃ Eq≋⇒Eq it ⦄
              ⦃ Sum.sumEq ⦃ it ⦄
                ⦃ Sum.sumEq ⦃ it ⦄
                  ⦃ Sum.sumEq ⦄ ⦄ ⦄)
            (λ _ → record { _≟_ = λ where ≋-refl ≋-refl → yes refl }))
