{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
open import Aeres.Data.X509.HashAlg
open import Aeres.Data.X509.HashAlg.TCB.OIDs    as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB      as MaskGenAlg
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.Properties where

open Aeres.Grammar.Definitions UInt8
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
      NoConfusion.sumₚ{A = HashAlg.SHA256}
       (HashAlg.SHA-Like.noConfusion _ _)
       (HashAlg.SHA-Like.noConfusion _ _)

    @0 noConfusion-SHA224- :
      NoConfusion HashAlg.SHA224
                  (Sum HashAlg.SHA256
                  (Sum HashAlg.SHA384
                       HashAlg.SHA512))
    noConfusion-SHA224- =
      NoConfusion.sumₚ{A = HashAlg.SHA224}
       (HashAlg.SHA-Like.noConfusion _ _)
       (NoConfusion.sumₚ{A = HashAlg.SHA224}
         (HashAlg.SHA-Like.noConfusion _ _)
         (HashAlg.SHA-Like.noConfusion _ _))

    @0 noConfusion-SHA1- :
      NoConfusion HashAlg.SHA1
                  (Sum HashAlg.SHA224
                  (Sum HashAlg.SHA256
                  (Sum HashAlg.SHA384
                       HashAlg.SHA512)))
    noConfusion-SHA1- =
      NoConfusion.sumₚ{A = HashAlg.SHA1}
       (HashAlg.SHA-Like.noConfusion _ _)
       (NoConfusion.sumₚ{A = HashAlg.SHA1}
         (HashAlg.SHA-Like.noConfusion _ _)
         (NoConfusion.sumₚ{A = HashAlg.SHA1}
           (HashAlg.SHA-Like.noConfusion _ _)
           (HashAlg.SHA-Like.noConfusion _ _)))

    @0 nonnesting : NonNesting SupportedHashAlg
    nonnesting =
      nonnestingSum TLV.nonnesting
        (nonnestingSum TLV.nonnesting
          (nonnestingSum TLV.nonnesting
            (nonnestingSum TLV.nonnesting
              TLV.nonnesting
              noConfusion-SHA384-)
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

    @0 unambiguous : Unambiguous SupportedHashAlg
    unambiguous =
      unambiguousSum
        (HashAlg.SHA-Like.unambiguous _)
        (unambiguousSum
          (HashAlg.SHA-Like.unambiguous _)
          (unambiguousSum
            (HashAlg.SHA-Like.unambiguous _)
            (unambiguousSum
              (HashAlg.SHA-Like.unambiguous _)
              (HashAlg.SHA-Like.unambiguous _)
              noConfusion-SHA384-)
            noConfusion-SHA256-)
          noConfusion-SHA224-)
        noConfusion-SHA1-

  @0 unambiguous : Unambiguous MaskGenAlg
  unambiguous =
    TLV.unambiguous
      (AlgorithmIdentifier.unambiguous Param
        λ o →
         unambiguous×ₚ SupportedHashAlg.unambiguous (λ where ≋-refl ≋-refl → refl))

  instance
    MG1Eq≋ : Eq≋ (AlgorithmIdentifierFields Param)
    MG1Eq≋ =
      AlgorithmIdentifier.eq≋ Param λ o →
        Eq⇒Eq≋
          (eqΣₚ
            (sumEq ⦃ Eq≋⇒Eq it ⦄
              ⦃ sumEq ⦃ it ⦄
                ⦃ sumEq ⦃ it ⦄
                  ⦃ sumEq ⦄ ⦄ ⦄)
            (λ _ → record { _≟_ = λ where ≋-refl ≋-refl → yes refl }))
