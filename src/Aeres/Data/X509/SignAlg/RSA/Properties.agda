{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.TCB.OIDs  as OIDs
import      Aeres.Data.X509.SignAlg.RSA.TCB   as RSA
import      Aeres.Data.X509.HashAlg.TCB       as HashAlg
import      Aeres.Data.X509.HashAlg.Properties as HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs  as OIDs
import      Aeres.Data.X509.MaskGenAlg.TCB    as MaskGenAlg
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module PSS where
  Rep : @0 List UInt8 → Set
  Rep =  &ₚ (Option RSA.PSS.SupportedHashAlg)
        (&ₚ (Option MaskGenAlg.MGF1.MaskGenAlg)
        (&ₚ (Option Int)
            (Option (Σₚ Int λ _ i → getVal i ≡ ℤ.1ℤ))))

  postulate
    equiv : Equivalent Rep RSA.PSSParamFields

  module SupportedHashAlg where

    @0 nonnesting : NonNesting RSA.PSS.SupportedHashAlg
    nonnesting =
      nonnestingSum TLV.nonnesting
        (nonnestingSum TLV.nonnesting
          (nonnestingSum TLV.nonnesting
            (nonnestingSum TLV.nonnesting TLV.nonnesting (HashAlg.SHA-Like.noConfusion _ _))
            (NoConfusion.sumₚ{A = HashAlg.SHA256}
              (HashAlg.SHA-Like.noConfusion OIDs.SHA256 _)
              (HashAlg.SHA-Like.noConfusion OIDs.SHA256 _)))
          (NoConfusion.sumₚ{A = HashAlg.SHA224} (HashAlg.SHA-Like.noConfusion OIDs.SHA224 _)
            (NoConfusion.sumₚ{A = HashAlg.SHA224}
              (HashAlg.SHA-Like.noConfusion OIDs.SHA224 _)
              (HashAlg.SHA-Like.noConfusion OIDs.SHA224 _))))
        (NoConfusion.sumₚ{A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion OIDs.SHA1 _)
          (NoConfusion.sumₚ{A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion OIDs.SHA1 _)
            (NoConfusion.sumₚ{A = HashAlg.SHA1} (HashAlg.SHA-Like.noConfusion OIDs.SHA1 _)
              (HashAlg.SHA-Like.noConfusion OIDs.SHA1 _))))
