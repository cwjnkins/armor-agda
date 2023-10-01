{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.SignAlg.DSA.Properties as DSA
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X509.SignAlg.ECDSA.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parallel    UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module ECDSA-Like where
  @0 unambiguous : ∀ {@0 bs} → (o : OIDValue bs) → Unambiguous (ECDSA-Like o)
  unambiguous o =
    TLV.unambiguous
      (DefinedByOID.unambiguous
        _
        λ where
          o' (mk×ₚ refl ≋-refl) (mk×ₚ refl ≋-refl) → refl)

  @0 noConfusion
    : ∀ {@0 bs₁ bs₂} → (o₁ : OIDValue bs₁) (o₂ : OIDValue bs₂)
      → {t : False (o₁ ≋? o₂)}
      → NoConfusion (ECDSA-Like o₁) (ECDSA-Like o₂)
  noConfusion o₁ o₂ {t} =
    DefinedByOID.noConfusionParam (ECDSA-Like-Params o₁)
      λ where
        o (mk×ₚ refl ≋-refl) (mk×ₚ refl ≋-refl) →
          contradiction ≋-refl (toWitnessFalse t)

@0 unambiguous : Unambiguous Supported
unambiguous =
  Sum.unambiguous (ECDSA-Like.unambiguous _)
    (Sum.unambiguous (ECDSA-Like.unambiguous _)
      (Sum.unambiguous (ECDSA-Like.unambiguous _)
        (Sum.unambiguous (ECDSA-Like.unambiguous _)
          (ECDSA-Like.unambiguous _)
          (ECDSA-Like.noConfusion _ _))
        (NoConfusion.sumₚ {A = SHA256}
          (ECDSA-Like.noConfusion _ _)
          (ECDSA-Like.noConfusion _ _)))
      (NoConfusion.sumₚ{A = SHA224}
        (ECDSA-Like.noConfusion _ _)
          (NoConfusion.sumₚ {A = SHA224} (ECDSA-Like.noConfusion _ _)
            (ECDSA-Like.noConfusion _ _))))
    (NoConfusion.sumₚ {A = SHA1} (ECDSA-Like.noConfusion _ _)
      (NoConfusion.sumₚ {A = SHA1} (ECDSA-Like.noConfusion _ _)
        (NoConfusion.sumₚ {A = SHA1} (ECDSA-Like.noConfusion _ _) (ECDSA-Like.noConfusion _ _))))
