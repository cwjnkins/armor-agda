{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X509.PublicKey.Val.EC
open import Aeres.Data.X509.PublicKey.Val.RSA
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.Properties where

open Aeres.Grammar.Definitions UInt8

@0 nonnesting : ∀ {@0 bs} → (o : OID bs) → NonNesting (PublicKeyVal o)
nonnesting o ++≡ (mkPKVal v₁) (mkPKVal v₂) = help o (_ ∈? _) ++≡ v₁ v₂
  where
  help : ∀ {@0 bs} → (o : OID bs)
         → (d : Dec ((-, TLV.val o) ∈ supportedPublicKeyAlgs))
         → NonNesting (PublicKeyVal' o d)
  help o (yes (here px)) = TLV.nonnesting
  help o (yes (there (here px))) = nonnesting×ₚ₁ TLV.nonnesting
  help o (no ¬p) = TLV.nonnesting

@0 unambiguous : ∀ {@0 bs} → (o : OID bs) → Unambiguous (PublicKeyVal o)
unambiguous{bs} o (mkPKVal v₁) (mkPKVal v₂) = cong mkPKVal (help o (_ ∈? _) v₁ v₂)
  where
  help : ∀ {@0 bs} → (o : OID bs) → (d : Dec ((-, TLV.val o) ∈ supportedPublicKeyAlgs))
         →  Unambiguous (PublicKeyVal' o d)
  help o (yes (here px)) = TLV.unambiguous RSA.unambiguous
  help o (yes (there (here px))) = EC.unambiguous
  help o (no ¬p) = TLV.unambiguous BitString.unambiguous
