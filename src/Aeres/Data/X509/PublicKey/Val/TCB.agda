{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.TCB where

PublicKeyVal' : ∀ {@0 bs} → (o : OID bs) → Dec ((-, TLV.val o) ∈ supportedPublicKeyAlgs) → @0 List UInt8 → Set
PublicKeyVal' o (yes (here px)) = RSABitString
PublicKeyVal' o (yes (there (here px))) = ECBitString
PublicKeyVal' o (no ¬p) = BitString

record PublicKeyVal {@0 bs₁ : List UInt8} (o : OID bs₁) (@0 bs : List UInt8) : Set where
  constructor mkPKVal
  field
    val : PublicKeyVal' o (_ ∈? _) bs
