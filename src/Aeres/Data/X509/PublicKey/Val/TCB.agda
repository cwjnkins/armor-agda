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

PublicKeyVal : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
PublicKeyVal o = PublicKeyVal' o (_ ∈? _)
