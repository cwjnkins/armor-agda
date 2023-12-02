open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Val.EC
open import Aeres.Data.X509.PublicKey.Val.RSA
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.BitString
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.Eq where

open Aeres.Grammar.Definitions UInt8

eq≋' : ∀ {@0 bs} → (a : PublicKeyAlg bs) → (d : Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported))
       → Eq≋ (PublicKeyVal' a d)
eq≋' o (yes (here px)) = it
eq≋' o (yes (there (here px))) = it
eq≋' o (no ¬p) = it

eq≋ : ∀ {@0 bs} → {a : PublicKeyAlg bs} → Eq≋ (PublicKeyVal a)
Eq≋._≋?_ (eq≋ {a = a}) v₁ v₂ =
  case Eq≋._≋?_ (eq≋' a (_ ∈? _)) v₁ v₂ ret (const _) of λ where
    (no ¬p) → no λ where ≋-refl → contradiction ≋-refl ¬p
    (yes ≋-refl) → yes ≋-refl
