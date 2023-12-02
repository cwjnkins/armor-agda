open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB as Alg
  hiding (getOID)
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Val.EC.TCB
open import Aeres.Data.X509.PublicKey.Val.RSA.TCB
open import Aeres.Data.X690-DER.BitString.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Val.TCB where

open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Sum.TCB                  UInt8

PublicKeyVal' : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported) → @0 List UInt8 → Set
PublicKeyVal' a (no ¬p) = BitString
PublicKeyVal' a (yes (here px)) = RSABitString
PublicKeyVal' a (yes (there (here px))) = ECBitString

PublicKeyVal : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → @0 List UInt8 → Set
PublicKeyVal a = PublicKeyVal' a ((-, TLV.val (Alg.getOID a)) ∈? OIDs.Supported)

RawPublicKeyVal“ : Raw (Sum BitString (Sum RSABitString ECBitString))
RawPublicKeyVal“ = RawSum RawBitString (RawSum RawRSABitString RawECBitString)

RawPublicKeyVal : Raw₁ RawPublicKeyAlg PublicKeyVal
toRawPublicKeyVal : ∀ {@0 bs₁} → (a : PublicKeyAlg bs₁) → (o∈? : Dec ((-, TLV.val (Alg.getOID a)) ∈ OIDs.Supported))
                    → ∀ {@0 bs₂} → PublicKeyVal' a o∈? bs₂ → Raw₁.D RawPublicKeyVal (Raw.to RawPublicKeyAlg a)

Raw₁.D RawPublicKeyVal o = Raw.D RawPublicKeyVal“
Raw₁.to RawPublicKeyVal o p = toRawPublicKeyVal o ((-, TLV.val (Alg.getOID o)) ∈? OIDs.Supported) p

toRawPublicKeyVal a (no ¬p) p = Raw.to RawPublicKeyVal“ (inj₁ p)
toRawPublicKeyVal a (yes (here px)) p = Raw.to RawPublicKeyVal“ (inj₂ (inj₁ p))
toRawPublicKeyVal a (yes (there (here px))) p = Raw.to RawPublicKeyVal“ (inj₂ (inj₂ p))
