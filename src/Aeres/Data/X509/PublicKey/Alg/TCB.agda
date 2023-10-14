{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
open import Aeres.Data.X509.PublicKey.Alg.ECPKParameters.TCB
  hiding (equivalent)
open import Aeres.Data.X509.PublicKey.Alg.RSAPKParameters
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable
-- import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.TCB where

open Aeres.Grammar.Definitions.Iso          UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Sum.TCB                  UInt8

PKParameters' : ∀ {@0 bs} → (o : OID bs) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → @0 List UInt8 → Set
PKParameters' o (no ¬p) = OctetStringValue
PKParameters' o (yes (here px)) = RSAPKParameters
PKParameters' o (yes (there (here px))) = ECPKParameters

PKParameters : AnyDefinedByOID
PKParameters o = PKParameters' o ((-, TLV.val o) ∈? OIDs.Supported)

RawPKParameters“ : Raw (Sum OctetStringValue (Sum Null ECPKParameters))
RawPKParameters“ = RawSum RawOctetStringValue (RawSum RawNull RawECPKParameters)

RawPKParameters : Raw₁ RawOID PKParameters
toRawPKParameters
  : ∀ {@0 bs₁} → (o : OID bs₁) (o∈? : Dec ((-, TLV.val o) ∈ OIDs.Supported)) → ∀ {@0 bs₂}
    → PKParameters' o o∈? bs₂ → Raw₁.D RawPKParameters (Raw.to RawOID o)

Raw₁.D RawPKParameters o = Raw.D RawPKParameters“
Raw₁.to RawPKParameters o p = toRawPKParameters o ((-, TLV.val o) ∈? OIDs.Supported) p

toRawPKParameters o (no ¬p) p = Raw.to RawPKParameters“ (inj₁ p)
toRawPKParameters o (yes (here px)) p = Raw.to RawPKParameters“ (inj₂ (inj₁ p))
toRawPKParameters o (yes (there (here px))) p = Raw.to RawPKParameters“ (inj₂ (inj₂ p))

PublicKeyAlg : @0 List UInt8 → Set
PublicKeyAlg = DefinedByOID PKParameters

RawPublicKeyAlg : Raw PublicKeyAlg
RawPublicKeyAlg = RawDefinedByOID RawPKParameters

getOID : ∀ {@0 bs} → (a : PublicKeyAlg bs) → OID _
getOID a = DefinedByOIDFields.oid (TLV.val a) 
