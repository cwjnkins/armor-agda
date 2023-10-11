{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB.OIDs as OIDs
import      Aeres.Data.X509.PublicKey.Alg.EC.TCB   as EC
import      Aeres.Data.X509.PublicKey.Alg.RSA.TCB  as RSA
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.Alg.TCB where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.Parallel.TCB UInt8
open Aeres.Grammar.Sum.TCB      UInt8

open EC  using (EC)
open RSA using (RSA)

supportedPublicKeyAlgs : List (Exists─ _ OIDValue)
supportedPublicKeyAlgs =
  (-, OIDs.RSA) ∷ [ -, OIDs.EC ]

UnsupportedParam : ∀ {@0 bs} → (o : OID bs) → @0 List UInt8 → Set
UnsupportedParam o =
     OctetStringValue
  ×ₚ const (False (((-, TLV.val o)) ∈? supportedPublicKeyAlgs))

RawUnsupportedParam : Raw₁ RawOID UnsupportedParam
Raw₁.D RawUnsupportedParam o = Raw.D RawOctetStringValue
Raw₁.to RawUnsupportedParam o p = Raw.to RawOctetStringValue (fstₚ p)

UnsupportedPublicKeyAlg =
  DefinedByOID UnsupportedParam

RawUnsupportedPublicKeyAlg : Raw UnsupportedPublicKeyAlg
RawUnsupportedPublicKeyAlg = RawDefinedByOID RawUnsupportedParam

PublicKeyAlg : @0 List UInt8 → Set
PublicKeyAlg =
   Sum RSA
  (Sum EC
       UnsupportedPublicKeyAlg)

RawPublicKeyAlg : Raw PublicKeyAlg
RawPublicKeyAlg = RawSum RSA.RawRSA (RawSum EC.RawEC RawUnsupportedPublicKeyAlg)

getOID : ∀ {@0 bs} → PublicKeyAlg bs → Exists─ _ OID
getOID (Sum.inj₁ x) =
  RSA.getOID x
getOID (Sum.inj₂ (Sum.inj₁ x)) =
  EC.getOID x
getOID (Sum.inj₂ (Sum.inj₂ x)) =
  -, DefinedByOIDFields.oid (TLV.val x)
