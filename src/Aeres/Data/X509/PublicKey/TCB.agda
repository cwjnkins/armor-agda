{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.PublicKey.Alg.TCB as Alg
open import Aeres.Data.X509.PublicKey.Alg.TCB.OIDs
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.TCB where

open Alg using (PublicKeyAlg)

record PublicKeyFields (@0 bs : List UInt8) : Set where
  constructor mkPublicKeyFields
  field
    @0 {a p} : List UInt8
    alg : PublicKeyAlg a
    key : PublicKeyVal (proj₂ (Alg.getOID alg)) p

PublicKey = TLV Tag.Sequence PublicKeyFields

getOID : ∀ {@0 bs} → PublicKey bs → Exists─ _ OID
getOID x = Alg.getOID (PublicKeyFields.alg (TLV.val x))
