{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.PublicKey.Alg.TCB as Alg
  hiding (getOID)
open import Aeres.Data.X509.PublicKey.Alg.TCB.OIDs
open import Aeres.Data.X509.PublicKey.Val.TCB
open import Aeres.Data.X690-DER.OID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
import      Aeres.Grammar.Definitions.Iso
import      Aeres.Grammar.Definitions.NonMalleable
import      Aeres.Grammar.Seq.TCB
open import Aeres.Prelude

module Aeres.Data.X509.PublicKey.TCB where

open Aeres.Grammar.Definitions.Iso          UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8
open Aeres.Grammar.Seq.TCB                  UInt8

record PublicKeyFields (@0 bs : List UInt8) : Set where
  constructor mkPublicKeyFields
  field
    @0 {a p} : List UInt8
    alg : PublicKeyAlg a
    key : PublicKeyVal alg p
    @0 bs≡ : bs ≡ a ++ p

PublicKeyFieldsRep : @0 List UInt8 → Set
PublicKeyFieldsRep = &ₚᵈ PublicKeyAlg PublicKeyVal

equivalent : Equivalent PublicKeyFieldsRep PublicKeyFields
proj₁ equivalent (mk&ₚ fstₚ₁ sndₚ₁ bs≡) = mkPublicKeyFields fstₚ₁ sndₚ₁ bs≡
proj₂ equivalent (mkPublicKeyFields alg key bs≡) = mk&ₚ alg key bs≡

RawPublicKeyFieldsRep : Raw PublicKeyFieldsRep
RawPublicKeyFieldsRep = Raw&ₚᵈ RawPublicKeyAlg RawPublicKeyVal

RawPublicKeyFields : Raw PublicKeyFields
RawPublicKeyFields =
  Iso.raw equivalent RawPublicKeyFieldsRep

PublicKey = TLV Tag.Sequence PublicKeyFields

RawPublicKey : Raw PublicKey
RawPublicKey = RawTLV _ RawPublicKeyFields

getOID : ∀ {@0 bs} → (pk : PublicKey bs) → OID _
getOID x = Alg.getOID (PublicKeyFields.alg (TLV.val x))

