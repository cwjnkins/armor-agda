{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.SignAlg.ECDSA.TCB as ECDSA
import      Aeres.Data.X509.SignAlg.DSA.TCB   as DSA
import      Aeres.Data.X509.SignAlg.RSA.TCB   as RSA
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude
import      Data.List.Relation.Unary.Any.Properties as Any

open Aeres.Grammar.Parallel.TCB UInt8
open Aeres.Grammar.Sum.TCB      UInt8
open Aeres.Grammar.Definitions UInt8

module Aeres.Data.X509.SignAlg.TCB where

supportedSignAlgOIDs : List (Exists─ _ OIDValue)
supportedSignAlgOIDs =
  DSA.supportedSignAlgOIDs ++ ECDSA.supportedSignAlgOIDs ++ RSA.supportedSignAlgOIDs

UnsupportedParam : ∀ {@0 bs} → OID bs → @0 List UInt8 → Set
UnsupportedParam o =
     OctetStringValue
  ×ₚ const (False ((-, TLV.val o) ∈? supportedSignAlgOIDs))

UnsupportedSignAlg =
  DefinedByOID UnsupportedParam

data SignAlg (@0 bs : List UInt8) : Set where
  dsa : DSA.Supported bs → SignAlg bs
  ecdsa : ECDSA.Supported bs → SignAlg bs
  rsa   : RSA.Supported bs → SignAlg bs
  unsupported : UnsupportedSignAlg bs → SignAlg bs

erase
  : ∀ {@0 bs} → SignAlg bs
    → DefinedByOID (λ _ bs → Erased (OctetStringValue bs)) bs
erase (dsa x) =
  case DSA.erase x ret (const _) of λ where
    (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ p₁ o∈) bs≡₁) len≡ bs≡) →
      mkTLV len (mkOIDDefinedFields algOID p₁ bs≡₁) len≡ bs≡
erase (ecdsa x) =
  case ECDSA.erase x ret (const _) of λ where
    (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ p₁ o∈) bs≡₁) len≡ bs≡) →
      mkTLV len (mkOIDDefinedFields algOID p₁ bs≡₁) len≡ bs≡
erase (rsa x) =
  case RSA.erase x ret (const _) of λ where
    (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ p₁ o∈) bs≡₁) len≡ bs≡) →
      mkTLV len (mkOIDDefinedFields algOID p₁ bs≡₁) len≡ bs≡
erase (unsupported (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ p₁ _) bs≡₁) len≡ bs≡)) =
  mkTLV len (mkOIDDefinedFields algOID (─ p₁) bs≡₁) len≡ bs≡

getOID : ∀ {@0 bs} → SignAlg bs → Exists─ _ OID
getOID s = -, DefinedByOIDFields.oid (TLV.val (erase s))

getOIDBS : ∀ {@0 bs} → SignAlg bs → List UInt8
getOIDBS = ↑_ ∘ OID.serialize ∘ proj₂ ∘ getOID

postulate
  RawSignAlg : Raw SignAlg
