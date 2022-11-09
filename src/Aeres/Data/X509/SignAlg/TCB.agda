{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Int.TCB
open import Aeres.Data.X690-DER.Null.TCB
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.HashAlg.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
import      Aeres.Data.X509.SignAlg.ECDSA.TCB as ECDSA
import      Aeres.Data.X509.SignAlg.DSA.TCB   as DSA
import      Aeres.Data.X509.SignAlg.RSA.TCB   as RSA
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

module Aeres.Data.X509.SignAlg.TCB where

supportedSignAlgOIDs : List (Exists─ _ OIDValue)
supportedSignAlgOIDs =
    (-, OIDs.ECDSA.SHA1) ∷ (-, OIDs.ECDSA.SHA224) ∷ (-, OIDs.ECDSA.SHA256) ∷ (-, OIDs.ECDSA.SHA384) ∷ (-, OIDs.ECDSA.SHA512)
  ∷ (-, OIDs.DSA.SHA1) ∷ (-, OIDs.DSA.SHA224) ∷ (-, OIDs.DSA.SHA256)
  ∷ (-, OIDs.RSA.MD2) ∷ (-, OIDs.RSA.MD5) ∷ (-, OIDs.RSA.SHA1) ∷ (-, OIDs.RSA.SHA224) ∷ (-, OIDs.RSA.SHA256) ∷ (-, OIDs.RSA.SHA384) ∷ [ (-, OIDs.RSA.SHA512) ]

UnsupportedSignAlg =
  TLV Tag.Sequence (&ₚ (Σₚ OID (λ _ o → False ((-, TLV.val o) ∈? supportedSignAlgOIDs))) OctetStringValue)

SignAlg : @0 List UInt8 → Set
SignAlg =
   Sum ECDSA.SHA1
  (Sum ECDSA.SHA224
  (Sum ECDSA.SHA256
  (Sum ECDSA.SHA384
  (Sum ECDSA.SHA512
  (Sum DSA.SHA1
  (Sum DSA.SHA224
  (Sum DSA.SHA256
  (Sum RSA.MD2
  (Sum RSA.MD5
  (Sum RSA.SHA1
  (Sum RSA.SHA224
  (Sum RSA.SHA256
  (Sum RSA.SHA384
  (Sum RSA.SHA512
  (Sum RSA.PSS
       UnsupportedSignAlg)))))))))))))))

getOID : ∀ {@0 bs} → SignAlg bs → Exists─ _ OID
getOID (Sum.inj₁ x) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₁ x)) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x))))))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ x)))))))))))))))) =
  -, AlgorithmIdentifierFields.algOID (TLV.val x)
getOID (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ x)))))))))))))))) =
  -, fstₚ (fstₚ (TLV.val x))
