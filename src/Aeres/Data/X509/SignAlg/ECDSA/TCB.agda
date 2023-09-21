{-# OPTIONS --subtyping #-}

open import Aeres.Binary
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.ECDSA.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

supportedSignAlgOIDs : List (Exists─ _ OIDValue)
supportedSignAlgOIDs =
  (-, OIDs.ECDSA.SHA1) ∷ (-, OIDs.ECDSA.SHA224) ∷ (-, OIDs.ECDSA.SHA256) ∷ (-, OIDs.ECDSA.SHA384) ∷ [ -, OIDs.ECDSA.SHA512 ]

ECDSA-Like-Params : ∀ {@0 bs} → (o : OIDValue bs) → ∀ {@0 bs'} → (o' : OID bs')
                  → @0 List UInt8 → Set
ECDSA-Like-Params o o' = (_≡ []) ×ₚ const (_≋_{A = OIDValue} (TLV.val o') o)

ECDSA-Like : {@0 bs : List UInt8} (o : OIDValue bs) → @0 List UInt8 → Set
ECDSA-Like o = DefinedByOID (ECDSA-Like-Params o)

SHA1   = ECDSA-Like OIDs.ECDSA.SHA1
SHA224 = ECDSA-Like OIDs.ECDSA.SHA224
SHA256 = ECDSA-Like OIDs.ECDSA.SHA256
SHA384 = ECDSA-Like OIDs.ECDSA.SHA384
SHA512 = ECDSA-Like OIDs.ECDSA.SHA512

Supported : @0 List UInt8 → Set
Supported =
   Sum SHA1
  (Sum SHA224
  (Sum SHA256
  (Sum SHA384
       SHA512)))

erase
  : ∀ {@0 bs} → Supported bs
    → DefinedByOID
        (λ o → (Erased ∘ OctetStringValue) ×ₚ const (True ((-, TLV.val o) ∈? supportedSignAlgOIDs)))
        bs
erase (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl refl) bs≡₁) len≡ bs≡)) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt refl) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl refl) bs≡₁) len≡ bs≡))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt refl) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl refl) bs≡₁) len≡ bs≡)))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt refl) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl refl) bs≡₁) len≡ bs≡))))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt refl) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl refl) bs≡₁) len≡ bs≡))))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt refl) bs≡₁) len≡ bs≡
