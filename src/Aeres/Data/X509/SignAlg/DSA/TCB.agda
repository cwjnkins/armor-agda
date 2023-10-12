{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Null.TCB
import      Aeres.Data.X509.SignAlg.TCB.OIDs as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.Sequence.DefinedByOID.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parallel.TCB
import      Aeres.Grammar.Sum.TCB
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.DSA.TCB where

open Aeres.Grammar.Definitions  UInt8
open Aeres.Grammar.Sum.TCB      UInt8
open Aeres.Grammar.Parallel.TCB UInt8

supportedSignAlgOIDs : List (Exists─ _ OIDValue)
supportedSignAlgOIDs =
  (-, OIDs.DSA.SHA1) ∷ (-, OIDs.DSA.SHA224) ∷ [ -, OIDs.DSA.SHA256 ]

DSA-Like-Params : ∀ {@0 bs} → (o : OIDValue bs) → ∀ {@0 bs'} → (o' : OID bs')
                  → @0 List UInt8 → Set
DSA-Like-Params o o' = Null ×ₚ const (_≋_{A = OIDValue} (TLV.val o') o)

RawDSALikeParams : ∀ {@0 bs} (o : OIDValue bs) → Raw₁ RawOID (DSA-Like-Params o)
Raw₁.D (RawDSALikeParams o) o' = Raw.D RawNull
Raw₁.to (RawDSALikeParams o) o' p = Raw.to RawNull (fstₚ p)

DSA-Like : {@0 bs : List UInt8} (o : OIDValue bs) → @0 List UInt8 → Set
DSA-Like o = DefinedByOID (DSA-Like-Params o)

RawDSALike : ∀ {@0 bs} (o : OIDValue bs) → Raw (DSA-Like o)
RawDSALike o = RawDefinedByOID (RawDSALikeParams o)

SHA1   = DSA-Like OIDs.DSA.SHA1
SHA224 = DSA-Like OIDs.DSA.SHA224
SHA256 = DSA-Like OIDs.DSA.SHA256

Supported : @0 List UInt8 → Set
Supported =
   Sum SHA1
  (Sum SHA224
       SHA256)

RawSupported : Raw Supported
RawSupported =
   RawSum (RawDSALike OIDs.DSA.SHA1)
  (RawSum (RawDSALike OIDs.DSA.SHA224)
          (RawDSALike OIDs.DSA.SHA256))

erase
  : ∀ {@0 bs} → Supported bs
    → DefinedByOID
        (λ o → (Erased ∘ OctetStringValue) ×ₚ const (True ((-, TLV.val o) ∈? supportedSignAlgOIDs)))
        bs
erase (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡)) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (mkTLV len (mkOIDDefinedFields algOID (mk×ₚ _ ≋-refl) bs≡₁) len≡ bs≡))) =
  mkTLV len (mkOIDDefinedFields algOID (mk×ₚ (─ self) tt) bs≡₁) len≡ bs≡
