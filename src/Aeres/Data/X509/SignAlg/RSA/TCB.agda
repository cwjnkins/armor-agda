{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X509.AlgorithmIdentifier.TCB
open import Aeres.Data.X509.SignAlg.RSA.PSS.TCB
open import Aeres.Data.X509.SignAlg.TCB.OIDs  as OIDs
import      Aeres.Data.X509.HashAlg.TCB       as HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs  as OIDs
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509.SignAlg.RSA.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Sum         UInt8

supportedSignAlgOIDs : List (Exists─ _ OIDValue)
supportedSignAlgOIDs =
    (-, OIDs.RSA.MD2) ∷ (-, OIDs.RSA.MD5)
  ∷ (-, OIDs.RSA.SHA1) ∷ (-, OIDs.RSA.SHA224) ∷ (-, OIDs.RSA.SHA256) ∷ (-, OIDs.RSA.SHA384) ∷ (-, OIDs.RSA.SHA512)
  ∷ [ -, OIDs.RSA.PSS ]

MD2    = HashAlg.SHA-Like OIDs.RSA.MD2
MD5    = HashAlg.SHA-Like OIDs.RSA.MD5
SHA1   = HashAlg.SHA-Like OIDs.RSA.SHA1
SHA224 = HashAlg.SHA-Like OIDs.RSA.SHA224
SHA256 = HashAlg.SHA-Like OIDs.RSA.SHA256
SHA384 = HashAlg.SHA-Like OIDs.RSA.SHA384
SHA512 = HashAlg.SHA-Like OIDs.RSA.SHA512

Supported : @0 List UInt8 → Set
Supported =
  (Sum MD2
  (Sum MD5
  (Sum SHA1
  (Sum SHA224
  (Sum SHA256
  (Sum SHA384
  (Sum SHA512
       PSS)))))))

erase : ∀ {@0 bs}
        → Supported bs
        → AlgorithmIdentifier
            (λ o →    (Erased ∘ OctetStringValue)
                   ×ₚ const (True ((-, TLV.val o) ∈? supportedSignAlgOIDs)))
            bs
erase (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡)) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡)))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡))))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡)))))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡))))))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₁ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡)))))))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡
erase (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (Sum.inj₂ (mkTLV len (mkAlgIDFields o(mk×ₚ _ ≋-refl refl)bs≡') len≡ bs≡)))))))) =
  mkTLV len (mkAlgIDFields o ((mk×ₚ (─ self) tt refl)) bs≡') len≡ bs≡

getOID : ∀ {@0 bs} → Supported bs → Exists─ _ OID
getOID s = -, AlgorithmIdentifierFields.algOID (TLV.val (erase s))
