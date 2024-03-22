open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
open import Armor.Data.X509.Semantic.Cert.Utils
import      Armor.Grammar.IList
import      Armor.Grammar.Definitions
import      Armor.Grammar.Option
open import Armor.Prelude
open import Relation.Nullary.Implication

module Armor.Data.X509.Semantic.Cert.R18 where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.IList       UInt8
open Armor.Grammar.Option      UInt8

--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
--- only for end-entity certificate

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.12

{- NOTE: This semantic check is only a sanity check: more fine-grained checks
-- depend upon specifics of the application using X.509 PKI, which are currently
-- outside the scope of ARMOR
-}

-- The following key usage purposes are defined:
--
-- anyExtendedKeyUsage OBJECT IDENTIFIER ::= { id-ce-extKeyUsage 0 }
--
-- id-kp OBJECT IDENTIFIER ::= { id-pkix 3 }
data KeyPurpose : Set where
  serverAuth clientAuth codeSigning emailProtection timeStamping ocspSigning : KeyPurpose

keyPurposeConsistentWithKU : ∀ {@0 bs} → KeyPurpose → ExtensionFieldKU bs → Bool
keyPurposeConsistentWithKU serverAuth ku =
-- id-kp-serverAuth             OBJECT IDENTIFIER ::= { id-kp 1 }
-- -- TLS WWW server authentication
-- -- Key usage bits that may be consistent: digitalSignature,
-- -- keyEncipherment or keyAgreement
  or (map (assertsKUBitField ku) (Extension.KUFields.digitalSignature ∷ Extension.KUFields.keyEncipherment ∷ [ Extension.KUFields.keyAgreement ]))
keyPurposeConsistentWithKU clientAuth ku =
-- id-kp-clientAuth             OBJECT IDENTIFIER ::= { id-kp 2 }
-- -- TLS WWW client authentication
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or keyAgreement
  or (map (assertsKUBitField ku) (Extension.KUFields.digitalSignature ∷ [ Extension.KUFields.keyAgreement ]))
keyPurposeConsistentWithKU codeSigning ku =
-- id-kp-codeSigning             OBJECT IDENTIFIER ::= { id-kp 3 }
-- -- Signing of downloadable executable code
-- -- Key usage bits that may be consistent: digitalSignature
  assertsKUBitField ku Extension.KUFields.digitalSignature
keyPurposeConsistentWithKU emailProtection ku =
-- id-kp-emailProtection         OBJECT IDENTIFIER ::= { id-kp 4 }
-- -- Email protection
-- -- Key usage bits that may be consistent: digitalSignature,
-- -- nonRepudiation, and/or (keyEncipherment or keyAgreement)

-- NOTE: This is very coarse grained. For example, OpenSSL distinguishes between
-- smime signing and smime encrypting, which are consistent with a subset of the
-- below fields (meaning, more strict)
  or (map (assertsKUBitField ku)
    (  Extension.KUFields.digitalSignature ∷ Extension.KUFields.nonRepudation
     ∷ Extension.KUFields.keyEncipherment ∷ [ Extension.KUFields.keyAgreement ]))
keyPurposeConsistentWithKU timeStamping ku =
-- id-kp-timeStamping            OBJECT IDENTIFIER ::= { id-kp 8 }
-- -- Binding the hash of an object to a time
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or nonRepudiation
  or (map (assertsKUBitField ku) (Extension.KUFields.digitalSignature ∷ [ Extension.KUFields.nonRepudation ]))
keyPurposeConsistentWithKU ocspSigning ku =
-- id-kp-OCSPSigning            OBJECT IDENTIFIER ::= { id-kp 9 }
-- -- Signing OCSP responses
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or nonRepudiation
  or (map (assertsKUBitField ku) (Extension.KUFields.digitalSignature ∷ [ Extension.KUFields.nonRepudation ]))

keyPurposeToEKUOID : KeyPurpose → Exists─ _ OIDValue
keyPurposeToEKUOID serverAuth = _ , OIDs.EKU.ServerAuth
keyPurposeToEKUOID clientAuth = _ , OIDs.EKU.ClientAuth
keyPurposeToEKUOID codeSigning = _ , OIDs.EKU.CodeSign
keyPurposeToEKUOID emailProtection = _ , OIDs.EKU.EmailProt
keyPurposeToEKUOID timeStamping = _ , OIDs.EKU.TimeStamp
keyPurposeToEKUOID ocspSigning = _ , OIDs.EKU.OCSPSign

KeyPurposeConsistentWithEKU : ∀ {@0 bs} → KeyPurpose → ExtensionFieldEKU bs → Set
KeyPurposeConsistentWithEKU kp eku =
    keyPurposeToEKUOID kp ∈ ekuPurps
  ⊎ (_ , OIDs.EKU.AnyExtendedKeyUsage) ∈ ekuPurps
  where
  ekuPurps = map (λ where (─ _ , x) → _ , TLV.val x) (toList (Extension.FieldEKU.getKeyPurposeIDs eku))

R18' : ∀ {@0 bs₁ bs₂} → KeyPurpose → Option ExtensionFieldKU bs₁ → Option ExtensionFieldEKU bs₂ → Set
R18' kp none none = ⊤
R18' kp none (some eku) = KeyPurposeConsistentWithEKU kp eku
R18' kp (some ku) none = T (keyPurposeConsistentWithKU kp ku)
R18' kp (some ku) (some eku) = T (keyPurposeConsistentWithKU kp ku) × KeyPurposeConsistentWithEKU kp eku

R18 : KeyPurpose → ∀ {@0 bs} → Cert bs → Set
R18 kp c = R18' kp (proj₂ (Cert.getKU c)) (proj₂ (Cert.getEKU c))

r18 : (kp : KeyPurpose) → ∀ {@0 bs} → (c : Cert bs) → Dec (R18 kp c)
r18 kp c = r18' kp (proj₂ (Cert.getKU c)) (proj₂ (Cert.getEKU c))
  where
  keyPurposeConsistentWithEKU?
    : ∀ {@0 bs} → (kp : KeyPurpose) (eku : ExtensionFieldEKU bs)
      → Dec (KeyPurposeConsistentWithEKU kp eku)
  keyPurposeConsistentWithEKU? kp eku =
    _ ∈? _ ⊎-dec _ ∈? _

  r18' : ∀ {@0 bs₁ bs₂} → (kp : KeyPurpose) → (ku : Option ExtensionFieldKU bs₁) (eku : Option ExtensionFieldEKU bs₂)
         → Dec (R18' kp ku eku)
  r18' kp none none = yes tt
  r18' kp none (some eku) = keyPurposeConsistentWithEKU? kp eku
  r18' kp (some ku) none = T-dec
  r18' kp (some ku) (some eku) = T-dec ×-dec keyPurposeConsistentWithEKU? kp eku

