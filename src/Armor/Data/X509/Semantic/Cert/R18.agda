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

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.3
-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.2.1.12
--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
--- only for end-entity certificate

-- The following key usage purposes are defined:
--
-- anyExtendedKeyUsage OBJECT IDENTIFIER ::= { id-ce-extKeyUsage 0 }
--
-- id-kp OBJECT IDENTIFIER ::= { id-pkix 3 }

data KeyPurpose-ConsistentWith-KeyUsage {@0 bs₁} (ku : ExtensionFieldKU bs₁) : ∀ {@0 bs₂} → OIDValue bs₂ → Set where
-- anyExtendedKeyUsage OBJECT IDENTIFIER ::= { id-ce-extKeyUsage 0 }
  anyKeyUsage : KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.AnyExtendedKeyUsage

-- id-kp-serverAuth             OBJECT IDENTIFIER ::= { id-kp 1 }
-- -- TLS WWW server authentication
-- -- Key usage bits that may be consistent: digitalSignature,
-- -- keyEncipherment or keyAgreement
  serverAuth : T (  assertsKUBitField ku Extension.KUFields.digitalSignature
                  ∨ assertsKUBitField ku Extension.KUFields.keyEncipherment
                  ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
               → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.ServerAuth

-- id-kp-clientAuth             OBJECT IDENTIFIER ::= { id-kp 2 }
-- -- TLS WWW client authentication
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or keyAgreement
  clientAuth : T (  assertsKUBitField ku Extension.KUFields.digitalSignature
                  ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
               → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.ClientAuth
               
-- id-kp-codeSigning             OBJECT IDENTIFIER ::= { id-kp 3 }
-- -- Signing of downloadable executable code
-- -- Key usage bits that may be consistent: digitalSignature
  codeSign : T (assertsKUBitField ku Extension.KUFields.digitalSignature)
             → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.CodeSign

-- id-kp-emailProtection         OBJECT IDENTIFIER ::= { id-kp 4 }
-- -- Email protection
-- -- Key usage bits that may be consistent: digitalSignature,
-- -- nonRepudiation, and/or (keyEncipherment or keyAgreement)
  emailProtection : T (  assertsKUBitField ku Extension.KUFields.digitalSignature
                       ∨ assertsKUBitField ku Extension.KUFields.nonRepudation
                       ∨ assertsKUBitField ku Extension.KUFields.keyEncipherment
                       ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
                    → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.EmailProt
  
-- id-kp-timeStamping            OBJECT IDENTIFIER ::= { id-kp 8 }
-- -- Binding the hash of an object to a time
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or nonRepudiation
  timeStamping : T (  assertsKUBitField ku Extension.KUFields.digitalSignature
                    ∨ assertsKUBitField ku Extension.KUFields.nonRepudation)
                 → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.TimeStamp

-- id-kp-OCSPSigning            OBJECT IDENTIFIER ::= { id-kp 9 }
-- -- Signing OCSP responses
-- -- Key usage bits that may be consistent: digitalSignature
-- -- and/or nonRepudiation
  ocspSigning : T (  assertsKUBitField ku Extension.KUFields.digitalSignature
                   ∨ assertsKUBitField ku Extension.KUFields.nonRepudation)
                → KeyPurpose-ConsistentWith-KeyUsage ku OIDs.EKU.OCSPSign

  -- TODO
  unknown : ∀ {@0 bs} → (o : OIDValue bs) → (─ bs , o) ∉ OIDs.EKU.SupportedKeyUsageIDs
            → KeyPurpose-ConsistentWith-KeyUsage ku o

KeyPurposes-ConsistentWith-KeyUsage : ∀ {@0 bs₁} → ExtensionFieldKU bs₁ → List (Exists─ _ OID) → Set
KeyPurposes-ConsistentWith-KeyUsage ku oids =
  All (λ oid → KeyPurpose-ConsistentWith-KeyUsage ku (TLV.val (proj₂ oid))) oids

R18' : ∀ {@0 bs₁ bs₂} → Option ExtensionFieldKU bs₁ → Option ExtensionFieldEKU bs₂ → Set
R18' none _ = ⊤
R18' (some _) none = ⊤
R18' (some ku) (some eku) = KeyPurposes-ConsistentWith-KeyUsage ku (toList (Extension.FieldEKU.getKeyPurposeIDs eku))

R18 : ∀ {@0 bs} → Cert bs → Set
R18 c = R18' (proj₂ (Cert.getKU c)) (proj₂ (Cert.getEKU c))

-- R18 : ∀ {@0 bs} → Cert bs → Set
-- R18 c = T (checkPurposeConsistency (Cert.getKU c) (getEKUOIDList (Cert.getEKU c)))

isKeyPurposeConsistentWithKeyUsage : ∀ {@0 bs₁ bs₂} → (ku : ExtensionFieldKU bs₁) (o : OIDValue bs₂)
                                     → Dec (KeyPurpose-ConsistentWith-KeyUsage ku o)
isKeyPurposeConsistentWithKeyUsage ku o =
  case (─ _ , o) ∈? OIDs.EKU.SupportedKeyUsageIDs of λ where
    (no o∉supported) → yes (unknown o o∉supported)
    (yes (here refl)) → yes anyKeyUsage
    (yes o∈@(there (here refl))) →
      case T? (  assertsKUBitField ku Extension.KUFields.digitalSignature
               ∨ assertsKUBitField ku Extension.KUFields.keyEncipherment
               ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
      of λ where
        (no ¬p) → no λ where
          (serverAuth pf) → contradiction pf ¬p
          (unknown o o∉) → contradiction o∈ o∉
        (yes p) → yes (serverAuth p)
    (yes o∈@(there (there (here refl)))) →
      case T? (  assertsKUBitField ku Extension.KUFields.digitalSignature
               ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
      of λ where
        (no ¬p) → no λ where
          (clientAuth pf) → contradiction pf ¬p
          (unknown o o∉) → contradiction o∈ o∉
        (yes p) → yes (clientAuth p)
    (yes o∈@(there (there (there (here refl))))) →
      case T? (assertsKUBitField ku Extension.KUFields.digitalSignature) of λ where
        (no ¬pf) → no λ where
          (codeSign pf) → contradiction pf ¬pf
          (unknown o o∉) → contradiction o∈ o∉
        (yes pf) → yes (codeSign pf)
    (yes o∈@(there (there (there (there (here refl)))))) →
      case T? (  assertsKUBitField ku Extension.KUFields.digitalSignature
               ∨ assertsKUBitField ku Extension.KUFields.nonRepudation
               ∨ assertsKUBitField ku Extension.KUFields.keyEncipherment
               ∨ assertsKUBitField ku Extension.KUFields.keyAgreement)
      of λ where
        (no ¬pf) → no λ where
          (emailProtection pf) → contradiction pf ¬pf
          (unknown o o∉) → contradiction o∈ (contradiction o∈ o∉)
        (yes pf) → yes (emailProtection pf)
    (yes o∈@(there (there (there (there (there (here refl))))))) →
      case T? (  assertsKUBitField ku Extension.KUFields.digitalSignature
               ∨ assertsKUBitField ku Extension.KUFields.nonRepudation)
      of λ where
        (no ¬pf) → no λ where
          (timeStamping pf) → contradiction pf ¬pf
          (unknown o o∉) → contradiction o∈ o∉
        (yes pf) → yes (timeStamping pf)
    (yes o∈@(there (there (there (there (there (there (here refl)))))))) →
      case T? (  assertsKUBitField ku Extension.KUFields.digitalSignature
               ∨ assertsKUBitField ku Extension.KUFields.nonRepudation)
      of λ where
        (no ¬pf) → no λ where
          (ocspSigning pf) → contradiction pf ¬pf
          (unknown o o∉) → contradiction o∈ o∉
        (yes pf) → yes (ocspSigning pf)

r18 : ∀ {@0 bs} (c : Cert bs) → Dec (R18 c)
r18 c =
  case (_,′_ (Cert.getKU c) (Cert.getEKU c)) ret (λ where (ku , eku) → Dec (R18' (proj₂ ku) (proj₂ eku))) of λ where
    ((─ _ , none) , _) → yes tt
    ((─ _ , some _) , (─ _ , none)) → yes tt
    ((─ _ , some ku) , (─ _ , some eku)) →
      All.all?
        (λ oid → isKeyPurposeConsistentWithKeyUsage ku (TLV.val (proj₂ oid)))
        (toList (Extension.FieldEKU.getKeyPurposeIDs eku))

