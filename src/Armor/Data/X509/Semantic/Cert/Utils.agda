open import Armor.Binary
open import Armor.Data.X509
import      Armor.Data.X509.Extension.TCB.OIDs as OIDs
import      Armor.Grammar.Definitions
open import Armor.Grammar.IList as IList
import      Armor.Grammar.Option
import      Armor.Grammar.Parallel
open import Armor.Prelude

module Armor.Data.X509.Semantic.Cert.Utils where

open Armor.Grammar.Definitions UInt8
open Armor.Grammar.Option      UInt8
open Armor.Grammar.Parallel    UInt8


------- helper functions -----

-- is it a CA certificate? the Basic Constraints extension is present and the value of CA is TRUE ?
IsConfirmedCA : ∀ {@0 bs} → Cert bs → Set
IsConfirmedCA c =
  maybe′
    T -- if Basic Constraints extension is present, reduces to whether the CA boolean is true
    ⊥ -- if Basic Constraints extension is absent, it cannot be confirmed as a CA
    (Cert.isCA c)

isConfirmedCA? : ∀ {@0 bs} (c : Cert bs) → Dec (IsConfirmedCA c)
isConfirmedCA? c = maybe{B = Dec ∘ maybe′ T ⊥} (λ b → T-dec) (no λ ()) (Cert.isCA c)

-- returns BCPathLen if exists
getBCPathLen :  Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.BCLit) Extension.BCFields)) → Exists─ (List UInt8) (Option NonNegativeInt)
getBCPathLen (─ .[] , none) = _ , none
getBCPathLen (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (Extension.mkBCFieldsSeqFields bcca bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = _ , bcpathlen


assertsKUBitField : ∀ {@0 bs} → ExtensionFieldKU bs → Extension.KUFields.BitField → Bool
assertsKUBitField ku bf = Extension.KUFields.getBitField (ExtensionFields.extension ku) bf

certAssertsKUBitField : ∀ {@0 bs} → Cert bs → Extension.KUFields.BitField → Bool
certAssertsKUBitField c bf = elimOption false (flip assertsKUBitField bf) (proj₂ (Cert.getKU c))
-- AssertsKUBitField' : ∀ {@0 bs} → Option ExtensionFieldKU bs → Extension.KUFields.BitField → Set
-- AssertsKUBitField' none _ = ⊥
-- AssertsKUBitField' (some ku) bf = T (Extension.KUFields.getBitField (ExtensionFields.extension ku) bf)

-- AssertsKUBitField : ∀ {@0 bs} → Cert bs → Extension.KUFields.BitField → Set
-- AssertsKUBitField c = AssertsKUBitField' (proj₂ (Cert.getKU c))

-- assertsKUBitField? : ∀ {@0 bs} → (o : Option ExtensionFieldKU bs) → (bf : Extension.KUFields.BitField) → Dec (AssertsKUBitField' o bf)
-- assertsKUBitField? none bf = no λ ()
-- assertsKUBitField? (some x) bf = T-dec

-- is DigSign present in KU extension ? bit 0 == true ?
-- isDigSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isDigSignPresent (─ .[] , none) = false
-- isDigSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDigSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- -- is NonRep present in KU extension ? bit 1 == true ?
-- isNonRepPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isNonRepPresent (─ .[] , none) = false
-- isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₁


-- -- is KeyEnc present in KU extension ? bit 2 == true ?
-- isKeyEncPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isKeyEncPresent (─ .[] , none) = false
-- isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₂


-- -- is KeyDec present in KU extension ? bit 3 == true ?
-- isKeyDecPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isKeyDecPresent (─ .[] , none) = false
-- isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₃


-- -- is KeyAgree present in KU extension ? bit 4 == true ?
-- isKeyAgreePresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isKeyAgreePresent (─ .[] , none) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₄


-- is KeyCertSign present in KU extension ? bit 5 == true ?
-- isKeyCertSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isKeyCertSignPresent (─ .[] , none) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₅


-- is CRLSign present in KU extension ? bit 6 == true ?
-- isCRLSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isCRLSignPresent (─ .[] , none) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₆


-- -- is Encryption present in KU extension ? bit 7 == true ?
-- isEncryptionPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isEncryptionPresent (─ .[] , none) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₇


-- -- is Decryption present in KU extension ? bit 8 == true ?
-- isDecryptionPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
-- isDecryptionPresent (─ .[] , none) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
-- isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈ ∷ x₉) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₈


-- get KU Bits in bool list
-- getKUBits : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → List Bool
-- getKUBits (─ .[] , none) = []
-- getKUBits (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- get SAN length
getSANLength : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → ℕ
getSANLength (─ .[] , none) = 0
getSANLength (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = lengthSequence fstₚ₁


-- is SAN present in Cert ?
isSANPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → Bool
isSANPresent (─ .[] , none) = false
isSANPresent (fst , some x) = true

-- is KU present in Cert ?
isKUPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKUPresent (─ .[] , none) = false
isKUPresent (fst , some x) = true


-- returns all certificate policy OIDs
getPolicyOIDList : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.CPOLLit) Extension.CertPolFields)) →  List (Exists─ (List UInt8) OID)
getPolicyOIDList (─ .[] , none) = []
getPolicyOIDList (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper (fstₚ val)
  where
  helper : ∀ {@0 bs} → SequenceOf Extension.CertPolicy.PolicyInformation bs → List (Exists─ (List UInt8) OID)
  helper nil = []
  helper (consIList (mkTLV len (Extension.CertPolicy.mkPolicyInformationFields cpid cpqls bs≡₂) len≡ bs≡₁) t bs≡) = (_ , cpid) ∷ (helper t)


-- returns all EKU OIds
getEKUOIDList : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.EKULit) Extension.EKUFields)) →  List (Exists─ (List UInt8) OID)
getEKUOIDList (─ .[] , none) = []
getEKUOIDList (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ val len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper (fstₚ val)
  where
  helper : ∀ {@0 bs} → SequenceOf OID bs → List (Exists─ (List UInt8) OID)
  helper nil = []
  helper (cons (mkIListCons head₁ tail₁ bs≡)) = (_ , head₁) ∷ helper tail₁


getExtensionsOIDList : List (Exists─ (List UInt8) Extension) →  List (Exists─ (List UInt8) OID)
getExtensionsOIDList = map helper
  where
  helper : Exists─ (List UInt8) Extension → (Exists─ (List UInt8) OID)
  helper (fst , mkTLV len (akiextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (skiextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (kuextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (ekuextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (bcextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (ianextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (sanextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (cpextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (crlextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (ncextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (pcextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (pmextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (inapextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (aiaextn x) len≡ bs≡) = _ , (ExtensionFields.extnId x)
  helper (fst , mkTLV len (other x ¬crit) len≡ bs≡) = _ , (ExtensionFields.extnId x)

-- checkPurposeConsistency : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → List (Exists─ (List UInt8) OID) → Bool
-- checkPurposeConsistency x [] = true
-- checkPurposeConsistency x ((fst , snd) ∷ y)
--   with ↑ OID.serialize snd ≟ OIDs.ServerAuthOID
-- ... | yes p = ((isDigSignPresent x) ∨ (isKeyEncPresent x) ∨ (isKeyAgreePresent x)) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.ClientAuthOID
-- ... | yes p = ((isDigSignPresent x) ∨ (isKeyAgreePresent x)) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.CodeSignOID
-- ... | yes p = (isDigSignPresent x) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.EmailProtOID
-- ... | yes p = ((isDigSignPresent x) ∨ (isKeyEncPresent x) ∨ (isKeyAgreePresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.TimeStampOID
-- ... | yes p = ((isDigSignPresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.OCSPSignOID
-- ... | yes p = ((isDigSignPresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
-- ... | no ¬p
--   with ↑ OID.serialize snd ≟ OIDs.AnyExtendedKeyUsage
-- ... | yes p = checkPurposeConsistency x y
-- ... | no ¬p = true
