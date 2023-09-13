{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert.Utils where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8


------- helper functions -----

-- is it a CA certificate? the Basic Constraints extension is present and the value of CA is TRUE ?
isCA : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.BCLit) Extension.BCFields)) → Bool
isCA (─ .[] , none) = false
isCA (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (Extension.mkBCFieldsSeqFields none bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCA (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (Extension.mkBCFieldsSeqFields (some (mkTLV len₂ (mkBoolValue v b vᵣ bs≡₅) len≡₂ bs≡₄)) bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = v


-- returns BCPathLen if exists
getBCPathLen :  Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.BCLit) Extension.BCFields)) → Exists─ (List UInt8) (Option Int)
getBCPathLen (─ .[] , none) = _ , none
getBCPathLen (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (Extension.mkBCFieldsSeqFields bcca bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = _ , bcpathlen


-- is DigSign present in KU extension ? bit 0 == true ?
isDigSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isDigSignPresent (─ .[] , none) = false
isDigSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDigSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- is NonRep present in KU extension ? bit 1 == true ?
isNonRepPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isNonRepPresent (─ .[] , none) = false
isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isNonRepPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₁


-- is KeyEnc present in KU extension ? bit 2 == true ?
isKeyEncPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKeyEncPresent (─ .[] , none) = false
isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyEncPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₂


-- is KeyDec present in KU extension ? bit 3 == true ?
isKeyDecPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKeyDecPresent (─ .[] , none) = false
isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyDecPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₃


-- is KeyAgree present in KU extension ? bit 4 == true ?
isKeyAgreePresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKeyAgreePresent (─ .[] , none) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyAgreePresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₄


-- is KeyCertSign present in KU extension ? bit 5 == true ?
isKeyCertSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKeyCertSignPresent (─ .[] , none) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isKeyCertSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₅


-- is CRLSign present in KU extension ? bit 6 == true ?
isCRLSignPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isCRLSignPresent (─ .[] , none) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isCRLSignPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₆


-- is Encryption present in KU extension ? bit 7 == true ?
isEncryptionPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isEncryptionPresent (─ .[] , none) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isEncryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₇


-- is Decryption present in KU extension ? bit 8 == true ?
isDecryptionPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isDecryptionPresent (─ .[] , none) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = false
isDecryptionPresent (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇ ∷ x₈ ∷ x₉) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x₈


-- get KU Bits in bool list
getKUBits : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → List Bool
getKUBits (─ .[] , none) = []
getKUBits (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton x x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = x


-- is SAN extension critical ? 
isSANCritical : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → Bool
isSANCritical (─ .[] , none) = false
isSANCritical (fst , some (mkExtensionFields extnId extnId≡ none extension bs≡)) = false
isSANCritical (fst , some (mkExtensionFields extnId extnId≡ (some (mkTLV len (mkBoolValue v b vᵣ bs≡₂) len≡ bs≡₁)) extension bs≡)) = v


-- get SAN length
getSANLength : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → ℕ
getSANLength (─ .[] , none) = 0
getSANLength (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = lengthSequence fstₚ₁


-- is SAN present in Cert ?
isSANPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.SANLit) Extension.SANFields)) → Bool
isSANPresent (─ .[] , none) = false
isSANPresent (fst , some x) = true

-- is KU present in Cert ?
isKUPresent : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → Bool
isKUPresent (─ .[] , none) = false
isKUPresent (fst , some x) = true


-- helper for SCP17 :  While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
checkCRLDistStruct : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.CRLDISTLit) Extension.CRLDistFields)) → Bool
checkCRLDistStruct (─ .[] , none) = true
checkCRLDistStruct (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mk×ₚ fstₚ₁ sndₚ₁ bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = helper fstₚ₁
  where
  helper : ∀ {@0 bs} → SequenceOf Extension.CRLDistPoint.DistPoint bs → Bool
  helper nil = true
  helper (cons (mkIListCons (mkTLV len (Extension.CRLDistPoint.mkDistPointFields crldp none crlissr bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none (some x) none bs≡₂) len≡ bs≡₁) t bs≡)) = false
  helper (cons (mkIListCons (mkTLV len (Extension.CRLDistPoint.mkDistPointFields none (some x) (some x₁) bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x₁) (some x) none bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t
  helper (cons (mkIListCons (mkTLV len (Extension.CRLDistPoint.mkDistPointFields (some x₁) (some x) (some x₂) bs≡₂) len≡ bs≡₁) t bs≡)) = true ∧ helper t


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


-- returns true only if the extension is unknown and has critical bit = true
isUnkwnCriticalExtension : Exists─ (List UInt8) Extension → Bool
isUnkwnCriticalExtension (fst , mkTLV len (other (mkExtensionFields extnId extnId≡ none extension bs≡₁)) len≡ bs≡) = false
isUnkwnCriticalExtension (fst , mkTLV len (other (mkExtensionFields extnId extnId≡ (some (mkTLV len₁ (mkBoolValue v b vᵣ bs≡₃) len≡₁ bs≡₂)) extension bs≡₁)) len≡ bs≡) = v
isUnkwnCriticalExtension (fst , mkTLV len _ len≡ bs≡) = false


-- is any unknown extention critical from the list ?
isAnyOtherExtnCritical : List (Exists─ (List UInt8) Extension) → Bool
isAnyOtherExtnCritical x = helper x
  where
  -- returns true only if at least one extension in the list is unknown and that extension has critical bit = true
  helper : List (Exists─ (List UInt8) Extension) → Bool
  helper [] = false
  helper (x ∷ x₁) = case (isUnkwnCriticalExtension x) of λ where
    false → helper x₁
    true → true


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
  helper (fst , mkTLV len (other x) len≡ bs≡) = _ , (ExtensionFields.extnId x)


checkPurposeConsistency : Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.KULit) Extension.KUFields)) → List (Exists─ (List UInt8) OID) → Bool
checkPurposeConsistency x [] = true
checkPurposeConsistency x ((fst , snd) ∷ y)
  with ↑ OID.serialize snd ≟ OIDs.ServerAuthOID
... | yes p = ((isDigSignPresent x) ∨ (isKeyEncPresent x) ∨ (isKeyAgreePresent x)) ∧ (checkPurposeConsistency x y)
... | no ¬p
  with ↑ OID.serialize snd ≟ OIDs.ClientAuthOID
... | yes p = ((isDigSignPresent x) ∨ (isKeyAgreePresent x)) ∧ (checkPurposeConsistency x y)
... | no ¬p
  with ↑ OID.serialize snd ≟ OIDs.CodeSignOID
... | yes p = (isDigSignPresent x) ∧ (checkPurposeConsistency x y)
... | no ¬p
  with ↑ OID.serialize snd ≟ OIDs.EmailProtOID
... | yes p = ((isDigSignPresent x) ∨ (isKeyEncPresent x) ∨ (isKeyAgreePresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
... | no ¬p
  with ↑ OID.serialize snd ≟ OIDs.TimeStampOID
... | yes p = ((isDigSignPresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
... | no ¬p
  with ↑ OID.serialize snd ≟ OIDs.OCSPSignOID
... | yes p = ((isDigSignPresent x) ∨ (isNonRepPresent x)) ∧ (checkPurposeConsistency x y)
... | no ¬p = true ∧ (checkPurposeConsistency x y)