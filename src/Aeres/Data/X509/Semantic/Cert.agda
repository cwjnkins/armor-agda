{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8


------- helper functions -----

-- returns true iff time1 <= time2
checkTwoTimes : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
checkTwoTimes yr₁ mn₁ da₁ hr₁ mi₁ se₁ yr₂ mn₂ da₂ hr₂ mi₂ se₂
  with yr₁ <? yr₂
...  | yes p₁ = true
...  | no ¬p₁
  with yr₂ <? yr₁
...  | yes p₂ = false
...  | no ¬p₂
  with mn₁ <? mn₂
...  | yes p₃ = true
...  | no ¬p₃
  with mn₂ <? mn₁
...  | yes p₄ = false
...  | no ¬p₄ 
  with da₁ <? da₂
...  | yes p₅ = true
...  | no ¬p₅ 
  with da₂ <? da₁
...  | yes p₆ = false
...  | no ¬p₆
  with hr₁ <? hr₂
...  | yes p₇ = true
...  | no ¬p₇
  with hr₂ <? hr₁
...  | yes p₈ = false
...  | no ¬p₈
  with mi₁ <? mi₂
...  | yes p₉ = true
...  | no ¬p₉
  with mi₂ <? mi₁
...  | yes p₁₀ = false
...  | no ¬p₁₀
  with se₁ <? se₂
...  | yes p₁₁ = true
...  | no ¬p₁₁
  with se₂ <? se₁
...  | yes p₁₂ = false
...  | no ¬p₁₂ = true


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


-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.
SCP1 : ∀ {@0 bs} → Cert bs → Set
SCP1 c = Cert.getTBSCertSignAlg c ≡ Cert.getCertSignAlg c

scp1 :  ∀ {@0 bs} (c : Cert bs) → Dec (SCP1 c)
scp1 c =
  case (proj₂ (Cert.getTBSCertSignAlg c) ≋? proj₂ (Cert.getCertSignAlg c)) ret (const _) of λ where
      (yes ≋-refl) → yes refl
      (no ¬eq) → no λ where refl → contradiction ≋-refl ¬eq


-- Extension field MUST only appear if the Version is 3(2).
SCP2 : ∀ {@0 bs} → Cert bs → Set
SCP2 c = T (isSome (proj₂ (Cert.getExtensions c))) → Cert.getVersion c ≡ ℤ.+ 2

scp2 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP2 c)
scp2 c =
  case proj₂ (Cert.getExtensions c) ret (λ x → Dec (T (isSome x) → Cert.getVersion c ≡ ℤ.+ 2)) of λ where
    none → yes (λ ())
    (some x) →
      case Cert.getVersion c ≟ ℤ.+ 2 of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes (λ _ → p)


-- At a minimum, conforming implementations MUST recognize Version 3 certificates.
-- Generation of Version 2 certificates is not expected by implementations based on this profile.
-- note : but, version 1 and 2 certs can be present for CA certificates. So, we are checking whether
-- the version is 1, 2, or 3 (0 - 2).
SCP3 : ∀ {@0 bs} → Cert bs → Set
SCP3 c = ((Cert.getVersion c ≡ ℤ.+ 0) ⊎ (Cert.getVersion c ≡  ℤ.+ 1)) ⊎ (Cert.getVersion c ≡  ℤ.+ 2)

scp3 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP3 c)
scp3 c = ((Cert.getVersion c ≟ ℤ.+ 0) ⊎-dec (Cert.getVersion c ≟  ℤ.+ 1)) ⊎-dec (Cert.getVersion c ≟  ℤ.+ 2)


-- The Serial number MUST be a positive integer assigned by the CA to each certificate.
SCP4 : ∀ {@0 bs} → Cert bs → Set
SCP4 c = ℤ.+ 0 ℤ.< Cert.getSerial c

scp4 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP4 c)
scp4 c = (ℤ.+ 0 ℤ.<? Cert.getSerial c)


-- The Issuer field MUST contain a non-empty distinguished name (DN).
-- TODO : fix the parser to enforce set length to minimum 1
SCP5 : ∀ {@0 bs} → Cert bs → Set
SCP5 c = 0 < Cert.getIssuerLen c 

scp5 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP5 c)
scp5 c = 0 <? Cert.getIssuerLen c 


-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
SCP6 : ∀ {@0 bs} → Cert bs → Set
SCP6 c = T (isCA (Cert.getBC c)) → (0 < Cert.getSubjectLen c)

scp6 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP6 c)
scp6 c
  with isCA (Cert.getBC c)
... | false = yes (λ ())
... | true
  with 0 <? Cert.getSubjectLen c
... | no ¬p = no λ x → contradiction (x tt) ¬p
... | yes p = yes (λ _ → p)


-- Unique Identifiers fields MUST only appear if the Version is 2 or 3.
SCP7₁ : ∀ {@0 bs} → Cert bs → Set
SCP7₁ c = T (isSome (proj₂ (Cert.getSubUID c))) → (Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)

SCP7₂ : ∀ {@0 bs} → Cert bs → Set
SCP7₂ c = T (isSome (proj₂ (Cert.getIssUID c))) → (Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)

scp7₁ : ∀ {@0 bs} (c : Cert bs) → Dec (SCP7₁ c)
scp7₁ c =
  case proj₂ (Cert.getSubUID c) ret (λ x → Dec (T (isSome x) → Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)) of λ where
    none → yes λ ()
    (some x) →
      case (Cert.getVersion c ≟ ℤ.+ 1 ⊎-dec Cert.getVersion c ≟ ℤ.+ 2) of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes (λ _ → p)

scp7₂ : ∀ {@0 bs} (c : Cert bs) → Dec (SCP7₂ c)
scp7₂ c =
  case proj₂ (Cert.getIssUID c) ret (λ x → Dec (T (isSome x) → Cert.getVersion c ≡ ℤ.+ 1 ⊎ Cert.getVersion c ≡  ℤ.+ 2)) of (λ where
    none → yes (λ ())
    (some _) →
      case (Cert.getVersion c ≟ ℤ.+ 1 ⊎-dec Cert.getVersion c ≟ ℤ.+ 2) of λ where
        (no ¬p) → no (λ abs → contradiction (abs tt) ¬p)
        (yes p) → yes λ _ → p)


-- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.
SCP8' : Exists─ (List UInt8) (Option Int) → Set
SCP8' (─ .[] , none) = ⊤
SCP8' (fst , some x) = ℤ.+ 0 ℤ.≤ Int.getVal x

SCP8 : ∀ {@0 bs} → Cert bs → Set
SCP8 c = SCP8' (getBCPathLen (Cert.getBC c))

scp8 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP8 c)
scp8 c =
  case (getBCPathLen (Cert.getBC c)) ret (λ x → Dec (SCP8' x)) of λ where
    (─ .[] , none) → yes tt
    (fst , some x) → ℤ.+ 0 ℤ.≤? Int.getVal x


-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
SCP9 : ∀ {@0 bs} → Cert bs → Set
SCP9 c = T (isCRLSignPresent (Cert.getKU c)) → (0 < Cert.getSubjectLen c)

scp9 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP9 c)
scp9 c
  with (isCRLSignPresent (Cert.getKU c))
... | false = yes (λ ())
... | true
  with (0 <? Cert.getSubjectLen c)
... | no ¬p = no λ x → contradiction (x tt) ¬p
... | yes p = yes (λ x → p)


-- When the Key Usage extension appears in a certificate, at least one of the bits MUST be set to 1.
SCP10 : ∀ {@0 bs} → Cert bs → Set
SCP10 c = T (isKUPresent (Cert.getKU c)) → (true ∈ getKUBits (Cert.getKU c))

scp10 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP10 c)
scp10 c
  with isKUPresent (Cert.getKU c)
... | false = yes (λ ())
... | true
  with true ∈? getKUBits (Cert.getKU c)
... | no ¬p =  no (λ x → contradiction (x tt) ¬p)
... | yes p = yes (λ x → p)


-- If subject naming information is present only in the Subject Alternative Name extension ,
-- then the Subject name MUST be an empty sequence and the Subject Alternative Name extension MUST be critical.
-- If the subject field contains an empty sequence, then the issuing CA MUST include a
-- subjectAltName extension that is marked as critical.
SCP11 : ∀ {@0 bs} → Cert bs → Set
SCP11 c = (0 ≡ Cert.getSubjectLen c) → T (isSANCritical (Cert.getSAN c))

scp11 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP11 c)
scp11 c with (0 ≟ Cert.getSubjectLen c)
scp11 c    | no n with isSANCritical (Cert.getSAN c)
scp11 c    | no n    | false = yes n
scp11 c    | no n    | true  = yes (λ x → tt)
scp11 c    | yes y with isSANCritical (Cert.getSAN c)
scp11 c    | yes y   | false = no (λ x → contradiction y x)
scp11 c    | yes y   | true  = yes (λ x → tt)


-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.
SCP12 : ∀ {@0 bs} → Cert bs → Set
SCP12 c = T (isSANPresent (Cert.getSAN c)) → (0 < getSANLength (Cert.getSAN c))

scp12 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP12 c)
scp12 c
  with isSANPresent (Cert.getSAN c)
... | false = yes (λ ())
... | true
  with 0 <? getSANLength (Cert.getSAN c)
... | yes y = yes (λ x → y)
... | no n = no (λ x → contradiction (x tt) n)


-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.
SCP13 : ∀ {@0 bs} → Cert bs → Set
SCP13 c = T (isKeyCertSignPresent (Cert.getKU c)) → T (isCA (Cert.getBC c))

scp13 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP13 c)
scp13 c with isKeyCertSignPresent (Cert.getKU c)
scp13 c    | false with isCA (Cert.getBC c)
scp13 c    | false    | _ =  yes (λ ())
scp13 c    | true with isCA (Cert.getBC c)
scp13 c    | true     | false = no (contradiction tt)
scp13 c    | true     | true  = yes λ x → x


-- A certificate MUST NOT include more than one instance of a particular Extension.
SCP14 : ∀ {@0 bs} → Cert bs → Set
SCP14 c = List.Unique _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))

scp14 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP14 c)
scp14 c = List.unique? _≟_ (getExtensionsOIDList (Cert.getExtensionsList c))


-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
SCP15 : ∀ {@0 bs} → Cert bs → Set
SCP15 c = T (isAnyOtherExtnCritical (Cert.getExtensionsList c)) → T false

scp15 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP15 c)
scp15 c
  with isAnyOtherExtnCritical (Cert.getExtensionsList c)
... | false = yes (λ ())
... | true = no (contradiction tt)


-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.
SCP16 : ∀ {@0 bs} → Cert bs → Set
SCP16 c = List.Unique _≟_ (getPolicyOIDList (Cert.getCPOL c))

scp16 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP16 c)
scp16 c = List.unique? _≟_ (getPolicyOIDList (Cert.getCPOL c))


-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
SCP17 : ∀ {@0 bs} → Cert bs → Set
SCP17 c = T (checkCRLDistStruct (Cert.getCRLDIST c))

scp17 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP17 c)
scp17 c
  with checkCRLDistStruct (Cert.getCRLDIST c)
... | false = no (λ x → x)
... | true = yes tt


-- The certificate Validity period includes the current time
SCP18 : ∀ {@0 bs₁ bs₂} → Cert bs₁ → Time bs₂ → Set
SCP18 c t = T (Time.lessEq (proj₂ (Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (Cert.getValidityEndTime c)))

scp18 : ∀ {@0 bs₁ bs₂} → (c : Cert bs₁) → (t : Time bs₂) → Dec (SCP18 c t)
scp18 c t
  with Time.lessEq (proj₂ (Cert.getValidityStartTime c)) t ∧ Time.lessEq t (proj₂ (Cert.getValidityEndTime c))
... | false = no id
... | true  = yes tt



------ new semantic checks


--- helper for SCP19
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


--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
SCP19 : ∀ {@0 bs} → Cert bs → Set
SCP19 c = T (checkPurposeConsistency (Cert.getKU c) (getEKUOIDList (Cert.getEKU c)))

scp19 : ∀ {@0 bs} (c : Cert bs) → Dec (SCP19 c)
scp19 c
  with checkPurposeConsistency (Cert.getKU c) (getEKUOIDList (Cert.getEKU c))
... | true = yes tt
... | false = no (λ x → x)

