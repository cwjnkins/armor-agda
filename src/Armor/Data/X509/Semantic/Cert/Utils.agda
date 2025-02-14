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

-- if ku extension is present, verify crlsign bit is true 
IsConfirmedCRLIssuer : ∀ {@0 bs} → Cert bs → Set 
IsConfirmedCRLIssuer c
  with Cert.getKU c
... | ─ .[] , none = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = ⊥
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = T x₆

isConfirmedCRLIssuer? :  ∀ {@0 bs} → (c : Cert bs) → Dec (IsConfirmedCRLIssuer c) 
isConfirmedCRLIssuer? c
  with Cert.getKU c
... | ─ .[] , none = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton [] x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ []) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = no λ ()
... | fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (mkBitStringValue bₕ bₜ bₕ<8 (singleton (x ∷ x₁ ∷ x₂ ∷ x₃ ∷ x₄ ∷ x₅ ∷ x₆ ∷ x₇) x≡) unusedBits bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡) = T-dec

-- returns BCPathLen if exists
getBCPathLen :  Exists─ (List UInt8) (Option (ExtensionFields (_≡ OIDs.BCLit) Extension.BCFields)) → Exists─ (List UInt8) (Option NonNegativeInt)
getBCPathLen (─ .[] , none) = _ , none
getBCPathLen (fst , some (mkExtensionFields extnId extnId≡ crit (mkTLV len (mkTLV len₁ (Extension.mkBCFieldsSeqFields bcca bcpathlen bs≡₃) len≡₁ bs≡₂) len≡ bs≡₁) bs≡)) = _ , bcpathlen


assertsKUBitField : ∀ {@0 bs} → ExtensionFieldKU bs → Extension.KUFields.BitField → Bool
assertsKUBitField ku bf = Extension.KUFields.getBitField (ExtensionFields.extension ku) bf

certAssertsKUBitField : ∀ {@0 bs} → Cert bs → Extension.KUFields.BitField → Bool
certAssertsKUBitField c bf = elimOption false (flip assertsKUBitField bf) (proj₂ (Cert.getKU c))

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
