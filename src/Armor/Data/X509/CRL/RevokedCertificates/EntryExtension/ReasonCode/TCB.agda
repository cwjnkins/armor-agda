open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB as Int
  hiding (getVal)
open import Armor.Data.X690-DER.Length.TCB
open import Armor.Data.X690-DER.TLV.TCB
import      Armor.Data.X690-DER.Tag as Tag
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.RevokedCertificates.EntryExtension.ReasonCode.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Parallel.TCB             UInt8

-- id-ce-cRLReasons OBJECT IDENTIFIER ::= { id-ce 21 }
-- reasonCode ::= { CRLReason }
-- CRLReason ::= ENUMERATED {
--        unspecified             (0),
--        keyCompromise           (1),
--        cACompromise            (2),
--        affiliationChanged      (3),
--        superseded              (4),
--        cessationOfOperation    (5),
--        certificateHold         (6),
--             -- value 7 is not used
--        removeFromCRL           (8),
--        privilegeWithdrawn      (9),
--        aACompromise           (10) }

supportedCodes : List ℤ
supportedCodes = ℤ.+ 0 ∷ ℤ.+ 1 ∷ ℤ.+ 2 ∷ ℤ.+ 3 ∷ ℤ.+ 4 ∷ ℤ.+ 5 ∷ ℤ.+ 6 ∷ ℤ.+ 8 ∷ ℤ.+ 9 ∷ [ ℤ.+ 10 ]

ReasonCodeFieldsEnum : @0 List UInt8 → Set
ReasonCodeFieldsEnum = Σₚ [ Tag.Enum ]Int λ _ i → Erased ((Singleton.x ∘ IntegerValue.val ∘ TLV.val) i ∈ supportedCodes)

ReasonCodeFields : @0 List UInt8 → Set
ReasonCodeFields xs = TLV Tag.OctetString ReasonCodeFieldsEnum xs
