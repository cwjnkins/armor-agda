open import Armor.Binary
open import Armor.Data.X690-DER.Int.TCB as Int
import      Armor.Grammar.Definitions.NonMalleable
import      Armor.Grammar.Parallel.TCB
open import Armor.Prelude

module Armor.Data.X509.CRL.Version.TCB where

open Armor.Grammar.Definitions.NonMalleable UInt8
open Armor.Grammar.Parallel.TCB             UInt8

data DecodedVersion : Set where
  v1 v2 : DecodedVersion

supportedVersions : List ℤ
supportedVersions = ℤ.+ 0 ∷ [ ℤ.+ 1 ]

Version : @0 List UInt8 → Set
Version = Σₚ Int λ _ i → Erased (Int.getVal i ∈ supportedVersions)

RawVersion : Raw Version
toRawVersion : ∀ {@0 bs} → (@0 i : Int bs) (i∈ : Int.getVal i ∈ supportedVersions) → DecodedVersion
Raw.D RawVersion = DecodedVersion
Raw.to RawVersion (mk×ₚ i (─ i∈)) = toRawVersion i (uneraseDec i∈ (_ ∈? _))

toRawVersion i (here px) = v1
toRawVersion i (there (here px)) = v2
