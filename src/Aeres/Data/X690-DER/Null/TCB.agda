{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.TLV
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.Null.TCB where

Null = TLV Tag.Null (_≡ [])

nullTLV : Null (Tag.Null ∷ [ # 0 ])
nullTLV = mkTLV (Length.shortₛ (# 0)) refl refl refl
