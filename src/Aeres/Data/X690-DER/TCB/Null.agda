{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TCB.TLV
import      Aeres.Data.X690-DER.TCB.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.Null where

Null = TLV Tag.Null (_≡ [])
