{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.TLV
open import Aeres.Data.X690-DER.Tag
open import Aeres.Prelude

module Aeres.Data.X690-DER.TCB.Null where

Null = TLV Tag.Null (_≡ [])
