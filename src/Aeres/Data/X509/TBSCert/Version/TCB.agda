{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Int.TCB as Int
  hiding (getVal)
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Data.X690-DER.Tag as Tag
open import Aeres.Prelude

module Aeres.Data.X509.TBSCert.Version.TCB where

-- https://datatracker.ietf.org/doc/html/rfc5280#section-4.1
-- Version  ::=  INTEGER  {  v1(0), v2(1), v3(2)  }

Version : (@0 _ : List UInt8) → Set
Version xs = TLV Tag.AA0 Int xs

getVal : ∀ {@0 bs} → Version bs → ℤ
getVal v = Int.getVal (TLV.val v)
