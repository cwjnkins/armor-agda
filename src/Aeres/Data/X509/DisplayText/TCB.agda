{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.IA5String.TCB
open import Aeres.Data.X509.Strings.TCB
open import Aeres.Data.X690-DER.TLV.TCB
import      Aeres.Grammar.Definitions
open import Aeres.Prelude

module Aeres.Data.X509.DisplayText.TCB where

open Aeres.Grammar.Definitions UInt8

data DisplayText : @0 List UInt8 → Set where
  ia5String     : ∀ {@0 bs} → Σₚ IA5String     (TLVLenBounded 1 200) bs → DisplayText bs
  visibleString : ∀ {@0 bs} → Σₚ VisibleString (TLVLenBounded 1 200) bs → DisplayText bs
  bmpString     : ∀ {@0 bs} → Σₚ BMPString     (TLVLenBounded 1 200) bs → DisplayText bs
  utf8String    : ∀ {@0 bs} → Σₚ UTF8String    (TLVLenBounded 1 200) bs → DisplayText bs
