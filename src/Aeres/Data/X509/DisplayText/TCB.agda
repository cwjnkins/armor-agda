{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
open import Aeres.Data.Unicode.UTF16.TCB
  renaming (size to sizeBMP)
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Data.X690-DER.Strings.BMPString.TCB
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.Strings.UTF8String.TCB
open import Aeres.Data.X690-DER.Strings.VisibleString.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Prelude

module Aeres.Data.X509.DisplayText.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

data DisplayText : @0 List UInt8 → Set where
  ia5String     : ∀ {@0 bs} → Σₚ IA5String     (TLVSizeBounded IA5StringValue.size     1 200) bs → DisplayText bs
  visibleString : ∀ {@0 bs} → Σₚ VisibleString (TLVSizeBounded VisibleStringValue.size 1 200) bs → DisplayText bs
  bmpString     : ∀ {@0 bs} → Σₚ BMPString     (TLVSizeBounded sizeBMP                 1 200) bs → DisplayText bs
  utf8String    : ∀ {@0 bs} → Σₚ UTF8String    (TLVSizeBounded UTF8.size               1 200) bs → DisplayText bs

postulate
  RawDisplayText : Raw DisplayText

