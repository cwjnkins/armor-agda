{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.Strings.IA5String.TCB
open import Aeres.Data.X690-DER.Strings.PrintableString.TCB
open import Aeres.Data.X690-DER
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Definitions.NonMalleable
open import Aeres.Data.Unicode.UTF8.TCB
open import Aeres.Data.Unicode.UTF16.TCB
open import Aeres.Data.Unicode.UTF32.TCB
open import Aeres.Prelude

module Aeres.Data.X509.DirectoryString.TCB where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Definitions.NonMalleable UInt8

data DirectoryString : @0 List UInt8 → Set where
  teletexString : ∀ {@0 bs} → Σₚ TeletexString TLVNonEmptyVal bs → DirectoryString bs
  printableString : ∀ {@0 bs} → Σₚ PrintableString TLVNonEmptyVal bs → DirectoryString bs
  universalString : ∀ {@0 bs} → Σₚ UniversalString TLVNonEmptyVal bs → DirectoryString bs
  utf8String : ∀ {@0 bs} → Σₚ UTF8String TLVNonEmptyVal bs → DirectoryString bs
  bmpString  : ∀ {@0 bs} → Σₚ BMPString  TLVNonEmptyVal bs → DirectoryString bs

postulate
  RawDirectoryString : Raw DirectoryString
  
