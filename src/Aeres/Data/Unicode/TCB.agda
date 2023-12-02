open import Aeres.Binary
open import Aeres.Data.Unicode.UTF8.TCB
open import Aeres.Data.Unicode.UTF16.TCB
open import Aeres.Data.Unicode.UTF32.TCB
open import Aeres.Prelude

module Aeres.Data.Unicode.TCB where

-- we only support the BMP subset of UTF16
data Unicode (@0 bs : List UInt8) : Set where
  utf8  : UTF8  bs → Unicode bs
  utf16 : BMP bs → Unicode bs
  utf32 : UTF32 bs → Unicode bs
