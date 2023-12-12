import Aeres.Binary.Base64EncDec.Base64
import Aeres.Binary.Base64EncDec.EncDec

module Aeres.Binary.Base64EncDec where

open Aeres.Binary.Base64EncDec.Base64 public
  hiding (charset ; ∈charsetUnique)

module Base64 where
  open Aeres.Binary.Base64EncDec.Base64 public
    using (charset ; ∈charsetUnique)
  open Aeres.Binary.Base64EncDec.EncDec public
