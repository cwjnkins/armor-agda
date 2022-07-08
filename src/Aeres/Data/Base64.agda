{-# OPTIONS --subtyping #-}

import Aeres.Data.Base64.Parser
import Aeres.Data.Base64.Properties
import Aeres.Data.Base64.TCB

module Aeres.Data.Base64 where

open Aeres.Data.Base64.Parser       public
module Base64 where
  open Aeres.Data.Base64.Properties public
    renaming ( module Base64Char to Char
             ; module Base64Pad  to Pad
             ; module Base64Str  to Str)
open Aeres.Data.Base64.TCB          public
