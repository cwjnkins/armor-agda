{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Strings.PrintableString.Char.Parser
import Aeres.Data.X690-DER.Strings.PrintableString.Char.Properties
import Aeres.Data.X690-DER.Strings.PrintableString.Char.TCB

module Aeres.Data.X690-DER.Strings.PrintableString.Char where

open Aeres.Data.X690-DER.Strings.PrintableString.Char.TCB    public

module Char where
  open Aeres.Data.X690-DER.Strings.PrintableString.Char.Parser public
  open Aeres.Data.X690-DER.Strings.PrintableString.Char.Properties public
