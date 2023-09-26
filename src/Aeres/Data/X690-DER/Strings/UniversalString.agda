{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Strings.UniversalString.Parser
import Aeres.Data.X690-DER.Strings.UniversalString.TCB
import Aeres.Data.X690-DER.Strings.UniversalString.Properties

module Aeres.Data.X690-DER.Strings.UniversalString where

open Aeres.Data.X690-DER.Strings.UniversalString.Parser public
open Aeres.Data.X690-DER.Strings.UniversalString.TCB    public

module UniversalString where
  open Aeres.Data.X690-DER.Strings.UniversalString.Properties public
