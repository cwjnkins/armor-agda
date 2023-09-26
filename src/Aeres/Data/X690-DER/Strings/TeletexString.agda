{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Strings.TeletexString.Parser
import Aeres.Data.X690-DER.Strings.TeletexString.TCB
import Aeres.Data.X690-DER.Strings.TeletexString.Properties

module Aeres.Data.X690-DER.Strings.TeletexString where

open Aeres.Data.X690-DER.Strings.TeletexString.Parser public
open Aeres.Data.X690-DER.Strings.TeletexString.TCB    public

module TeletexString where
  open Aeres.Data.X690-DER.Strings.TeletexString.Properties public
