{-# OPTIONS --subtyping #-}

import Aeres.Data.Unicode.UTF16.Parser
import Aeres.Data.Unicode.UTF16.Properties
import Aeres.Data.Unicode.UTF16.TCB

module Aeres.Data.Unicode.UTF16 where

open Aeres.Data.Unicode.UTF16.TCB    public
open Aeres.Data.Unicode.UTF16.Parser public

module UTF16 where
  open Aeres.Data.Unicode.UTF16.Properties public