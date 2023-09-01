{-# OPTIONS --subtyping #-}

import Aeres.Data.Unicode.UTF32.Parser
import Aeres.Data.Unicode.UTF32.Properties
import Aeres.Data.Unicode.UTF32.TCB

module Aeres.Data.Unicode.UTF32 where

open Aeres.Data.Unicode.UTF32.TCB    public

module UTF32 where
  open Aeres.Data.Unicode.UTF32.Properties public
  open Aeres.Data.Unicode.UTF32.Parser public
