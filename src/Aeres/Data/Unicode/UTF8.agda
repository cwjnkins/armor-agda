{-# OPTIONS --subtyping #-}

import Aeres.Data.Unicode.UTF8.Parser
import Aeres.Data.Unicode.UTF8.Properties
import Aeres.Data.Unicode.UTF8.Serializer
import Aeres.Data.Unicode.UTF8.TCB

module Aeres.Data.Unicode.UTF8 where

open Aeres.Data.Unicode.UTF8.Parser public
open Aeres.Data.Unicode.UTF8.TCB    public

module UTF8 where
  open Aeres.Data.Unicode.UTF8.Properties public
  open Aeres.Data.Unicode.UTF8.Serializer public
