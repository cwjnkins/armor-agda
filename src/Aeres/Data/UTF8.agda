{-# OPTIONS --subtyping #-}

import Aeres.Data.UTF8.Parser
import Aeres.Data.UTF8.Properties
import Aeres.Data.UTF8.Serializer
import Aeres.Data.UTF8.TCB

module Aeres.Data.UTF8 where

open Aeres.Data.UTF8.Parser public
open Aeres.Data.UTF8.TCB    public

module UTF8 where
  open Aeres.Data.UTF8.Properties public
  open Aeres.Data.UTF8.Serializer public
