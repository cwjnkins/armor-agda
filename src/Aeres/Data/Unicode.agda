import Aeres.Data.Unicode.Properties
import Aeres.Data.Unicode.TCB
import Aeres.Data.Unicode.UTF8
import Aeres.Data.Unicode.UTF16
import Aeres.Data.Unicode.UTF32

module Aeres.Data.Unicode where

open Aeres.Data.Unicode.TCB public
  hiding (module Unicode)
open Aeres.Data.Unicode.UTF8 public
open Aeres.Data.Unicode.UTF16 public
open Aeres.Data.Unicode.UTF32 public

module Unicode where
  open Aeres.Data.Unicode.Properties public
