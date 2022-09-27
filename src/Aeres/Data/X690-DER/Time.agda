{-# OPTIONS --subtyping #-}

import Aeres.Data.X690-DER.Time.Properties
import Aeres.Data.X690-DER.Time.TCB

module Aeres.Data.X690-DER.Time where

open import Aeres.Data.X690-DER.Time.TCB
  public
  hiding (getYear ; getMonth ; getDay ; getHour ; getMin ; getSec ; module Time)

module Time where
  open Aeres.Data.X690-DER.Time.TCB
    public
    using (getYear ; getMonth ; getDay ; getHour ; getMin ; getSec)
  open Aeres.Data.X690-DER.Time.Properties
    public
