import Aeres.Data.X690-DER.Time.TimeType.Parser
import Aeres.Data.X690-DER.Time.TimeType.Properties
import Aeres.Data.X690-DER.Time.TimeType.Relation
import Aeres.Data.X690-DER.Time.TimeType.TCB

module Aeres.Data.X690-DER.Time.TimeType where

open Aeres.Data.X690-DER.Time.TimeType.TCB public
  hiding (module TimeType ; encodeℕ)

module TimeType where
  open Aeres.Data.X690-DER.Time.TimeType.Parser       public
  open Aeres.Data.X690-DER.Time.TimeType.Properties   public
  open Aeres.Data.X690-DER.Time.TimeType.Relation     public
    renaming
      ( _Time≤_ to _≤_
      ; _Time≥_ to _≥_
      ; _Time<_ to _<_
      ; _Time>_ to _>_
      ; _Time≡_ to _≡_)
  open Aeres.Data.X690-DER.Time.TimeType.TCB public
    using (encodeℕ)
  open Aeres.Data.X690-DER.Time.TimeType.TCB.TimeType public
