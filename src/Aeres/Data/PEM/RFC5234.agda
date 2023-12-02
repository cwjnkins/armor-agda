import Aeres.Data.PEM.RFC5234.Parser
import Aeres.Data.PEM.RFC5234.Properties
import Aeres.Data.PEM.RFC5234.TCB

module Aeres.Data.PEM.RFC5234 where

open Aeres.Data.PEM.RFC5234.Parser public
open Aeres.Data.PEM.RFC5234.TCB public

module RFC5234 where
  open Aeres.Data.PEM.RFC5234.Properties public
