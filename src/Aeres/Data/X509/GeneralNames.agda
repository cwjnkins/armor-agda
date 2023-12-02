import Aeres.Data.X509.GeneralNames.Eq
import Aeres.Data.X509.GeneralNames.Parser
import Aeres.Data.X509.GeneralNames.Properties
import Aeres.Data.X509.GeneralNames.TCB
import Aeres.Data.X509.GeneralNames.GeneralName

module Aeres.Data.X509.GeneralNames where

open Aeres.Data.X509.GeneralNames.Parser public
open Aeres.Data.X509.GeneralNames.TCB public

module GeneralNames where
  open Aeres.Data.X509.GeneralNames.Eq public
  open Aeres.Data.X509.GeneralNames.Properties public
  open Aeres.Data.X509.GeneralNames.GeneralName public

