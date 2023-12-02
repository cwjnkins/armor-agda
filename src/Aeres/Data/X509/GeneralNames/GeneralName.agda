import Aeres.Data.X509.GeneralNames.GeneralName.Eq
import Aeres.Data.X509.GeneralNames.GeneralName.Parser
import Aeres.Data.X509.GeneralNames.GeneralName.Properties
import Aeres.Data.X509.GeneralNames.GeneralName.TCB

module Aeres.Data.X509.GeneralNames.GeneralName where

open Aeres.Data.X509.GeneralNames.GeneralName.Parser public
open Aeres.Data.X509.GeneralNames.GeneralName.TCB    public
  hiding (module GeneralName)

module GeneralName where
  open Aeres.Data.X509.GeneralNames.GeneralName.Properties public
  open Aeres.Data.X509.GeneralNames.GeneralName.Eq public

