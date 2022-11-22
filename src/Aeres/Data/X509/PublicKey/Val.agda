{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.PublicKey.Val.EC
import Aeres.Data.X509.PublicKey.Val.Eq
import Aeres.Data.X509.PublicKey.Val.Parser
import Aeres.Data.X509.PublicKey.Val.Properties
import Aeres.Data.X509.PublicKey.Val.RSA
import Aeres.Data.X509.PublicKey.Val.TCB

module Aeres.Data.X509.PublicKey.Val where

module Val where
  module EC where
    open Aeres.Data.X509.PublicKey.Val.EC public
    open EC public

  module RSA where
    open Aeres.Data.X509.PublicKey.Val.RSA public
    open RSA public

  open Aeres.Data.X509.PublicKey.Val.Eq         public
  open Aeres.Data.X509.PublicKey.Val.Properties public

open Aeres.Data.X509.PublicKey.Val.Parser public
open Aeres.Data.X509.PublicKey.Val.TCB public
