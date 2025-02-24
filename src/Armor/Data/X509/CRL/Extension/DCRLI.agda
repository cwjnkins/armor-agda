{-# OPTIONS --erasure #-}
import Armor.Data.X509.CRL.Extension.DCRLI.Parser
import Armor.Data.X509.CRL.Extension.DCRLI.TCB
import Armor.Data.X509.CRL.Extension.DCRLI.Properties

module Armor.Data.X509.CRL.Extension.DCRLI where

open Armor.Data.X509.CRL.Extension.DCRLI.Parser public
open Armor.Data.X509.CRL.Extension.DCRLI.TCB    public

module DCRLI where
  open Armor.Data.X509.CRL.Extension.DCRLI.Properties public
