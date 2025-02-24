{-# OPTIONS --erasure #-}
import Armor.Data.X509.CRL.Extension.IDP.Eq
import Armor.Data.X509.CRL.Extension.IDP.Parser
import Armor.Data.X509.CRL.Extension.IDP.TCB
import Armor.Data.X509.CRL.Extension.IDP.Properties

module Armor.Data.X509.CRL.Extension.IDP where

open Armor.Data.X509.CRL.Extension.IDP.Parser public
open Armor.Data.X509.CRL.Extension.IDP.TCB    public

module IDP where
  open Armor.Data.X509.CRL.Extension.IDP.Eq public
  open Armor.Data.X509.CRL.Extension.IDP.Properties public
