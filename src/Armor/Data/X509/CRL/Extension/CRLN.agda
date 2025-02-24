{-# OPTIONS --erasure #-}
import Armor.Data.X509.CRL.Extension.CRLN.Parser
import Armor.Data.X509.CRL.Extension.CRLN.TCB
import Armor.Data.X509.CRL.Extension.CRLN.Properties

module Armor.Data.X509.CRL.Extension.CRLN where

open Armor.Data.X509.CRL.Extension.CRLN.Parser public
open Armor.Data.X509.CRL.Extension.CRLN.TCB    public

module CRLN where
  open Armor.Data.X509.CRL.Extension.CRLN.Properties public
