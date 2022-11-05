{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.HashAlg.TCB
import Aeres.Data.X509.HashAlg.Parser

module Aeres.Data.X509.HashAlg where

module RSASSA-PSS where
  open Aeres.Data.X509.HashAlg.TCB.RSASSA-PSS public
  open Aeres.Data.X509.HashAlg.Parser.RSASSA-PSS public
