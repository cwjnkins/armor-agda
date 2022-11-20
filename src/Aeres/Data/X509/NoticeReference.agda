{-# OPTIONS --subtyping #-}

import Aeres.Data.X509.NoticeReference.Parser
import Aeres.Data.X509.NoticeReference.Properties
import Aeres.Data.X509.NoticeReference.TCB

module Aeres.Data.X509.NoticeReference where

open Aeres.Data.X509.NoticeReference.Parser public
open Aeres.Data.X509.NoticeReference.TCB    public

module NoticeReference where
  open Aeres.Data.X509.NoticeReference.Properties public
