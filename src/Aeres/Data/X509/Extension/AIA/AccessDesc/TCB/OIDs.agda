{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.Parser
open import Aeres.Data.X690-DER.OID.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.Extension.AIA.AccessDesc.TCB.OIDs where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

OSCPLit : List UInt8
OSCPLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 1 ]

OSCP : OIDValue OSCPLit
OSCP = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length OSCPLit)) OSCPLit)} tt))


CAIssuersLit : List UInt8
CAIssuersLit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 48 ∷ [ # 2 ]

CAIssuers : OIDValue CAIssuersLit
CAIssuers = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CAIssuersLit)) CAIssuersLit)} tt))

