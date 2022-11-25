{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X690-DER.OID.Parser
open import Aeres.Data.X690-DER.OID.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Parser
open import Aeres.Prelude

module Aeres.Data.X509.MaskGenAlg.TCB.OIDs where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Parser      UInt8

{-
   pkcs-1  OBJECT IDENTIFIER  ::=  { iso(1) member-body(2)
                           us(840) rsadsi(113549) pkcs(1) 1 }

   -- When id-mgf1 is used in an AlgorithmIdentifier the parameters
   -- MUST be present and MUST be a HashAlgorithm.

   id-mgf1  OBJECT IDENTIFIER  ::=  { pkcs-1 8 }
-}

MGF1Lit : List UInt8
MGF1Lit = # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 8 ]

MGF1 : OIDValue MGF1Lit
MGF1 = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length MGF1Lit)) MGF1Lit)} tt))
