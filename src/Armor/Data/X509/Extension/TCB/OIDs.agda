open import Armor.Binary
open import Armor.Data.X690-DER.OID.Parser
open import Armor.Data.X690-DER.OID.TCB
open import Armor.Data.X690-DER.Tag
import      Armor.Grammar.Definitions
import      Armor.Grammar.Parallel.TCB
import      Armor.Grammar.Parser
open import Armor.Prelude

module Armor.Data.X509.Extension.TCB.OIDs where

open Armor.Grammar.Definitions  UInt8
open Armor.Grammar.Parallel.TCB UInt8
open Armor.Grammar.Parser       UInt8

AKILit : List UInt8
AKILit = # 85 ∷ # 29 ∷ [ # 35 ]

AKI : OIDValue AKILit
AKI = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length AKILit)) AKILit)} tt))

SKILit : List UInt8
SKILit = # 85 ∷ # 29 ∷ [ # 14 ]

SKI : OIDValue SKILit
SKI = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SKILit)) SKILit)} tt))

KULit : List UInt8
KULit =  # 85 ∷ # 29 ∷ [ # 15 ]

KU : OIDValue KULit
KU = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length KULit)) KULit)} tt))

EKULit : List UInt8
EKULit =  # 85 ∷ # 29 ∷ [ # 37 ]

EKU : OIDValue EKULit
EKU = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length EKULit)) EKULit)} tt))

BCLit : List UInt8
BCLit =  # 85 ∷ # 29 ∷ [ # 19 ]

BC : OIDValue BCLit
BC = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length BCLit)) BCLit)} tt))

IANLit : List UInt8
IANLit =  # 85 ∷ # 29 ∷ [ # 18 ]

IAN : OIDValue IANLit
IAN = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length IANLit)) IANLit)} tt))

SANLit : List UInt8
SANLit =  # 85 ∷ # 29 ∷ [ # 17 ]

SAN : OIDValue SANLit
SAN = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length SANLit)) SANLit)} tt))

CPOLLit : List UInt8
CPOLLit =   # 85 ∷ # 29 ∷ [ # 32 ]

CPOL : OIDValue CPOLLit
CPOL = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CPOLLit)) CPOLLit)} tt))

CRLDISTLit : List UInt8
CRLDISTLit =   # 85 ∷ # 29 ∷ [ # 31 ]

CRLDIST : OIDValue CRLDISTLit
CRLDIST = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CRLDISTLit)) CRLDISTLit)} tt))

NCLit : List UInt8
NCLit =   # 85 ∷ # 29 ∷ [ # 30 ]

NC : OIDValue NCLit
NC = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length NCLit)) NCLit)} tt))

PCLit : List UInt8
PCLit =   # 85 ∷ # 29 ∷ [ # 36 ]

PC : OIDValue PCLit
PC = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PCLit)) PCLit)} tt))

PMLit : List UInt8
PMLit =   # 85 ∷ # 29 ∷ [ # 33 ]

PM : OIDValue PMLit
PM = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length PMLit)) PMLit)} tt))

INAPLit : List UInt8
INAPLit =  # 85 ∷ # 29 ∷ [ # 54 ]

INAP : OIDValue INAPLit
INAP = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length INAPLit)) INAPLit)} tt))

AIALit : List UInt8
AIALit = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ # 1 ∷ [ # 1 ]

AIA : OIDValue AIALit
AIA = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length AIALit)) AIALit)} tt))

module EKU where
  AnyExtendedKeyUsageLit : List UInt8
  AnyExtendedKeyUsageLit = # 85 ∷ # 29 ∷ # 37 ∷ [ # 0 ]

  AnyExtendedKeyUsage : OIDValue AnyExtendedKeyUsageLit
  AnyExtendedKeyUsage = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length AnyExtendedKeyUsageLit)) AnyExtendedKeyUsageLit)} tt))

  KeyPurposePrefix : List UInt8
  KeyPurposePrefix = # 43 ∷ # 6 ∷ # 1 ∷ # 5 ∷ # 5 ∷ # 7 ∷ [ # 3 ]

  ServerAuthLit : List UInt8
  ServerAuthLit = KeyPurposePrefix ++ [ # 1 ]

  ServerAuth : OIDValue ServerAuthLit
  ServerAuth = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length ServerAuthLit)) ServerAuthLit)} tt))

  ClientAuthLit : List UInt8
  ClientAuthLit = KeyPurposePrefix ++ [ # 2 ]

  ClientAuth : OIDValue ClientAuthLit
  ClientAuth = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length ClientAuthLit)) ClientAuthLit)} tt))

  CodeSignLit : List UInt8
  CodeSignLit = KeyPurposePrefix ++ [ # 3 ]

  CodeSign : OIDValue CodeSignLit 
  CodeSign = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length CodeSignLit)) CodeSignLit)} tt))

  EmailProtLit : List UInt8
  EmailProtLit = KeyPurposePrefix ++ [ # 4 ]

  EmailProt : OIDValue EmailProtLit
  EmailProt = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length EmailProtLit)) EmailProtLit)} tt))

  TimeStampLit : List UInt8
  TimeStampLit = KeyPurposePrefix ++ [ # 8 ]

  TimeStamp : OIDValue TimeStampLit
  TimeStamp = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length TimeStampLit)) TimeStampLit)} tt))

  OCSPSignLit : List UInt8
  OCSPSignLit = KeyPurposePrefix ++ [ # 9 ]

  OCSPSign : OIDValue OCSPSignLit
  OCSPSign = fstₚ (Success.value (toWitness{Q = Logging.val (runParser (parseOIDValue (length OCSPSignLit)) OCSPSignLit)} tt))

  SupportedKeyUsageIDs : List (Exists─ _ OIDValue)
  SupportedKeyUsageIDs = (─ _ , AnyExtendedKeyUsage) ∷ (─ _ , ServerAuth) ∷ (─ _ , ClientAuth) ∷ (─ _ , CodeSign) ∷ (─ _ , EmailProt) ∷ (─ _ , TimeStamp) ∷ [ (─ _ , OCSPSign) ] 
