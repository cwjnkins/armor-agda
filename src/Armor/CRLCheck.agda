{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
open import Armor.Data.X509.Cert as Cert
open import Armor.Data.X509.CRL.CertList as CRL
open import Armor.Data.X509.CRL.Semantic.Validation
import      Armor.Grammar.Definitions
import      Armor.Grammar.IList as IList
open import Armor.Grammar.Parser
import      Armor.IO
open import Armor.Foreign.ByteString
  hiding (foldl)
import      Armor.Foreign.Time as FFI
open import Armor.Prelude
import      Data.Nat.Properties as Nat
open import Data.Nat.Show renaming (show to showℕ) 
import      IO

module Armor.CRLCheck where

open Armor.Grammar.Definitions UInt8
open IList                     UInt8
  hiding (toList)

usage : String
usage = "usage: 'aeres CRL ..."

parseCertsPEM : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 Cert.CertList))
parseCertsPEM fn input =
  case proj₁ (LogDec.runMaximalParser Char PEM.parseCertList input) of λ where
    (mkLogged log (no ¬p)) →
      Armor.IO.putStrLnErr (foldl String._++_ "" log)
      IO.>> Armor.IO.exitFailure
    (mkLogged log (yes (success prefix read read≡ certs (_ ∷ _) ps≡))) →
      Armor.IO.putStrLnErr 
        (fn String.++ ": incomplete read\n")
      IO.>> Armor.IO.exitFailure
    (mkLogged log (yes (success prefix read read≡ certs [] ps≡))) → 
      case runParser Cert.parseCertList (PEM.extractCerts certs) of λ where
        (mkLogged log₂ (no  _)) →
          Armor.IO.putStrLnErr
            (fn String.++ " (decoded): failed to parse PEM as X.509" String.++ "\n"
             String.++ (foldl String._++_ "-- " log₂))
          IO.>> Armor.IO.exitFailure
        (mkLogged log₂ (yes (success prefix read read≡ certs (_ ∷ _) ps≡))) →
          Armor.IO.putStrLnErr
            (fn String.++ " (decoded): incomplete read\n")
          IO.>> Armor.IO.exitFailure
        (mkLogged log₂ (yes certs)) → IO.return (_ , certs)


parseCRLDER : (fileName : String) (contents : List UInt8) → IO.IO (Exists─ _ (Success UInt8 CRL.CertList))
parseCRLDER fn contents =
  case runParser CRL.parseCertList contents of λ where
    (mkLogged log₂ (no  _)) →
      Armor.IO.putStrLnErr
        (fn String.++ " (decoded): failed to parse bytestring as X.509 CRL" String.++ "\n"
         String.++ (foldl String._++_ "-- " log₂))
      IO.>> Armor.IO.exitFailure
    (mkLogged log₂ (yes (success prefix read read≡ crl suf@(_ ∷ _) ps≡))) →
      Armor.IO.putStrLnErr
        (fn String.++ " (decoded): incomplete read\n"
         String.++ "-- attempting to parse remainder")
      IO.>> ((case runParser CRL.parseCertList suf of λ where
        (mkLogged log₃ (yes _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
          IO.>> Armor.IO.exitFailure
        (mkLogged log₃ (no _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): "
            String.++ show (map toℕ (take 10 suf))
            String.++ foldl String._++_ "" log₃)
          IO.>> Armor.IO.exitFailure))
    (mkLogged log₂ (yes crl)) → IO.return (_ , crl)


main : IO.Main
main = IO.run $
  Armor.IO.getArgs IO.>>= λ args →
  case
    processCmdArgs args (record { certs = nothing ; crls = nothing })
  of λ where
    (inj₁ msg) →
      Armor.IO.putStrLnErr ("-- " String.++ msg)
      IO.>> Armor.IO.exitFailure
    (inj₂ cmd) →
      case (CmdArg.certs cmd) of λ where
        (just cert) → readPEM cert
           IO.>>= λ certs─ →
           case (CmdArg.crls cmd) of λ where
             (just crl) → readDER crl
               IO.>>= λ crls─ →
                 case certs─ of λ where
                   (─ .[] , nil) → Armor.IO.putStrLnErr ("-- ")
                                   IO.>> Armor.IO.exitFailure
                   (fst , cons (mkIListCons cert- rest bs≡)) → 
                     case callProcessRevocation (mkRevInputs cert- (proj₂ crls─) false) of λ where
                       v → IO.putStrLn (printer v)
             nothing → Armor.IO.putStrLnErr ("-- ")
                      IO.>> Armor.IO.exitFailure
        nothing → Armor.IO.putStrLnErr ("-- ")
                  IO.>> Armor.IO.exitFailure
  where
  record CmdArgTmp : Set where
    pattern
    field
      certs : Maybe String
      crls : Maybe String

  record CmdArg : Set where
    field
      certs : Maybe String
      crls : Maybe String

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
  processCmdArgs (certs ∷ crls ∷ []) cmd = inj₂ (record { certs = just certs ; crls = just crls })
  processCmdArgs _ cmd = inj₁ "unrecognized arguments"

  readPEM : (filename : String) → IO.IO (Exists─ _ Cert.CertList)
  readPEM filename =
    IO.readFiniteFile filename
    IO.>>= (parseCertsPEM filename ∘ String.toList)
    IO.>>= λ certs → let (_ , success pre r r≡ cs suf ps≡) = certs in
    IO.return (_ , cs)
    
  readDER : (filename : String) → IO.IO (Exists─ _ CRL.CertList)
  readDER filename =
    Armor.IO.openFile filename Armor.IO.Primitive.readMode
    IO.>>= Armor.IO.hGetByteStringContents
    IO.>>= λ contents → let bs = Armor.Foreign.ByteString.toUInt8 contents in
    parseCRLDER filename bs
    IO.>>= λ crls → let (_ , success pre r r≡ crls suf ps≡) = crls in
    IO.return (_ , crls)

  printer : CertStatus → String
  printer unspecified = ("unspecified")
  printer keyCompromise = ("keyCompromise")
  printer cACompromise = ("cACompromise")
  printer affiliationChanged = ("affiliationChanged")
  printer superseded = ("superseded")
  printer cessationOfOperation = ("cessationOfOperation")
  printer certificateHold = ("certificateHold")
  printer removeFromCRL = ("removeFromCRL")
  printer privilegeWithdrawn = ("privilegeWithdrawn")
  printer aACompromise = ("aACompromise")
  printer UNREVOKED = ("UNREVOKED")
  printer UNDETERMINED = ("UNDETERMINED")
