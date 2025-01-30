{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
open import Armor.Data.X509.Cert as Cert
open import Armor.Data.X509.CRL.CertList as CRL
open import Armor.Data.X509.CRL.Semantic.Validation2
open import Armor.Data.X509.CRL.Semantic.Utils2
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
    processCmdArgs args (record { certs = nothing ; crls = nothing ; deltas = nothing})
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
                 case (CmdArg.deltas cmd) of λ where
                   (just delta) → readDER delta
                     IO.>>= λ deltas─ → helper₁ (proj₂ certs─) (proj₂ crls─) (proj₂ deltas─) 
                   nothing → helper₂ (proj₂ certs─) (proj₂ crls─)
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
      deltas : Maybe String

  record CmdArg : Set where
    field
      certs : Maybe String
      crls : Maybe String
      deltas : Maybe String

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
  processCmdArgs (certs ∷ crls ∷ deltas ∷ []) cmd = inj₂ (record { certs = just certs ; crls = just crls ; deltas = just deltas})
  processCmdArgs (certs ∷ crls ∷ []) cmd = inj₂ (record { certs = just certs ; crls = just crls ; deltas = nothing})
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

  printer : Status → String
  printer record { sts = REVOKED ; rsn = (just allReasons) } = "REVOKED -- allReasons"
  printer record { sts = REVOKED ; rsn = (just unspecified) } = "REVOKED -- unspecified"
  printer record { sts = REVOKED ; rsn = (just keyCompromise) } = "REVOKED -- keyCompromise"
  printer record { sts = REVOKED ; rsn = (just cACompromise) } = "REVOKED -- cACompromise"
  printer record { sts = REVOKED ; rsn = (just affiliationChanged) } = "REVOKED -- affiliationChanged"
  printer record { sts = REVOKED ; rsn = (just superseded) } = "REVOKED -- superseded"
  printer record { sts = REVOKED ; rsn = (just cessationOfOperation) } = "REVOKED -- cessationOfOperation"
  printer record { sts = REVOKED ; rsn = (just certificateHold) } = "REVOKED -- certificateHold"
  printer record { sts = REVOKED ; rsn = (just removeFromCRL) } = "REVOKED -- removeFromCRL"
  printer record { sts = REVOKED ; rsn = (just privilegeWithdrawn) } = "REVOKED -- privilegeWithdrawn"
  printer record { sts = REVOKED ; rsn = (just aACompromise) } = "REVOKED -- aACompromise"
  printer record { sts = REVOKED ; rsn = nothing } = "REVOKED"
  printer record { sts = UNREVOKED ; rsn = rsn } = "UNREVOKED"

  helper₁ : ∀{@0 bs₁ bs₂ bs₃} → SequenceOf Cert bs₁ → CRL.CertList bs₂ → CRL.CertList bs₃ → _
  helper₁ nil crl delta = Armor.IO.putStrLnErr ("-- ")
                          IO.>> Armor.IO.exitFailure
  helper₁ (cons (mkIListCons cert rest bs≡)) crl delta =
    case Main (mkRevInputs cert crl (just delta) true) of λ where
      (inj₁ x) → Armor.IO.putStrLnErr (x)
                 IO.>> Armor.IO.exitFailure
      (inj₂ y) → IO.putStrLn (printer y)
                 IO.>> helper₁ rest crl delta

  helper₂ : ∀{@0 bs₁ bs₂} → SequenceOf Cert bs₁ → CRL.CertList bs₂ → _
  helper₂ nil crl = Armor.IO.putStrLnErr ("-- ")
                    IO.>> Armor.IO.exitFailure
  helper₂ (cons (mkIListCons cert rest bs≡)) crl =
    case Main (mkRevInputs{_}{_}{[]} cert crl nothing false) of λ where
      (inj₁ x) → Armor.IO.putStrLnErr (x)
                 IO.>> Armor.IO.exitFailure
      (inj₂ y) → IO.putStrLn (printer y)
                 IO.>> helper₂ rest crl
