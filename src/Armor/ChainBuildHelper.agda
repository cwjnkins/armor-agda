{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
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

module Armor.ChainBuildHelper where

open Armor.Grammar.Definitions UInt8
open IList                     UInt8
  hiding (toList)

usage : String
usage = "usage: 'aeres CERTS --SKI/--AKI"

parseCertsPEM : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 CertList))
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
      case runParser parseCertList (PEM.extractCerts certs) of λ where
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

main : IO.Main
main = IO.run $
  Armor.IO.getArgs IO.>>= λ args →
  case
    processCmdArgs args (record { certs = nothing ; isSKI = false; isAKI = false })
  of λ where
    (inj₁ msg) →
      Armor.IO.putStrLnErr ("-- " String.++ msg)
      IO.>> Armor.IO.exitFailure
    (inj₂ cmd) →
      case (CmdArg.certs cmd) of λ where
        nothing →
          Armor.IO.putStrLnErr ("-- error --")
          IO.>> Armor.IO.exitFailure
        (just certs) →
          readPEM certs
          IO.>>= λ cs → printer (IList.toList _ (proj₂ cs)) (CmdArg.isSKI cmd) (CmdArg.isAKI cmd)
  where
  record CmdArgTmp : Set where
    pattern
    field
      certs : Maybe String
      isSKI : Bool
      isAKI : Bool

  record CmdArg : Set where
    field
      certs : Maybe String
      isSKI : Bool
      isAKI : Bool

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
  processCmdArgs ("--SKI" ∷ certs ∷ []) cmd = inj₂ (record { certs = just certs ; isSKI = true ; isAKI = false })
  processCmdArgs ("--AKI" ∷ certs ∷ []) cmd = inj₂ (record { certs = just certs ; isSKI = false ; isAKI = true })  
  processCmdArgs _ cmd = inj₁ "unrecognized arguments"

  readPEM : (filename : String) → IO.IO (Exists─ _ CertList)
  readPEM filename =
    IO.readFiniteFile filename
    IO.>>= (parseCertsPEM filename ∘ String.toList)
    IO.>>= λ certs → let (_ , success pre r r≡ cs suf ps≡) = certs in
    IO.return (_ , cs)

  record Output : Set where
    field
      ID : List UInt8

  certOutput : ∀ {@0 bs} → Cert bs → Bool → Bool → Output
  Output.ID (certOutput x false false) = []
  Output.ID (certOutput x false true) = Cert.getAKIBytes x (Cert.getAKI x)
  Output.ID (certOutput x true false) = Cert.getSKIBytes x (Cert.getSKI x)
  Output.ID (certOutput x true true) = []

  showOutput : Output → String
  showOutput o = (showBytes ID) String.++ "\n"
    where
    open Output o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

  printer : List (Exists─ _ Cert) → Bool → Bool → _
  printer [] _ _ = Armor.IO.putStrLnErr ("")
  printer (cert ∷ rest) isSKI isAKI =
    IO.putStrLn (showOutput (certOutput (proj₂ cert) isSKI isAKI)) IO.>>
    printer rest isSKI isAKI
