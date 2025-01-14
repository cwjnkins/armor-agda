{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
open import Armor.Data.X509.CRL.CertList as CRL
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
    processCmdArgs args (record { crls = nothing })
  of λ where
    (inj₁ msg) →
      Armor.IO.putStrLnErr ("-- " String.++ msg)
      IO.>> Armor.IO.exitFailure
    (inj₂ cmd) →
      case (CmdArg.crls cmd) of λ where
        nothing →
          Armor.IO.putStrLnErr ("-- error --")
          IO.>> Armor.IO.exitFailure
        (just crls) →
          readDER crls
          IO.>>= λ cs → printer (proj₂ cs)
  where
  record CmdArgTmp : Set where
    pattern
    field
      crls : Maybe String

  record CmdArg : Set where
    field
      crls : Maybe String

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
  processCmdArgs (crls ∷ []) cmd = inj₂ (record { crls = just crls })
  processCmdArgs _ cmd = inj₁ "unrecognized arguments"

  readDER : (filename : String) → IO.IO (Exists─ _ CRL.CertList)
  readDER filename =
    Armor.IO.openFile filename Armor.IO.Primitive.readMode
    IO.>>= Armor.IO.hGetByteStringContents
    IO.>>= λ contents → let bs = Armor.Foreign.ByteString.toUInt8 contents in
    parseCRLDER filename bs
    IO.>>= λ crls → let (_ , success pre r r≡ crls suf ps≡) = crls in
    IO.return (_ , crls)

  record Output : Set where
    field
      ID : List UInt8

  crlOutput : ∀ {@0 bs} → CRL.CertList bs → Output
  Output.ID (crlOutput x) = []

  showOutput : Output → String
  showOutput o = (showBytes ID) String.++ "\n"
    where
    open Output o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

  printer : ∀ {@0 bs} → CRL.CertList bs → _
  printer crl = IO.putStrLn (showOutput (crlOutput crl))
