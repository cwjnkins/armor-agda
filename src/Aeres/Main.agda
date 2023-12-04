{-# OPTIONS --guardedness --sized-types #-}

open import Aeres.Binary
  hiding (module Base64)
import      Aeres.Data.Base64 as Base64
import      Aeres.Data.PEM as PEM
open import Aeres.Data.X509
-- open import Aeres.Data.X509.ChainBuilder.Exec
open import Aeres.Data.X509.Semantic.Chain.Builder
open import Aeres.Data.X509.Semantic.Cert
open import Aeres.Data.X509.Semantic.Chain
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Grammar.Parser
import      Aeres.IO
open import Aeres.Foreign.ByteString
  hiding (foldl)
import      Aeres.Foreign.Time as FFI
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
open import Data.Nat.Show renaming (show to showℕ) 
import      IO

module Aeres.Main where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Base256

usage : String
usage = "usage: 'aeres CERTCHAIN TRUSTEDSTORE"

-- str2dig : String → Maybe (List Dig)
-- str2dig xs = do
--   bs ← decToMaybe ∘ All.all? (_<? 256) ∘ map toℕ ∘ String.toList $ xs
--   return (map (λ where (n , n<256) → Fin.fromℕ< n<256) (All.toList bs))

-- TODO: bindings for returning error codes?
parseDERCerts : (fileName : String) (contents : List UInt8) → IO.IO (Exists─ _ (Success UInt8 CertList))
parseDERCerts fn contents =
  case runParser parseCertList contents of λ where
    (mkLogged log₂ (no  _)) →
      Aeres.IO.putStrLnErr
        (fn String.++ " (decoded): failed to parse bytestring as X.509" String.++ "\n"
         String.++ (foldl String._++_ "-- " log₂))
      IO.>> Aeres.IO.exitFailure
    (mkLogged log₂ (yes (success prefix read read≡ chainX509 suf@(_ ∷ _) ps≡))) →
      Aeres.IO.putStrLnErr
        (fn String.++ " (decoded): incomplete read\n"
         String.++ "-- only read "
           String.++ (showℕ (Aeres.Grammar.IList.lengthIList _ chainX509))
           String.++ " certificate(s), but more bytes remain\n"
         String.++ "-- attempting to parse remainder")
      IO.>> ((case runParser parseCert suf of λ where
        (mkLogged log₃ (yes _)) →
          Aeres.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
          IO.>> Aeres.IO.exitFailure
        (mkLogged log₃ (no _)) →
          Aeres.IO.putStrLnErr (fn String.++ " (decoded): "
            String.++ show (map toℕ (take 10 suf))
            String.++ foldl String._++_ "" log₃)
          IO.>> Aeres.IO.exitFailure))
    (mkLogged log₂ (yes schain)) → IO.return (_ , schain)

parseCerts : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 CertList))
parseCerts fn input =
  case proj₁ (LogDec.runMaximalParser Char PEM.parseCertList input) of λ where
    (mkLogged log₁ (no ¬p)) →
      Aeres.IO.putStrLnErr (foldl String._++_ "" log₁)
      IO.>> Aeres.IO.exitFailure
    (mkLogged log₁ (yes (success prefix read read≡ chain suf@(_ ∷ _) ps≡))) →
      Aeres.IO.putStrLnErr 
        (fn String.++ ": incomplete read\n"
         String.++ "-- only read " String.++ (showℕ (Aeres.Grammar.IList.lengthIList _ chain))
         String.++ " certificate(s), but " String.++ (showℕ (length suf)) String.++ " byte(s) remain")
      IO.>> Aeres.IO.putStrLnErr "-- attempting to parse remainder"
      IO.>> (case proj₁ (LogDec.runMaximalParser Char PEM.parseCert suf) of λ where
        (mkLogged log₂ (yes _)) →
          Aeres.IO.putStrLnErr "-- parse remainder success (SHOULD NOT HAPPEN!)"
          IO.>> Aeres.IO.exitFailure
        (mkLogged log₂ (no  _)) →
          Aeres.IO.putStrLnErr (foldl String._++_ "-- " log₂)
          IO.>> Aeres.IO.exitFailure)
    (mkLogged log₁ (yes (success prefix read read≡ chain [] ps≡))) →
      case runParser parseCertList (PEM.extractCerts chain) of λ where
        (mkLogged log₂ (no  _)) →
          Aeres.IO.putStrLnErr
            (fn String.++ " (decoded): failed to parse PEM as X.509" String.++ "\n"
             String.++ (foldl String._++_ "-- " log₂))
          IO.>> Aeres.IO.exitFailure
        (mkLogged log₂ (yes (success prefix read read≡ chainX509 suf@(_ ∷ _) ps≡))) →
          Aeres.IO.putStrLnErr
            (fn String.++ " (decoded): incomplete read\n"
             String.++ "-- only read "
               String.++ (showℕ (Aeres.Grammar.IList.lengthIList _ chainX509))
               String.++ " certificate(s), but more bytes remain\n"
             String.++ "-- attempting to parse remainder")
          IO.>> ((case runParser parseCert suf of λ where
            (mkLogged log₃ (yes _)) →
              Aeres.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
              IO.>> Aeres.IO.exitFailure
            (mkLogged log₃ (no _)) →
              Aeres.IO.putStrLnErr (fn String.++ " (decoded): "
                String.++ show (map toℕ (take 10 suf))
                String.++ foldl String._++_ "" log₃)
              IO.>> Aeres.IO.exitFailure))
        (mkLogged log₂ (yes schain)) → IO.return (_ , schain)

main : IO.Main
main = IO.run $
  Aeres.IO.getArgs IO.>>= λ args →
  case args of λ where
    ("--DER" ∷ certName ∷ rootName ∷ []) →
      Aeres.IO.openFile certName Aeres.IO.Primitive.readMode
      IO.>>= λ h → Aeres.IO.hGetByteStringContents h
      IO.>>= λ contentBS → let bs = Aeres.Foreign.ByteString.toUInt8 contentBS in
      parseDERCerts certName bs
      IO.>>= λ certS → let (_ , success pre₁ r₁ r₁≡ cert suf₁ ps≡₁) = certS in
      IO.readFiniteFile rootName
      IO.>>= (parseCerts rootName ∘ String.toList)
      IO.>>= λ rootS → let (_ , success pre₂ r₂ r₂≡ trustedRoot suf₂ ps≡₂) = rootS in
      runCertChecks (chainToList₁ trustedRoot) (chainToList₁ cert)
    (certName ∷ rootName ∷ []) →
      IO.readFiniteFile certName
      IO.>>= (parseCerts certName ∘ String.toList)
      IO.>>= λ certS → let (_ , success pre₁ r₁ r₁≡ cert suf₁ ps≡₁) = certS in
      IO.readFiniteFile rootName
      IO.>>= (parseCerts rootName ∘ String.toList)
      IO.>>= λ rootS → let (_ , success pre₂ r₂ r₂≡ trustedRoot suf₂ ps≡₂) = rootS in
      runCertChecks (chainToList₁ trustedRoot) (chainToList₁ cert)
    _ →
      Aeres.IO.putStrLnErr usage
      IO.>> Aeres.IO.putStrLnErr "-- wrong number of arguments passed"
      IO.>> Aeres.IO.exitFailure

  where
  record Output : Set where
    field
      sigAlgOID  : List UInt8
      tbsBytes   : List UInt8
      pkBytes    : List UInt8
      sigBytes   : List UInt8
      ekuOIDBytes : List (List UInt8)

  certOutput : ∀ {@0 bs} → Cert bs → Output
  Output.sigAlgOID (certOutput x) = SignAlg.getOIDBS ∘ proj₂ ∘ Cert.getTBSCertSignAlg $ x
  Output.tbsBytes  (certOutput x) = Cert.getTBSBytes x
  Output.pkBytes   (certOutput x) = Cert.getPublicKeyBytes x
  Output.sigBytes  (certOutput x) = Cert.getSignatureValueBytes x
  Output.ekuOIDBytes (certOutput x) = Cert.getEKUOIDList x (Cert.getEKU x)

  showOutput : Output → String
  showOutput o =
              (showBytes tbsBytes)  String.++ "\n"
    String.++ (showBytes sigBytes)  String.++ "\n"
    String.++ (showBytes pkBytes)   String.++ "\n"
    String.++ (showBytes sigAlgOID) String.++ "\n"
    String.++ (showListBytes ekuOIDBytes) String.++ "\n"
    String.++ "***************"
    where
    open Output o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

    showListBytes : List (List UInt8) → String
    showListBytes [] = ""
    showListBytes (x ∷ x₁) = (showBytes x) String.++ "@@ " String.++ (showListBytes x₁)


  runCheck : ∀ {@0 bs} → Cert bs → String
             → {P : ∀ {@0 bs} → Cert bs → Set}
             → (∀ {@0 bs} → (c : Cert bs) → Dec (P c))
             → IO.IO ⊤
  runCheck c m d
    with d c
  ... | no ¬p =
    Aeres.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Aeres.IO.exitFailure
  ... | yes p =
    Aeres.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return tt

  runChainCheck : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
    → (chain : Chain trustedRoot candidates issuee) → String
    → {P : ∀ {@0 bs} → Cert bs → Chain trustedRoot candidates issuee → Set}
    → (Dec (P issuee chain))
    → IO.IO ⊤
  runChainCheck i c m d
    with d
  ... | no ¬p =
    Aeres.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Aeres.IO.exitFailure
  ... | yes p =
    Aeres.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return tt

  runChecks' :  ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → (issuee : Cert bs) → ℕ → Chain trustedRoot candidates issuee  → IO.IO ⊤
  runChecks' issuee n (root x) =
     Aeres.IO.putStrLnErr ("=== Checking " String.++ (showℕ n)) IO.>>
     runCheck issuee "SCP1" scp1 IO.>>
     runCheck issuee "SCP2" scp2 IO.>>
     runCheck issuee "SCP4" scp4 IO.>>
     runCheck issuee "SCP5" scp5 IO.>>
     runCheck issuee "SCP6" scp6 IO.>>
     runCheck issuee "SCP7" scp7 IO.>>
     runCheck issuee "SCP8" scp8 IO.>>
     runCheck issuee "SCP9" scp9 IO.>>
     runCheck issuee "SCP10" scp10 IO.>>
     runCheck issuee "SCP11" scp11 IO.>>
     runCheck issuee "SCP12" scp12 IO.>>
     runCheck issuee "SCP13" scp13 IO.>>
     runCheck issuee "SCP14" scp14 IO.>>
     runCheck issuee "SCP15" scp15 IO.>>
     runCheck issuee "SCP16" scp16 IO.>>
     runCheck issuee "SCP17" scp17 IO.>>
     (if ⌊ n ≟ 1 ⌋ then (runCheck issuee "SCP19" scp19) else (IO.return tt)) IO.>>
     Aeres.IO.getCurrentTime IO.>>= λ now →
     Aeres.IO.putStrLnErr (FFI.showTime now) IO.>>= λ _ →
     case GeneralizedTime.fromForeignUTC now of λ where
       (no ¬p) →
         Aeres.IO.putStrLnErr "SCP18: failed to read time from system" IO.>>
         Aeres.IO.exitFailure
       (yes p) →
         runCheck issuee "SCP18" (λ c₁ → scp18 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl)))
  runChecks' issuee n (link issuer isIn chain) =
     Aeres.IO.putStrLnErr ("=== Checking " String.++ (showℕ n)) IO.>>
     runCheck issuee "SCP1" scp1 IO.>>
     runCheck issuee "SCP2" scp2 IO.>>
     runCheck issuee "SCP4" scp4 IO.>>
     runCheck issuee "SCP5" scp5 IO.>>
     runCheck issuee "SCP6" scp6 IO.>>
     runCheck issuee "SCP7" scp7 IO.>>
     runCheck issuee "SCP8" scp8 IO.>>
     runCheck issuee "SCP9" scp9 IO.>>
     runCheck issuee "SCP10" scp10 IO.>>
     runCheck issuee "SCP11" scp11 IO.>>
     runCheck issuee "SCP12" scp12 IO.>>
     runCheck issuee "SCP13" scp13 IO.>>
     runCheck issuee "SCP14" scp14 IO.>>
     runCheck issuee "SCP15" scp15 IO.>>
     runCheck issuee "SCP16" scp16 IO.>>
     runCheck issuee "SCP17" scp17 IO.>>
     (if ⌊ n ≟ 1 ⌋ then (runCheck issuee "SCP19" scp19) else (IO.return tt)) IO.>>
     Aeres.IO.getCurrentTime IO.>>= λ now →
     Aeres.IO.putStrLnErr (FFI.showTime now) IO.>>= λ _ →
     case GeneralizedTime.fromForeignUTC now of λ where
       (no ¬p) →
         Aeres.IO.putStrLnErr "SCP18: failed to read time from system" IO.>>
         Aeres.IO.exitFailure
       (yes p) →
         runCheck issuee "SCP18" (λ c₁ → scp18 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl))) IO.>>
         (IO.putStrLn (showOutput (certOutput issuer)) IO.>>
         runChecks' issuer (n + 1) chain)

  helper₁ : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → (issuee : Cert bs) → Chain trustedRoot candidates issuee → IO.IO Bool
  helper₁ issuee chain =
    runChecks' issuee 1 chain IO.>>
    runChainCheck issuee chain "CCP2" (ccp2 issuee chain) IO.>>
    runChainCheck issuee chain "CCP3" (ccp3 issuee chain) IO.>>
    runChainCheck issuee chain "CCP4" (ccp4 issuee chain) IO.>>
    runChainCheck issuee chain "CCP5" (ccp5 issuee chain) IO.>>
    runChainCheck issuee chain "CCP10" (ccp10 issuee chain) IO.>>
    IO.return true

  helper₂ : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} (issuee : Cert bs)
    → List (Chain trustedRoot candidates issuee) → _
  helper₂ issuee [] = Aeres.IO.putStrLnErr "Error: no valid chain found" 
  helper₂ issuee (chain ∷ otherChains) =
    helper₁ issuee chain IO.>>= λ where
      false →  helper₂ issuee otherChains
      true → Aeres.IO.exitSuccess

  runCertChecks : (trustedRoot candidates : List (Exists─ _ Cert)) → _
  runCertChecks trustedRoot [] = Aeres.IO.putStrLnErr "Error: no candidate certificates"
  runCertChecks trustedRoot (end ∷ restCerts) =
    helper₂ (proj₂ end) (buildChains trustedRoot restCerts (proj₂ end))
