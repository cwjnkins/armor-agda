{-# OPTIONS --subtyping --guardedness --sized-types #-}

open import Aeres.Binary
  hiding (module Base64)
import      Aeres.Data.Base64 as Base64
import      Aeres.Data.PEM as PEM
open import Aeres.Data.X509
open import Aeres.Data.X509.ChainBuilder.Exec
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
parseCerts : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 Chain))
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
      case runParser parseChain (PEM.extractCerts chain) of λ where
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
    (certName ∷ rootName ∷ []) →
      IO.readFiniteFile certName
      IO.>>= (parseCerts certName ∘ String.toList)
      IO.>>= λ certS → let (_ , success pre₁ r₁ r₁≡ cert suf₁ ps≡₁) = certS in
      IO.readFiniteFile rootName
      IO.>>= (parseCerts rootName ∘ String.toList)
      IO.>>= λ rootS → let (_ , success pre₂ r₂ r₂≡ root suf₂ ps≡₂) = rootS in
      runCertChecks (proj₂ (listToChain (buildChain (chainToList cert) (chainToList root)))) -- calling chain builder here
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
      kuBits     : List Bool
      ekuOIDBytes : List (List UInt8)

  certOutput : ∀ {@0 bs} → Cert bs → Output
  Output.sigAlgOID (certOutput x) = SignAlg.getOIDBS ∘ proj₂ ∘ Cert.getTBSCertSignAlg $ x
  Output.tbsBytes  (certOutput x) = Cert.getTBSBytes x
  Output.pkBytes   (certOutput x) = Cert.getPublicKeyBytes x
  Output.sigBytes  (certOutput x) = Cert.getSignatureValueBytes x
  Output.kuBits    (certOutput x) = Cert.getKUBits x (Cert.getKU x)
  Output.ekuOIDBytes (certOutput x) = Cert.getEKUOIDList x (Cert.getEKU x)

  showOutput : Output → String
  showOutput o =
              (showBytes tbsBytes)  String.++ "\n"
    String.++ (showBytes sigBytes)  String.++ "\n"
    String.++ (showBytes pkBytes)   String.++ "\n"
    String.++ (showBytes sigAlgOID) String.++ "\n"
    String.++ (showBoolList kuBits) String.++ "\n"
    String.++ (showListBytes ekuOIDBytes) String.++ "\n"
    String.++ "***************"
    where
    open Output o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

    showListBytes : List (List UInt8) → String
    showListBytes [] = ""
    showListBytes (x ∷ x₁) = (showBytes x) String.++ "@@ " String.++ (showListBytes x₁)

    showBoolList : List Bool → String
    showBoolList xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

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

  runChainCheck : ∀ {@0 bs} → Chain bs → String
                  → {P : ∀ {@0 bs} → Chain bs → Set}
                  → (∀ {@0 bs} → (c : Chain bs) → Dec (P c))
                  → IO.IO ⊤
  runChainCheck c m d
    with d c
  ... | no ¬p =
    Aeres.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Aeres.IO.exitFailure
  ... | yes p =
    Aeres.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return tt

  runChecks' : ∀ {@0 bs} → ℕ → Chain bs → _
  runChecks' n nil = IO.return tt
  runChecks' n (cons (mkIListCons c tail bs≡)) =
    Aeres.IO.putStrLnErr ("=== Checking " String.++ (showℕ n)) IO.>>
    runCheck c "SCP1" scp1 IO.>>
    runCheck c "SCP2" scp2 IO.>>
    runCheck c "SCP3" scp3 IO.>>
    runCheck c "SCP4" scp4 IO.>>
    runCheck c "SCP5" scp5 IO.>>
    runCheck c "SCP6" scp6 IO.>>
    runCheck c "SCP7(1)" scp7₁ IO.>>
    runCheck c "SCP7(2)" scp7₂ IO.>>
    runCheck c "SCP8" scp8 IO.>>
    runCheck c "SCP9" scp9 IO.>>
    runCheck c "SCP10" scp10 IO.>>
    runCheck c "SCP11" scp11 IO.>>
    runCheck c "SCP12" scp12 IO.>>
    runCheck c "SCP13" scp13 IO.>>
    runCheck c "SCP14" scp14 IO.>>
    runCheck c "SCP15" scp15 IO.>>
    runCheck c "SCP16" scp16 IO.>>
    runCheck c "SCP17" scp17 IO.>>
    runCheck c "SCP19" scp19 IO.>>
    Aeres.IO.getCurrentTime IO.>>= λ now →
    Aeres.IO.putStrLnErr (FFI.showTime now) IO.>>= λ _ →
    case Time.fromFFI now of λ where
      nothing →
        Aeres.IO.putStrLnErr "SCP18: failed to read time from system" IO.>>
        Aeres.IO.exitFailure
      (just (bs , t)) →
        -- Aeres.IO.putStrLnErr ("SCP18: system time: " String.++ (show t)) IO.>>
        runCheck c "SCP18" (λ c₁ → scp18 c₁ t) IO.>>
        IO.putStrLn (showOutput (certOutput c)) IO.>>
        runChecks' (n + 1) tail

  runCertChecks : ∀ {@0 bs} → (cert : Chain bs) → _
  runCertChecks nil = Aeres.IO.putStrLnErr "Error: empty chain" 
  runCertChecks (cons x) =
    runChecks' 1 (cons x) IO.>>
    runChainCheck (cons x) "CCP2" ccp2 IO.>>
    runChainCheck (cons x) "CCP3" ccp3 IO.>>
    runChainCheck (cons x) "CCP4" ccp3 IO.>>
    runChainCheck (cons x) "CCP5" ccp5 IO.>>
    runChainCheck (cons x) "CCP6" ccp6 IO.>>
    runChainCheck (cons x) "CCP10" ccp10 IO.>>
    Aeres.IO.exitSuccess
