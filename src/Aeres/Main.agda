{-# OPTIONS --subtyping --guardedness --sized-types #-}

open import Aeres.Binary
  hiding (module Base64)
import      Aeres.Data.Base64 as Base64
import      Aeres.Data.PEM as PEM
open import Aeres.Data.X509
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
usage = "usage: 'aeres [CERT]'"

-- str2dig : String → Maybe (List Dig)
-- str2dig xs = do
--   bs ← decToMaybe ∘ All.all? (_<? 256) ∘ map toℕ ∘ String.toList $ xs
--   return (map (λ where (n , n<256) → Fin.fromℕ< n<256) (All.toList bs))

-- TODO: bindings for returning error codes?
main : IO.Main
main = IO.run $
  Aeres.IO.getByteStringContents IO.>>= λ bs →
  let input = toChar bs in
  case proj₁ (LogDec.runMaximalParser Char PEM.parseCertList input) of λ where
    (mkLogged log (no ¬p)) →
      Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
      Aeres.IO.exitFailure
    (mkLogged log (yes (success prefix read read≡ chain suf@(_ ∷ _) ps≡))) →
      Aeres.IO.putStrLnErr
        ("Only read " String.++ (showℕ (Aeres.Grammar.IList.lengthIList _ chain))
         String.++ " certificate(s) - but more bytes remain") IO.>>
      (case proj₁ (LogDec.runMaximalParser Char PEM.parseCert suf) of λ where
        (mkLogged log (no _)) →
          Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
          Aeres.IO.exitFailure
        (mkLogged _ (yes _)) →
          Aeres.IO.putStrLnErr "aeres: THIS SHOULD NOT HAPPEN" IO.>>
          Aeres.IO.exitFailure)
    (mkLogged log (yes (success prefix read read≡ chain [] ps≡))) →
      case runParser parseChain (PEM.extractCerts chain) of λ where
       (mkLogged _ (yes (success _ r r≡ chain suf ps≡))) →
         case suf ≟ [] of λ where
           (no  _) →
             Aeres.IO.putStrLnErr
               ("Only read " String.++ (showℕ (lengthIList (fstₚ chain)))
                String.++ " certificate(s), but more bytes remain") IO.>>
             (case runParser parseCert suf of λ where
               (mkLogged log (no _)) →
                 Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
                 Aeres.IO.exitFailure
               (mkLogged _ (yes _)) →
                 Aeres.IO.putStrLnErr "aeres: THIS SHOULD NOT HAPPEN" IO.>>
                 Aeres.IO.exitFailure)
           (yes _) → runCertChecks chain
       (mkLogged log (no _)) →
         Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
         Aeres.IO.exitFailure

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

  runChecks' : ∀ {@0 bs} → ℕ → IList Cert bs → _
  runChecks' n nil = IO.return tt
  runChecks' n (consIList c tail bs≡) =
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

  runCertChecks : ∀ {@0 bs} → Chain bs → _
  runCertChecks c =
    runChecks' 1 (fstₚ c) IO.>>
    runChainCheck c "CCP2" ccp2 IO.>>
    runChainCheck c "CCP5" ccp5 IO.>>
    runChainCheck c "CCP6" ccp6 IO.>>
    Aeres.IO.exitSuccess
