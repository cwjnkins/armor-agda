{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
-- open import Armor.Data.X509.ChainBuilder.Exec
open import Armor.Data.X509.Semantic.Chain.Builder
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Data.X509.Semantic.Cert.R18.TCB
open import Armor.Data.X509.Semantic.Cert
open import Armor.Data.X509.Semantic.Chain
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

module Armor.Main where

open Armor.Grammar.Definitions UInt8
open IList                     UInt8
  hiding (toList)

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
      Armor.IO.putStrLnErr
        (fn String.++ " (decoded): failed to parse bytestring as X.509" String.++ "\n"
         String.++ (foldl String._++_ "-- " log₂))
      IO.>> Armor.IO.exitFailure
    (mkLogged log₂ (yes (success prefix read read≡ chainX509 suf@(_ ∷ _) ps≡))) →
      Armor.IO.putStrLnErr
        (fn String.++ " (decoded): incomplete read\n"
         String.++ "-- only read "
           String.++ (showℕ (IList.lengthIList _ chainX509))
           String.++ " certificate(s), but more bytes remain\n"
         String.++ "-- attempting to parse remainder")
      IO.>> ((case runParser parseCert suf of λ where
        (mkLogged log₃ (yes _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
          IO.>> Armor.IO.exitFailure
        (mkLogged log₃ (no _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): "
            String.++ show (map toℕ (take 10 suf))
            String.++ foldl String._++_ "" log₃)
          IO.>> Armor.IO.exitFailure))
    (mkLogged log₂ (yes schain)) → IO.return (_ , schain)

parseCerts : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 CertList))
parseCerts fn input =
  case proj₁ (LogDec.runMaximalParser Char PEM.parseCertList input) of λ where
    (mkLogged log₁ (no ¬p)) →
      Armor.IO.putStrLnErr (foldl String._++_ "" log₁)
      IO.>> Armor.IO.exitFailure
    (mkLogged log₁ (yes (success prefix read read≡ chain suf@(_ ∷ _) ps≡))) →
      Armor.IO.putStrLnErr 
        (fn String.++ ": incomplete read\n"
         String.++ "-- only read " String.++ (showℕ (IList.lengthIList _ chain))
         String.++ " certificate(s), but " String.++ (showℕ (length suf)) String.++ " byte(s) remain")
      IO.>> Armor.IO.putStrLnErr "-- attempting to parse remainder"
      IO.>> (case proj₁ (LogDec.runMaximalParser Char PEM.parseCert suf) of λ where
        (mkLogged log₂ (yes _)) →
          Armor.IO.putStrLnErr "-- parse remainder success (SHOULD NOT HAPPEN!)"
          IO.>> Armor.IO.exitFailure
        (mkLogged log₂ (no  _)) →
          Armor.IO.putStrLnErr (foldl String._++_ "-- " log₂)
          IO.>> Armor.IO.exitFailure)
    (mkLogged log₁ (yes (success prefix read read≡ chain [] ps≡))) →
      case runParser parseCertList (PEM.extractCerts chain) of λ where
        (mkLogged log₂ (no  _)) →
          Armor.IO.putStrLnErr
            (fn String.++ " (decoded): failed to parse PEM as X.509" String.++ "\n"
             String.++ (foldl String._++_ "-- " log₂))
          IO.>> Armor.IO.exitFailure
        (mkLogged log₂ (yes (success prefix read read≡ chainX509 suf@(_ ∷ _) ps≡))) →
          Armor.IO.putStrLnErr
            (fn String.++ " (decoded): incomplete read\n"
             String.++ "-- only read "
               String.++ (showℕ (IList.lengthIList _ chainX509))
               String.++ " certificate(s), but more bytes remain\n"
             String.++ "-- attempting to parse remainder")
          IO.>> ((case runParser parseCert suf of λ where
            (mkLogged log₃ (yes _)) →
              Armor.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
              IO.>> Armor.IO.exitFailure
            (mkLogged log₃ (no _)) →
              Armor.IO.putStrLnErr (fn String.++ " (decoded): "
                String.++ show (map toℕ (take 10 suf))
                String.++ foldl String._++_ "" log₃)
              IO.>> Armor.IO.exitFailure))
        (mkLogged log₂ (yes schain)) → IO.return (_ , schain)

-- CertListToList : ∀ {@0 bs} → CertList bs  → List (Exists─ (List UInt8) Cert)
-- CertListToList nil = []
-- CertListToList (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t
--   where
--   helper : ∀ {@0 bs} → IList Cert bs → List (Exists─ (List UInt8) Cert)
--   helper nil = []
--   helper (cons (mkIListCons h t bs≡)) = (_ , h) ∷ helper t

main : IO.Main
main = IO.run $
  Armor.IO.getArgs IO.>>= λ args →
  case
    processCmdArgs args (record { certname = nothing ; rootname = nothing ; isDER = false ; purpose = nothing })
  of λ where
    (inj₁ msg) →
      Armor.IO.putStrLnErr ("-- " String.++ msg)
      IO.>> Armor.IO.exitFailure
    (inj₂ cmd) →
      readCert (CmdArg.isDER cmd) (CmdArg.certname cmd)
      IO.>>= λ cert─ → case (CmdArg.rootname cmd) of λ where
        nothing → runCertChecksLeaf (CmdArg.purpose cmd) (IList.toList _ (proj₂ cert─))
        (just rootName) →
          readPEM rootName
          IO.>>= λ root─ → runCertChecks (CmdArg.purpose cmd) (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
  where
  record CmdArgTmp : Set where
    pattern
    field
      certname rootname : Maybe String
      isDER : Bool -- default false
      purpose : Maybe KeyPurpose

  record CmdArg : Set where
    field
      certname : String
      rootname : Maybe String
      isDER : Bool
      purpose : Maybe KeyPurpose

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
  processCmdArgs ("--DER" ∷ args) cmd = processCmdArgs args (record cmd { isDER = true })
  processCmdArgs ("--purpose" ∷ purpose ∷ args) cmd =
    case readPurpose purpose of λ where
      (inj₁ msg) → inj₁ msg
      (inj₂ kp) → processCmdArgs args (record cmd { purpose = just kp })
    where
    purpMap : List (String × KeyPurpose)
    purpMap = ("serverAuth" , serverAuth) ∷ ("clientAuth" , clientAuth) ∷ ("codeSigning" , codeSigning)
              ∷ ("emailProtection" , emailProtection) ∷ ("timeStamping" , timeStamping) ∷ [ ("ocspSigning" , ocspSigning) ]

    readPurpose : String → String ⊎ KeyPurpose
    readPurpose purp = case purp ∈? map proj₁ purpMap of λ where
      (no ¬purp∈) → inj₁ ("Unrecognized purpose: " String.++ purp)
      (yes purp∈) → inj₂ (proj₂ (lookup purpMap (Any.index purp∈)))
  processCmdArgs (certName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName })
  processCmdArgs (certName ∷ rootName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; rootname = just rootName })
  processCmdArgs [] record { certname = just certName ; rootname = rootName ; isDER = isDER ; purpose = purpose } =
    inj₂ (record { certname = certName ; rootname = rootName ; isDER = isDER ; purpose = purpose })
  processCmdArgs [] cmd = inj₁ "not enough arguments"
  processCmdArgs args _ = inj₁ "unrecognized arguments"

  readPEM : (filename : String) → IO.IO (Exists─ _ CertList)
  readPEM filename =
    IO.readFiniteFile filename
    IO.>>= (parseCerts filename ∘ String.toList)
    IO.>>= λ certS → let (_ , success pre r r≡ certs suf ps≡) = certS in
    IO.return (_ , certs)

  readDER : (filename : String) → IO.IO (Exists─ _ CertList)
  readDER filename =
    Armor.IO.openFile filename Armor.IO.Primitive.readMode
    IO.>>= Armor.IO.hGetByteStringContents
    IO.>>= λ contents → let bs = Armor.Foreign.ByteString.toUInt8 contents in
    parseDERCerts filename bs
    IO.>>= λ certS → let (_ , success pre r r≡ certs suf ps≡) = certS in
    IO.return (_ , certs)

  readCert : (isDER : Bool) (filename : String) → IO.IO (Exists─ _ CertList)
  readCert false = readPEM
  readCert true = readDER

  record Output : Set where
    field
      sigAlgOID  : List UInt8
      tbsBytes   : List UInt8
      pkBytes    : List UInt8
      sigBytes   : List UInt8
      ekuOIDBytes : List (List UInt8)

  certOutput : ∀ {@0 bs} → Cert bs → Output
  Output.sigAlgOID (certOutput x) = SignAlg.getOIDBS ∘ Cert.getTBSCertSignAlg $ x
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
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Armor.IO.exitFailure
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return tt

  runChainCheck : ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
    → (issuee : Cert bs) → Chain trustedRoot candidates issuee
    → {P : ∀ {@0 bs} → (i : Cert bs) → Chain trustedRoot candidates i → Set}
    → (∀ {@0 bs} → (j : Cert bs) → (chain : Chain trustedRoot candidates j) → Dec (P j chain))
    → IO.IO ⊤
  runChainCheck m i c d
    with d i c
  ... | no ¬p =
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Armor.IO.exitFailure
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return tt

  runSingleCertChecks : ∀ {@0 bs} → Maybe KeyPurpose → Cert bs → ℕ → _
  runSingleCertChecks kp cert n =
    Armor.IO.putStrLnErr ("=== Checking " String.++ (showℕ n)) IO.>>
     runCheck cert "R1" r1 IO.>>
     runCheck cert "R2" r2 IO.>>
     runCheck cert "R3" r3 IO.>>
     runCheck cert "R4" r4 IO.>>
     runCheck cert "R5" r5 IO.>>
     runCheck cert "R6" r6 IO.>>
     -- runCheck cert "R7" r7 IO.>>
     runCheck cert "R8" r8 IO.>>
     runCheck cert "R9" r9 IO.>>
     runCheck cert "R10" r10 IO.>>
     -- runCheck cert "R11" r11 IO.>>
     runCheck cert "R12" r12 IO.>>
     runCheck cert "R13" r13 IO.>>
     -- runCheck cert "R14" r14 IO.>>
     runCheck cert "R15" r15 IO.>>
     -- runCheck cert "R16" r16 IO.>>
     (if ⌊ n ≟ 1 ⌋ then (runCheck cert "R18" (r18 kp)) else (IO.return tt)) IO.>>
     Armor.IO.getCurrentTime IO.>>= λ now →
     Armor.IO.putStrLnErr (FFI.showTime now) IO.>>= λ _ →
     case GeneralizedTime.fromForeignUTC now of λ where
       (no ¬p) →
         Armor.IO.putStrLnErr "R17: failed to read time from system" IO.>>
         Armor.IO.exitFailure
       (yes p) →
         runCheck cert "R17" (λ c₁ → r17 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl)))

  runChecks' :  ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → (issuee : Cert bs) → ℕ → Chain trustedRoot candidates issuee  → IO.IO ⊤
  runChecks' kp issuee n (root (trustedCA , snd)) =
    IO.putStrLn (showOutput (certOutput issuee)) IO.>>
    runSingleCertChecks kp issuee n IO.>>
    IO.putStrLn (showOutput (certOutput (proj₂ trustedCA))) IO.>>
    runSingleCertChecks kp (proj₂ trustedCA) (n + 1)
  runChecks' kp issuee n (link issuer isIn chain) =
    IO.putStrLn (showOutput (certOutput issuee)) IO.>>
    runSingleCertChecks kp issuee n IO.>>
    runChecks' kp issuer (n + 1) chain

  helper₁ : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → (issuee : Cert bs) → Chain trustedRoot candidates issuee → IO.IO Bool
  helper₁ kp issuee chain =
    runChecks' kp issuee 1 chain IO.>>
    runChainCheck "R19" issuee chain r19 IO.>>
    runChainCheck "R20" issuee chain r20 IO.>>
    -- runChainCheck "R21" issuee chain r21 IO.>>
    runChainCheck "R22" issuee chain r22 IO.>>
    runChainCheck "R23" issuee chain r23 IO.>>
    runChainCheck "R27" issuee chain r27 IO.>>
    IO.return true

  helper₂ : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} → Maybe KeyPurpose → (issuee : Cert bs)
    → List (Chain trustedRoot candidates issuee) → _
  helper₂ kp issuee [] = Armor.IO.putStrLnErr "Error: no valid chain found" 
  helper₂ kp issuee (chain ∷ otherChains) =
    helper₁ kp issuee chain IO.>>= λ where
      false →  helper₂ kp issuee otherChains
      true → Armor.IO.exitSuccess

  runCertChecks : Maybe KeyPurpose → (trustedRoot candidates : List (Exists─ _ Cert)) → _
  runCertChecks kp trustedRoot [] = Armor.IO.putStrLnErr "Error: no candidate certificates"
  runCertChecks kp trustedRoot ((─ _ , end) ∷ restCerts) =
    helper₂ kp end (buildChains trustedRoot (removeCertFromCerts end restCerts) end)
    where
    open import Armor.Data.X509.Semantic.Chain.Properties
    @0 un : (c : Chain trustedRoot (removeCertFromCerts end restCerts) end) → (-, end) ∉ trustedRoot → ChainUnique c
    un c end∉trust = chainUnique _ _ (∉removeCertFromCerts end restCerts) end∉trust c

  runCertChecksLeaf : Maybe KeyPurpose → (certs : List (Exists─ _ Cert)) → _
  runCertChecksLeaf kp [] = Armor.IO.putStrLnErr "Error: no parsed leaf certificate"
  runCertChecksLeaf kp (leaf ∷ rest) =
    -- IO.putStrLn (showOutput (certOutput (proj₂ leaf))) IO.>>
    runSingleCertChecks kp (proj₂ leaf) 1 IO.>>
    Armor.IO.exitSuccess
