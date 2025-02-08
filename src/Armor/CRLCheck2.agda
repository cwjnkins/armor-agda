{-# OPTIONS --guardedness --sized-types #-}

open import Armor.Binary
import      Armor.Data.Base64 as Base64
import      Armor.Data.PEM as PEM
open import Armor.Data.X509
open import Armor.Data.X509.Cert as Cert
open import Armor.Data.X509.Semantic.Chain.Builder
open import Armor.Data.X509.Semantic.Chain.TCB
open import Armor.Data.X509.Semantic.Cert.R18.TCB
open import Armor.Data.X509.Semantic.Cert
open import Armor.Data.X509.Semantic.Chain
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

module Armor.CRLCheck2 where

open Armor.Grammar.Definitions UInt8
open IList                     UInt8
  hiding (toList)

usage : String
usage = "usage: 'aeres CERTCHAIN TRUSTEDSTORE"

parseCerts : (fileName : String) (contents : List Char) → IO.IO (Exists─ _ (Success UInt8 Cert.CertList))
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
      case runParser Cert.parseCertList (PEM.extractCerts chain) of λ where
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

parseCrls : (fileName : String) (contents : List UInt8) → IO.IO (Exists─ _ (Success UInt8 CRL.CRLList))
parseCrls fn contents =
  case runParser CRL.parseCRLList contents of λ where
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
      IO.>> ((case runParser CRL.parseCertList suf of λ where
        (mkLogged log₃ (yes _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): parse remainder success (SHOULD NOT HAPPEN)")
          IO.>> Armor.IO.exitFailure
        (mkLogged log₃ (no _)) →
          Armor.IO.putStrLnErr (fn String.++ " (decoded): "
            String.++ show (map toℕ (take 10 suf))
            String.++ foldl String._++_ "" log₃)
          IO.>> Armor.IO.exitFailure))
    (mkLogged log₂ (yes schain)) → IO.return (_ , schain)

main : IO.Main
main = IO.run $
  Armor.IO.getArgs IO.>>= λ args →
  case
    processCmdArgs args (record { certname = nothing ; rootname = nothing ; crlname = nothing ; purpose = nothing })
  of λ where
    (inj₁ msg) →
      Armor.IO.putStrLnErr ("-- " String.++ msg)
      IO.>> Armor.IO.exitFailure
    (inj₂ cmd) →
      readPEMCert (CmdArg.certname cmd)
      IO.>>= λ cert─ → case (CmdArg.rootname cmd) of λ where
        nothing → runCertChecksLeaf (CmdArg.purpose cmd) (IList.toList _ (proj₂ cert─))
        (just rootName) →
          readPEMCert rootName
          IO.>>= λ root─ → case (CmdArg.crlname cmd) of λ where
            nothing → runCertChecks (CmdArg.purpose cmd) nothing
                        (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
            (just crlName) →
              readDERCRL crlName
              IO.>>= λ crl─ → runCertChecks (CmdArg.purpose cmd) (just (IList.toList _ (proj₂ crl─)))
                                (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
  where
  record CmdArgTmp : Set where
    pattern
    field
      certname rootname crlname : Maybe String
      purpose : Maybe KeyPurpose

  record CmdArg : Set where
    field
      certname : String
      rootname : Maybe String
      crlname : Maybe String
      purpose : Maybe KeyPurpose

  processCmdArgs : List String → CmdArgTmp → String ⊎ CmdArg
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
      (no ¬purp∈) → inj₁ ("unrecognized purpose: " String.++ purp)
      (yes purp∈) → inj₂ (proj₂ (lookup purpMap (Any.index purp∈)))
  processCmdArgs (certName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName })
  processCmdArgs (certName ∷ rootName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; rootname = just rootName })
  processCmdArgs (certName ∷ rootName ∷ crlName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; rootname = just rootName ; crlname = just crlName})
  processCmdArgs [] record { certname = just certName ; rootname = rootName ; crlname = crlName ; purpose = purpose } =
    inj₂ (record { certname = certName ; rootname = rootName ; crlname = crlName ; purpose = purpose })
  processCmdArgs [] cmd = inj₁ "not enough arguments"
  processCmdArgs args _ = inj₁ "unrecognized arguments"

  readPEMCert : (filename : String) → IO.IO (Exists─ _ Cert.CertList)
  readPEMCert filename =
    IO.readFiniteFile filename
    IO.>>= (parseCerts filename ∘ String.toList)
    IO.>>= λ certS → let (_ , success pre r r≡ certs suf ps≡) = certS in
    IO.return (_ , certs)

  readDERCRL : (filename : String) → IO.IO (Exists─ _ CRL.CRLList)
  readDERCRL filename =
    Armor.IO.openFile filename Armor.IO.Primitive.readMode
    IO.>>= Armor.IO.hGetByteStringContents
    IO.>>= λ contents → let bs = Armor.Foreign.ByteString.toUInt8 contents in
    parseCrls filename bs
    IO.>>= λ crlS → let (_ , success pre r r≡ crls suf ps≡) = crlS in
    IO.return (_ , crls)

  record CertOutput : Set where
    field
      sigAlgOID  : List UInt8
      tbsBytes   : List UInt8
      pkBytes    : List UInt8
      sigBytes   : List UInt8
      ekuOIDBytes : List (List UInt8)

  record CRLOutput : Set where
    field
      sigAlgOID  : List UInt8
      tbsBytes   : List UInt8
      sigBytes   : List UInt8

  certOutput : ∀ {@0 bs} → Cert bs → CertOutput
  CertOutput.sigAlgOID (certOutput x) = SignAlg.getOIDBS ∘ Cert.getTBSCertSignAlg $ x
  CertOutput.tbsBytes  (certOutput x) = Cert.getTBSBytes x
  CertOutput.pkBytes   (certOutput x) = Cert.getPublicKeyBytes x
  CertOutput.sigBytes  (certOutput x) = Cert.getSignatureValueBytes x
  CertOutput.ekuOIDBytes (certOutput x) = Cert.getEKUOIDList x (Cert.getEKU x)

  crlOutput : ∀ {@0 bs} → CRL.CertList bs → CRLOutput
  CRLOutput.sigAlgOID (crlOutput x) = SignAlg.getOIDBS ∘ CRL.CertList.CertList.getCertSignAlg $ x
  CRLOutput.tbsBytes  (crlOutput x) =  CRL.CertList.CertList.getTBSBytes x
  CRLOutput.sigBytes  (crlOutput x) = CRL.CertList.CertList.getSignatureValueBytes x

  showOutputCert : CertOutput → String
  showOutputCert o =
    "*******Output Certificate Start*******" String.++ "\n"
    String.++ (showBytes tbsBytes)  String.++ "\n"
    String.++ (showBytes sigBytes)  String.++ "\n"
    String.++ (showBytes pkBytes)   String.++ "\n"
    String.++ (showBytes sigAlgOID) String.++ "\n"
    String.++ (showListBytes ekuOIDBytes) String.++ "\n"
    String.++ "*******Output Certificate End*******"
    where
    open CertOutput o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

    showListBytes : List (List UInt8) → String
    showListBytes [] = ""
    showListBytes (x ∷ x₁) = (showBytes x) String.++ " @@ " String.++ (showListBytes x₁)

  showOutputCRL : CRLOutput → String
  showOutputCRL o =
    "*******Output CRL Start*******" String.++ "\n"
    String.++ (showBytes tbsBytes)  String.++ "\n"
    String.++ (showBytes sigBytes)  String.++ "\n"
    String.++ (showBytes sigAlgOID) String.++ "\n"
    String.++ "*******Output CRL End*******"
    where
    open CRLOutput o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs


  crlStsPrinter : Status → String
  crlStsPrinter record { sts = REVOKED ; rsn = (just allReasons) } = "REVOKED -- allReasons"
  crlStsPrinter record { sts = REVOKED ; rsn = (just unspecified) } = "REVOKED -- unspecified"
  crlStsPrinter record { sts = REVOKED ; rsn = (just keyCompromise) } = "REVOKED -- keyCompromise"
  crlStsPrinter record { sts = REVOKED ; rsn = (just cACompromise) } = "REVOKED -- cACompromise"
  crlStsPrinter record { sts = REVOKED ; rsn = (just affiliationChanged) } = "REVOKED -- affiliationChanged"
  crlStsPrinter record { sts = REVOKED ; rsn = (just superseded) } = "REVOKED -- superseded"
  crlStsPrinter record { sts = REVOKED ; rsn = (just cessationOfOperation) } = "REVOKED -- cessationOfOperation"
  crlStsPrinter record { sts = REVOKED ; rsn = (just certificateHold) } = "REVOKED -- certificateHold"
  crlStsPrinter record { sts = REVOKED ; rsn = (just removeFromCRL) } = "REVOKED -- removeFromCRL"
  crlStsPrinter record { sts = REVOKED ; rsn = (just privilegeWithdrawn) } = "REVOKED -- privilegeWithdrawn"
  crlStsPrinter record { sts = REVOKED ; rsn = (just aACompromise) } = "REVOKED -- aACompromise"
  crlStsPrinter record { sts = REVOKED ; rsn = nothing } = "REVOKED"
  crlStsPrinter record { sts = UNREVOKED ; rsn = _ } = "UNREVOKED"

  chainPrinter : List (Exists─ _ Cert) → _
  chainPrinter [] = IO.putStrLn ""
  chainPrinter (c ∷ rest) = IO.putStrLn (showOutputCert (certOutput (proj₂ c))) IO.>>
                            chainPrinter rest

  checkResult : List CRLStatus → IO.IO Bool
  checkResult [] = IO.return true
  checkResult (mkCRLStatus crl s@(record { sts = REVOKED ; rsn = rsn }) ∷ rest) =
    Armor.IO.putStrLnErr ("CRL Revocation Status: " String.++ (crlStsPrinter s)) IO.>>
    IO.return false
  checkResult (mkCRLStatus crl record { sts = UNREVOKED ; rsn = rsn } ∷ rest) = checkResult rest
   
  crlPrinter : List CRLStatus → _
  crlPrinter [] = IO.putStrLn ""
  crlPrinter (mkCRLStatus crl record { sts = sts ; rsn = rsn } ∷ rest) =
                         IO.putStrLn (showOutputCRL (crlOutput (crl))) IO.>>
                         crlPrinter rest

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
    Armor.IO.putStrLnErr ("=== Now Checking Certificate " String.++ (showℕ n)) IO.>>
     runCheck cert "R1" r1 IO.>>
     runCheck cert "R2" r2 IO.>>
     runCheck cert "R3" r3 IO.>>
     runCheck cert "R4" r4 IO.>>
     runCheck cert "R5" r5 IO.>>
     runCheck cert "R6" r6 IO.>>
     runCheck cert "R8" r8 IO.>>
     runCheck cert "R9" r9 IO.>>
     runCheck cert "R10" r10 IO.>>
     runCheck cert "R12" r12 IO.>>
     runCheck cert "R13" r13 IO.>>
     runCheck cert "R15" r15 IO.>>
     (if ⌊ n ≟ 1 ⌋ then (runCheck cert "R18" (r18 kp)) else (IO.return tt)) IO.>>
     Armor.IO.getCurrentTime IO.>>= λ now →
     case GeneralizedTime.fromForeignUTC now of λ where
       (no ¬p) →
         Armor.IO.putStrLnErr "R17: failed to read time from system" IO.>>
         Armor.IO.exitFailure
       (yes p) →
         runCheck cert "R17" (λ c₁ → r17 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl)))

  runChecks' :  ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → (issuee : Cert bs) → ℕ → Chain trustedRoot candidates issuee  → IO.IO ⊤
  runChecks' kp issuee n (root (trustedCA , snd)) =
    runSingleCertChecks kp issuee n IO.>>
    runSingleCertChecks kp (proj₂ trustedCA) (n + 1)
  runChecks' kp issuee n (link issuer isIn chain) =
    runSingleCertChecks kp issuee n IO.>>
    runChecks' kp issuer (n + 1) chain

  -- runCRLCheck : ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
  --   → (issuee : Cert bs) → Chain trustedRoot candidates issuee → List (Exists─ _ CRL.CertList)
  --   → {P : ∀ {@0 bs} → (i : Cert bs) → Chain trustedRoot candidates i → List (Exists─ _ CRL.CertList) → Set}
  --   → (∀ {@0 bs} → (j : Cert bs) → (chain : Chain trustedRoot candidates j) → (crl : List (Exists─ _ CRL.CertList)) → Dec (P j chain crl))
  --   → IO.IO ⊤
  -- runCRLCheck m issuee chain crl d
  --   with d issuee chain crl
  -- ... | no ¬p =
  --   Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
  --   Armor.IO.exitFailure
  -- ... | yes p =
  --   Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
  --   IO.return tt

  runCRLCheck : ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
    → (issuee : Cert bs) → Chain trustedRoot candidates issuee → List (Exists─ _ CRL.CertList)
    → IO.IO ⊤
  runCRLCheck m issuee chain crl =
    case CRLCheckChain issuee chain crl of λ where
      (just res) →
        checkResult res IO.>>= λ where
          false → IO.return tt
          true → crlPrinter res IO.>>
                 IO.return tt
      nothing → Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
                Armor.IO.exitFailure


  semChecks : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → Maybe (List (Exists─ _ CRL.CertList)) → (issuee : Cert bs)
    → Chain trustedRoot candidates issuee → IO.IO Bool
  semChecks kp nothing issuee chain =
    runChecks' kp issuee 1 chain IO.>>
    Armor.IO.putStrLnErr ("=== Now Checking Chain ") IO.>>
    runChainCheck "R19" issuee chain r19 IO.>>
    runChainCheck "R20" issuee chain r20 IO.>>
    runChainCheck "R22" issuee chain r22 IO.>>
    runChainCheck "R23" issuee chain r23 IO.>>
    runChainCheck "R27" issuee chain r27 IO.>>
    chainPrinter (toList chain) IO.>>
    IO.return true
  semChecks kp (just crl) issuee chain =
    runChecks' kp issuee 1 chain IO.>>
    Armor.IO.putStrLnErr ("=== Now Checking Chain ") IO.>>
    runChainCheck "R19" issuee chain r19 IO.>>
    runChainCheck "R20" issuee chain r20 IO.>>
    runChainCheck "R22" issuee chain r22 IO.>>
    runChainCheck "R23" issuee chain r23 IO.>>
    runChainCheck "R27" issuee chain r27 IO.>>
    runCRLCheck "CRL Validation" issuee chain crl IO.>>
    chainPrinter (toList chain) IO.>>
    IO.return true


  runCertChecks : Maybe KeyPurpose → Maybe (List (Exists─ _ CRL.CertList)) → (trustedRoot candidates : List (Exists─ _ Cert)) → _
  runCertChecks kp crl trustedRoot [] = Armor.IO.putStrLnErr "Error: no candidate certificates"
  runCertChecks kp crl trustedRoot ((─ _ , end) ∷ restCerts) =
    helper kp crl end (buildChains trustedRoot (removeCertFromCerts end restCerts) end)
    where
    helper : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} → Maybe KeyPurpose
                                    → Maybe (List (Exists─ _ CRL.CertList)) → (issuee : Cert bs)
                                    → List (Chain trustedRoot candidates issuee) → _
    helper kp crl issuee [] = Armor.IO.putStrLnErr "Error: no valid chain found" 
    helper kp crl issuee (chain ∷ otherChains) =
      semChecks kp crl issuee chain IO.>>= λ where
        false →  helper kp crl issuee otherChains
        true → Armor.IO.exitSuccess

  runCertChecksLeaf : Maybe KeyPurpose → (certs : List (Exists─ _ Cert)) → _
  runCertChecksLeaf kp [] = Armor.IO.putStrLnErr "Error: no parsed leaf certificate"
  runCertChecksLeaf kp (leaf ∷ rest) =
    runSingleCertChecks kp (proj₂ leaf) 1 IO.>>
    Armor.IO.exitSuccess
