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
        (just rootName) →
          readPEMCert rootName
          IO.>>= λ root─ → case (CmdArg.crlname cmd) of λ where
            nothing → runCertChecks (CmdArg.purpose cmd) nothing
                        (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
            (just crlName) →
              readDERCRL crlName
              IO.>>= λ crl─ → runCertChecks (CmdArg.purpose cmd) (just (IList.toList _ (proj₂ crl─)))
                                (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
        nothing → case (CmdArg.crlname cmd) of λ where
          nothing → runCertChecksLeaf (CmdArg.purpose cmd) (IList.toList _ (proj₂ cert─)) nothing
          (just crlName) →
            readDERCRL crlName
            IO.>>= λ crl─ → runCertChecksLeaf (CmdArg.purpose cmd) (IList.toList _ (proj₂ cert─)) (just (IList.toList _ (proj₂ crl─)))

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
  processCmdArgs (certName ∷ "--trust_store" ∷ rootName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; rootname = just rootName })
  processCmdArgs (certName ∷ "--crl" ∷ crlName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; crlname = just crlName})
  processCmdArgs (certName ∷ "--trust_store" ∷ rootName ∷ "--crl" ∷ crlName ∷ []) cmd = processCmdArgs [] (record cmd { certname = just certName ; rootname = just rootName ; crlname = just crlName})
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
    -- String.++ (showBytes tbsBytes)  String.++ "\n"
    String.++ (showBytes sigBytes)  String.++ "\n"
    String.++ (showBytes sigAlgOID) String.++ "\n"
    String.++ "*******Output CRL End*******"
    where
    open CRLOutput o
    showBytes : List UInt8 → String
    showBytes xs = foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs

  printRm : List RevocationReason → String
  printRm [] = ""
  printRm (allReasons ∷ x₁) = "allReasons " String.++ printRm x₁
  printRm (unspecified ∷ x₁) = "unspecified " String.++ printRm x₁
  printRm (keyCompromise ∷ x₁) = "keyCompromise " String.++ printRm x₁
  printRm (cACompromise ∷ x₁) = "cACompromise " String.++ printRm x₁
  printRm (affiliationChanged ∷ x₁) = "affiliationChanged " String.++ printRm x₁
  printRm (superseded ∷ x₁) = "superseded " String.++ printRm x₁
  printRm (cessationOfOperation ∷ x₁) = "cessationOfOperation " String.++ printRm x₁
  printRm (certificateHold ∷ x₁) = "certificateHold " String.++ printRm x₁
  printRm (removeFromCRL ∷ x₁) = "removeFromCRL " String.++ printRm x₁
  printRm (privilegeWithdrawn ∷ x₁) = "privilegeWithdrawn " String.++ printRm x₁
  printRm (aACompromise ∷ x₁) = "aACompromise " String.++ printRm x₁


  crlStsPrinter : State → String
  crlStsPrinter (validState (REVOKED reasonMask allReasons)) = "REVOKED -- allReasons "  String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask unspecified)) = "REVOKED -- unspecified " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask keyCompromise)) = "REVOKED -- keyCompromise " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask cACompromise)) = "REVOKED -- cACompromise " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask affiliationChanged)) = "REVOKED -- affiliationChanged " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask superseded)) =  "REVOKED -- superseded " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask cessationOfOperation)) = "REVOKED -- cessationOfOperation " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask certificateHold)) = "REVOKED -- certificateHold " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask removeFromCRL)) = "REVOKED -- removeFromCRL " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask privilegeWithdrawn)) = "REVOKED -- privilegeWithdrawn " String.++ printRm reasonMask
  crlStsPrinter (validState (REVOKED reasonMask aACompromise)) = "REVOKED -- aACompromise " String.++ printRm reasonMask
  crlStsPrinter (validState (UNREVOKED reasonMask)) = "UNREVOKED " String.++ printRm reasonMask
  crlStsPrinter undeterminedState = "UNDETERMINED"

  chainPrinter : List (Exists─ _ Cert) → _
  chainPrinter [] = IO.putStrLn ""
  chainPrinter (c ∷ rest) = IO.putStrLn (showOutputCert (certOutput (proj₂ c))) IO.>>
                            chainPrinter rest
   
  crllPrinter : List (Exists─ _ CRL.CertList) → _
  crllPrinter [] = IO.putStrLn ""
  crllPrinter (c ∷ rest) = IO.putStrLn (showOutputCRL (crlOutput (proj₂ c))) IO.>>
                           crllPrinter rest

  statePrinter : List State → _
  statePrinter [] = IO.putStrLn ""
  statePrinter (c ∷ rest) = IO.putStrLn (crlStsPrinter c) IO.>>
                            statePrinter rest

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

  runCRLCheckSingle :  ∀ {@0 bs} → String
                           → (issuee : Cert bs)
                           → List (Exists─ _ CRL.CertList)
                           → IO.IO ⊤
  runCRLCheckSingle m issuee [] = Armor.IO.putStrLnErr "Error: no crl given" IO.>>
                                  Armor.IO.exitFailure
  runCRLCheckSingle m issuee (crl ∷ crls) =
    case verifiedCertStateCRLs issuee crl crls initState  of λ where
      (crll , st@(validState (REVOKED reasonMask reason)) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                                                                  Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
                                                                  crllPrinter [ crll ] IO.>>
                                                                  IO.return tt
      (crll , st@(validState (UNREVOKED reasonMask)) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                                                             Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
                                                             crllPrinter [ crll ] IO.>>
                                                             IO.return tt
      (crll , st@(undeterminedState) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                                             Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
                                             crllPrinter [ crll ] IO.>>
                                             Armor.IO.exitFailure
                                    
  runSingleCertChecks : ∀ {@0 bs} → Maybe KeyPurpose → Cert bs → Maybe (List (Exists─ _ CRL.CertList)) → ℕ → _
  runSingleCertChecks kp cert nothing n =
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
  runSingleCertChecks kp cert (just crl) n =
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
     runCRLCheckSingle "CRL Validation" cert crl IO.>>
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
    runSingleCertChecks kp issuee nothing n IO.>>
    runSingleCertChecks kp (proj₂ trustedCA) nothing (n + 1)
  runChecks' kp issuee n (link issuer isIn chain) =
    runSingleCertChecks kp issuee nothing n IO.>>
    runChecks' kp issuer (n + 1) chain


  runCRLCheckChain :  ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
                           → (issuee : Cert bs) → Chain trustedRoot candidates issuee
                           → List (Exists─ _ CRL.CertList)
                           → IO.IO ⊤
  runCRLCheckChain m issuee chain [] = Armor.IO.putStrLnErr "Error: no crl given" IO.>>
                                       Armor.IO.exitFailure
  runCRLCheckChain m issuee chain (crl ∷ crls) =
    case (toList chain) of λ where
      [] → Armor.IO.putStrLnErr "Error: no cert given" IO.>>
           Armor.IO.exitFailure
      (cert ∷ certs) →
        case verifiedChainStateCRLs crl crls cert certs initState of λ where
          (crll , states , pf) →  
                                  statePrinter states IO.>>
                                  crllPrinter crll IO.>>
                                  IO.return tt
          -- (crll , st@(validState (REVOKED reasonMask reason)) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
          --                                                             Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
          --                                                             IO.return tt
          -- (crll , st@(validState (UNREVOKED reasonMask)) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
          --                                                        Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
          --                                                        IO.return tt
          -- (crll , st@(undeterminedState) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
          --                                        Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
          --                                        Armor.IO.exitFailure 
                                    


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
    runCRLCheckChain "CRL Validation" issuee chain crl IO.>>
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

  runCertChecksLeaf : Maybe KeyPurpose → (certs : List (Exists─ _ Cert)) → Maybe (List (Exists─ _ CRL.CertList)) → _
  runCertChecksLeaf kp [] crl = Armor.IO.putStrLnErr "Error: no parsed leaf certificate"
  runCertChecksLeaf kp (leaf ∷ rest)  crl =
    runSingleCertChecks kp (proj₂ leaf) crl 1 IO.>>
    Armor.IO.exitSuccess
