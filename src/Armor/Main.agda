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
open import Armor.Data.X509.CRL.Semantic.Validation
open import Armor.Data.X509.CRL.Semantic.Utils
open import Armor.Data.X509.CRL.Semantic.R1
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
usage = "usage: './Main CERTCHAIN --trust_store TRUSTEDSTORE --crl CRL --purpose XYZ"

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
            nothing → runCertChecksChain (CmdArg.purpose cmd) nothing
                        (IList.toList _ (proj₂ root─)) (IList.toList _ (proj₂ cert─))
            (just crlName) →
              readDERCRL crlName
              IO.>>= λ crl─ → runCertChecksChain (CmdArg.purpose cmd) (just (IList.toList _ (proj₂ crl─)))
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
  CRLOutput.sigAlgOID (crlOutput x) = SignAlg.getOIDBS ∘ CRL.CertList.CertList.getCertListSignAlg $ x
  CRLOutput.tbsBytes  (crlOutput x) =  CRL.CertList.CertList.getTBSBytes x
  CRLOutput.sigBytes  (crlOutput x) = CRL.CertList.CertList.getSignatureValueBytes x

  showOutputCert : CertOutput → _
  showOutputCert o =
    IO.putStrLn ("*******Output Certificate Start*******") IO.>>
    showBytes tbsBytes IO.>>
    showBytes sigBytes IO.>>
    showBytes pkBytes IO.>>
    showBytes sigAlgOID IO.>>
    showListBytes ekuOIDBytes IO.>>
    IO.putStrLn ("*******Output Certificate End*******")
    where
    open CertOutput o
    showBytes : List UInt8 → _
    showBytes xs = IO.putStrLn (foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs)

    showBytes' : List UInt8 → _
    showBytes' xs = IO.putStr (foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs)

    showListBytes : List (List UInt8) → _
    showListBytes [] = IO.putStrLn ""
    showListBytes (x ∷ x₁) = showBytes' x IO.>>
                             IO.putStr " @@ " IO.>>
                             showListBytes x₁

  showOutputCRL : CRLOutput → _
  showOutputCRL o =
    IO.putStrLn ("*******Output CRL Start*******") IO.>>
    showBytes' tbsBytes IO.>>
    showBytes sigBytes IO.>>
    showBytes sigAlgOID IO.>>
    IO.putStrLn ("*******Output CRL End*******")
    where
    open CRLOutput o
    showBytes : List UInt8 → _
    showBytes xs = IO.putStrLn (foldr (λ b s → show (toℕ b) String.++ " " String.++ s) "" xs)

    showBytes' : List UInt8 → _
    showBytes' [] = IO.putStrLn ""
    showBytes' (x ∷ xs) = IO.putStr ((show (toℕ x)) String.++ " ") IO.>>
                          showBytes' xs

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
  chainPrinter (c ∷ rest) = showOutputCert (certOutput (proj₂ c)) IO.>>
                            chainPrinter rest
   
  crllPrinter : List (Exists─ _ CRL.CertList) → _
  crllPrinter [] = IO.putStrLn ""
  crllPrinter (c ∷ rest) = showOutputCRL (crlOutput (proj₂ c)) IO.>>
                           crllPrinter rest

  statePrinter : List State → _
  statePrinter [] = Armor.IO.putStrLnErr ""
  statePrinter (c ∷ rest) = Armor.IO.putStrLnErr (crlStsPrinter c) IO.>>
                            statePrinter rest

  data ChainRevocationStatus : Set where
    REVOKED   : ChainRevocationStatus
    UNREVOKED : ChainRevocationStatus
    UNDETERMINED : ChainRevocationStatus

  findRevocationState : List State → ChainRevocationStatus → ChainRevocationStatus
  findRevocationState [] prev = prev
  findRevocationState (validState (REVOKED reasonMask reason) ∷ x₁) REVOKED = REVOKED
  findRevocationState (validState (REVOKED reasonMask reason) ∷ x₁) UNREVOKED = REVOKED
  findRevocationState (validState (REVOKED reasonMask reason) ∷ x₁) UNDETERMINED = UNDETERMINED
  findRevocationState (validState (UNREVOKED reasonMask) ∷ x₁) REVOKED = REVOKED
  findRevocationState (validState (UNREVOKED reasonMask) ∷ x₁) UNREVOKED = findRevocationState x₁ UNREVOKED
  findRevocationState (validState (UNREVOKED reasonMask) ∷ x₁) UNDETERMINED = UNDETERMINED
  findRevocationState (undeterminedState ∷ x₁) prev = UNDETERMINED

  runCheck : ∀ {@0 bs} → Cert bs → String
             → {P : ∀ {@0 bs} → Cert bs → Set}
             → (∀ {@0 bs} → (c : Cert bs) → Dec (P c))
             → IO.IO Bool
  runCheck c m d
    with d c
  ... | no ¬p =
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    IO.return false
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return true

  runCheck₂ : ∀ {@0 bs} → CRL.CertList bs → String
             → {P : ∀ {@0 bs} → CRL.CertList bs → Set}
             → (∀ {@0 bs} → (c : CRL.CertList bs) → Dec (P c))
             → IO.IO Bool
  runCheck₂ c m d
    with d c
  ... | no ¬p =
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    IO.return false
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return true

  runCheck₃ : ∀ {@0 bs} →  CRL.CertList bs → ℕ → IO.IO Bool
  runCheck₃ crl n =
    Armor.IO.putStrLnErr ("=== Now Checking CRL " String.++ (showℕ n)) IO.>>
      runCheck₂ crl "CRLR1" CRLr1 IO.>>= λ where
       true → runCheck₂ crl "CRLR2" CRLr2 IO.>>= λ where
         true → runCheck₂ crl "CRLR3" CRLr3 IO.>>= λ where
           true → runCheck₂ crl "CRLR4" CRLr4 IO.>>= λ where
             true → runCheck₂ crl "CRLR5" CRLr5 IO.>>= λ where
               true → Armor.IO.getCurrentTime IO.>>= λ now →
                        case GeneralizedTime.fromForeignUTC now of λ where
                          (no ¬p) →
                            Armor.IO.putStrLnErr "CRLR6: failed to read time from system" IO.>>
                              IO.return false
                          (yes p) →
                            runCheck₂ crl "CRLR6" (λ c₁ → CRLr6 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl))) IO.>>= λ where
                              true → runCheck₂ crl "CRLR7" CRLr7 IO.>>= λ where
                                true → IO.return true
                                false → IO.return false
                              false → IO.return false
               false → IO.return false
             false → IO.return false
           false → IO.return false
         false → IO.return false
       false → IO.return false

  runCheck₄ : List (Exists─ _ CRL.CertList) → ℕ → IO.IO Bool
  runCheck₄ [] n = IO.return true
  runCheck₄ (x ∷ x₁) n =
    runCheck₃ (proj₂ x) n IO.>>= λ where
      true → runCheck₄ x₁ (n + 1)
      false → IO.return false
    
  runChainCheck : ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
    → (issuee : Cert bs) → Chain trustedRoot candidates issuee
    → {P : ∀ {@0 bs} → (i : Cert bs) → Chain trustedRoot candidates i → Set}
    → (∀ {@0 bs} → (j : Cert bs) → (chain : Chain trustedRoot candidates j) → Dec (P j chain))
    → IO.IO Bool
  runChainCheck m i c d
    with d i c
  ... | no ¬p =
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    IO.return false
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return true

  runChainCheckWithCRLs : ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → {issuee : Cert bs} → String
    → Chain trustedRoot candidates issuee
    → List (Exists─ _ CRL.CertList)
    → {P : ∀ {@0 bs} {i : Cert bs} → Chain trustedRoot candidates i → List (Exists─ _ CRL.CertList) → Set}
    → (∀ {@0 bs} {j : Cert bs} → (chain : Chain trustedRoot candidates j) → (crls : List (Exists─ _ CRL.CertList)) → Dec (P chain crls))
    → IO.IO Bool
  runChainCheckWithCRLs m chain crls d
    with d chain crls
  ... | no ¬p =
    Armor.IO.putStrLnErr (m String.++ ": failed") IO.>>
    IO.return false
  ... | yes p =
    Armor.IO.putStrLnErr (m String.++ ": passed") IO.>>
    IO.return true

  runCRLCheckSingle :  ∀ {@0 bs} → String
                           → (cert : Cert bs)
                           → List (Exists─ _ CRL.CertList)
                           → IO.IO Bool
  runCRLCheckSingle m cert [] = IO.return false
  runCRLCheckSingle m cert (crl ∷ rest) =
    case verifiedCertStateCRLs cert crl rest initState  of λ where
        (crll , st@(validState (REVOKED reasonMask reason)) , pf) →
          runCheck₃ (proj₂ crll) 1 IO.>>= λ where
            true → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                   Armor.IO.putStrLnErr (m String.++ ": REVOKED") IO.>>
                   IO.return true
            false → IO.return false
        (crll , st@(validState (UNREVOKED reasonMask)) , pf) → 
          runCheck₃ (proj₂ crll) 1 IO.>>= λ where
            true → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                   Armor.IO.putStrLnErr (m String.++ ": UNREVOKED") IO.>>
                   IO.return true
            false → IO.return false
        (crll , st@(undeterminedState) , pf) → Armor.IO.putStrLnErr (crlStsPrinter st) IO.>>
                                               Armor.IO.putStrLnErr (m String.++ ": UNDETERMINED") IO.>>
                                               IO.return false

  runSingleCertChecks : ∀ {@0 bs} → Maybe KeyPurpose → Cert bs → Maybe (List (Exists─ _ CRL.CertList)) → ℕ → IO.IO Bool
  runSingleCertChecks kp cert crl n =
    Armor.IO.putStrLnErr ("=== Now Checking Certificate " String.++ (showℕ n)) IO.>>
      runCheck cert "R1" r1 IO.>>= λ where
       true → runCheck cert "R2" r2 IO.>>= λ where
         true → runCheck cert "R3" r3 IO.>>= λ where
           true → runCheck cert "R4" r4 IO.>>= λ where
             true → runCheck cert "R5" r5 IO.>>= λ where
               true → runCheck cert "R6" r6 IO.>>= λ where
                 true → runCheck cert "R8" r8 IO.>>= λ where
                   true → runCheck cert "R9" r9 IO.>>= λ where
                     true → runCheck cert "R10" r10 IO.>>= λ where
                       true → runCheck cert "R12" r12 IO.>>= λ where
                         true → runCheck cert "R13" r13 IO.>>= λ where
                           true → runCheck cert "R15" r15 IO.>>= λ where
                             true → Armor.IO.getCurrentTime IO.>>= λ now →
                                      case GeneralizedTime.fromForeignUTC now of λ where
                                        (no ¬p) →
                                          Armor.IO.putStrLnErr "R17: failed to read time from system" IO.>>
                                          IO.return false
                                        (yes p) →
                                          runCheck cert "R17" (λ c₁ → r17 c₁ (Validity.generalized (mkTLV (Length.shortₛ (# 15)) p refl refl))) IO.>>= λ where
                                            true → case n ≟ 1  of λ where
                                                     (yes q) →
                                                       runCheck cert "R18" (r18 kp) IO.>>= λ where
                                                         true →
                                                           case crl of λ where
                                                             (just x) →
                                                               runCRLCheckSingle "CRL Validation" cert x IO.>>= λ where
                                                                 true → IO.return true
                                                                 false → IO.return false
                                                             nothing → IO.return true
                                                         false → IO.return false
                                                     (no ¬q) → IO.return true
                                            false → IO.return false
                             false → IO.return false
                           false → IO.return false
                         false → IO.return false
                       false → IO.return false
                     false → IO.return false
                   false → IO.return false
                 false → IO.return false
               false → IO.return false
             false → IO.return false
           false → IO.return false
         false → IO.return false
       false → IO.return false
         
  runChainChecks' :  ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → (issuee : Cert bs) → ℕ → Chain trustedRoot candidates issuee  → IO.IO Bool
  runChainChecks' kp issuee n (root (trustedCA , snd)) =
    runSingleCertChecks kp issuee nothing n IO.>>= λ where
      true → runSingleCertChecks kp (proj₂ trustedCA) nothing (n + 1) IO.>>= λ where
        true → IO.return true
        false → IO.return false
      false → IO.return false
  runChainChecks' kp issuee n (link issuer isIn chain) =
    runSingleCertChecks kp issuee nothing n IO.>>= λ where
      true → runChainChecks' kp issuer (n + 1) chain IO.>>= λ where
        true → IO.return true
        false → IO.return false
      false → IO.return false

  runCRLCheckChain :  ∀ {@0 bs} → {trustedRoot candidates : List (Exists─ _ Cert)} → String
                           → (cert : Cert bs) → Chain trustedRoot candidates cert
                           → List (Exists─ _ CRL.CertList)
                           → IO.IO Bool
  runCRLCheckChain m cert chain [] = Armor.IO.putStrLnErr "Error: no CRL given" IO.>>
                                     IO.return false
  runCRLCheckChain m issuee chain (crl ∷ crls) =
    case (take (length (toList chain) - 1) (toList chain)) of λ where
      [] → IO.return true
      (cert ∷ certs) →
        case verifiedChainStateCRLs crl crls cert certs initState of λ where
          (crll , states , pf) →
            case findRevocationState states UNREVOKED of λ where
              REVOKED →
                runCheck₄ crll 1 IO.>>= λ where
                  true →
                    Armor.IO.putStrLnErr ("=== Now Checking CRL Chain ") IO.>>
                    runChainCheckWithCRLs "CRLR8" chain crll CRLr8 IO.>>= λ where
                      true →
                        IO.putStrLn (m String.++ ": REVOKED") IO.>>
                        statePrinter states IO.>>
                        crllPrinter crll IO.>>
                        IO.return true
                      false → IO.return false
                  false → IO.return false
              UNREVOKED →
                runCheck₄ crll 1 IO.>>= λ where
                  true →
                    Armor.IO.putStrLnErr ("=== Now Checking CRL Chain ") IO.>>
                    runChainCheckWithCRLs "CRLR8" chain crll CRLr8 IO.>>= λ where
                      true →
                        IO.putStrLn (m String.++ ": UNREVOKED") IO.>>
                        statePrinter states IO.>>
                        crllPrinter crll IO.>>
                        IO.return true
                      false → IO.return false
                  false → IO.return false
              UNDETERMINED → IO.putStrLn (m String.++ ": UNDETERMINED") IO.>>
                             statePrinter states IO.>>
                             IO.return false

  runChainChecks : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)}
    → Maybe KeyPurpose → Maybe (List (Exists─ _ CRL.CertList)) → (issuee : Cert bs)
    → Chain trustedRoot candidates issuee → IO.IO Bool
  runChainChecks kp crl issuee chain =
      runChainChecks' kp issuee 1 chain IO.>>= λ where
        true →
          Armor.IO.putStrLnErr ("=== Now Checking Chain ") IO.>>
          runChainCheck "R19" issuee chain r19 IO.>>= λ where
          true → runChainCheck "R20" issuee chain r20 IO.>>= λ where
            true → runChainCheck "R22" issuee chain r22 IO.>>= λ where
              true → runChainCheck "R23" issuee chain r23 IO.>>= λ where
                true → runChainCheck "R27" issuee chain r27 IO.>>= λ where
                  true → case crl of λ where
                           (just x) → runCRLCheckChain "CRL Validation" issuee chain x IO.>>= λ where
                             true → chainPrinter (toList chain) IO.>>
                                    IO.return true
                             false → IO.return false
                           nothing → chainPrinter (toList chain) IO.>>
                                     IO.return true
                  false → IO.return false
                false → IO.return false
              false → IO.return false
            false → IO.return false
          false → IO.return false
        false → IO.return false

  runCertChecksChain : Maybe KeyPurpose → Maybe (List (Exists─ _ CRL.CertList)) → (trustedRoot candidates : List (Exists─ _ Cert)) → _
  runCertChecksChain kp crl trustedRoot [] = Armor.IO.putStrLnErr "Error: no candidate certificates" IO.>>
                                        Armor.IO.exitFailure
  runCertChecksChain kp crl trustedRoot ((─ _ , end) ∷ restCerts) =
    helper kp crl end (buildChains trustedRoot (removeCertFromCerts end restCerts) end) IO.>>= λ where
      true → IO.putStrLn "Chain Semantic Validation : Success" IO.>>
             Armor.IO.exitSuccess
      false → IO.putStrLn "Chain Semantic Validation : Failed" IO.>>
              Armor.IO.exitFailure
    where
    helper : ∀ {@0 bs} {trustedRoot candidates : List (Exists─ _ Cert)} → Maybe KeyPurpose
                                    → Maybe (List (Exists─ _ CRL.CertList)) → (issuee : Cert bs)
                                    → List (Chain trustedRoot candidates issuee) → IO.IO Bool
    helper kp crl issuee [] = Armor.IO.putStrLnErr "Error: no valid chain found" IO.>>
                              IO.return false
    helper kp crl issuee (chain ∷ otherChains) =
      runChainChecks kp crl issuee chain IO.>>= λ where
        false →  helper kp crl issuee otherChains
        true →
          IO.putStrLn (showℕ (length (chain ∷ otherChains))) IO.>>
          IO.return true

  runCertChecksLeaf : Maybe KeyPurpose → (certs : List (Exists─ _ Cert)) → Maybe (List (Exists─ _ CRL.CertList)) → _
  runCertChecksLeaf kp [] crl = Armor.IO.putStrLnErr "Error: no parsed leaf certificate" IO.>>
                                Armor.IO.exitFailure
  runCertChecksLeaf kp (leaf ∷ rest)  crl =
    runSingleCertChecks kp (proj₂ leaf) crl 1 IO.>>= λ where
      true → IO.putStrLn "Cert Semantic Validation : Success" IO.>>
             Armor.IO.exitSuccess
      false → IO.putStrLn "Cert Semantic Validation : Failed" IO.>>
              Armor.IO.exitFailure
