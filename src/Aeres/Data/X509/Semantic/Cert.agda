{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.Semantic.Cert.Utils
-- import      Aeres.Data.X509.Semantic.Cert.SCP1 as SCP1
import      Aeres.Data.X509.Semantic.Cert.SCP2 as SCP2
import      Aeres.Data.X509.Semantic.Cert.SCP3 as SCP3
import      Aeres.Data.X509.Semantic.Cert.SCP4 as SCP4
import      Aeres.Data.X509.Semantic.Cert.SCP5 as SCP5
import      Aeres.Data.X509.Semantic.Cert.SCP6 as SCP6
import      Aeres.Data.X509.Semantic.Cert.SCP7 as SCP7
import      Aeres.Data.X509.Semantic.Cert.SCP8 as SCP8
import      Aeres.Data.X509.Semantic.Cert.SCP9 as SCP9
import      Aeres.Data.X509.Semantic.Cert.SCP10 as SCP10
import      Aeres.Data.X509.Semantic.Cert.SCP11 as SCP11
import      Aeres.Data.X509.Semantic.Cert.SCP12 as SCP12
import      Aeres.Data.X509.Semantic.Cert.SCP13 as SCP13
import      Aeres.Data.X509.Semantic.Cert.SCP14 as SCP14
import      Aeres.Data.X509.Semantic.Cert.SCP15 as SCP15
import      Aeres.Data.X509.Semantic.Cert.SCP16 as SCP16
import      Aeres.Data.X509.Semantic.Cert.SCP17 as SCP17
import      Aeres.Data.X509.Semantic.Cert.SCP18 as SCP18
import      Aeres.Data.X509.Semantic.Cert.SCP19 as SCP19
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Option
open import Aeres.Grammar.IList as IList
open import Aeres.Prelude

module Aeres.Data.X509.Semantic.Cert where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Option      UInt8

---------------------- SCP rules -----------------

-- SignatureAlgorithm field MUST contain the same algorithm identifier as
-- the Signature field in the sequence TbsCertificate.
-- open SCP1 public

-- Extension field MUST only appear if the Version is 3(2).
open SCP2 public

-- At a minimum, conforming implementations MUST recognize Version 3 certificates.
-- Generation of Version 2 certificates is not expected by implementations based on this profile.
-- note : but, version 1 and 2 certs can be present for CA certificates. So, we are checking whether
-- the version is 1, 2, or 3 (0 - 2).
open SCP3 public

-- The Serial number MUST be a positive integer assigned by the CA to each certificate.
open SCP4 public

-- The Issuer field MUST contain a non-empty distinguished name (DN).
-- TODO : fix the parser to enforce set length to minimum 1
open SCP5 public


-- If the Subject is a CA (e.g., the Basic Constraints extension, is present and the value of CA is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
open SCP6 public

-- -- Unique Identifiers fields MUST only appear if the Version is 2 or 3.
open SCP7 public


-- -- Where it appears, the PathLenConstraint field MUST be greater than or equal to zero.
open SCP8 public

-- if the Subject is a CRL issuer (e.g., the Key Usage extension, is present and the value of CRLSign is TRUE),
-- then the Subject field MUST be populated with a non-empty distinguished name.
open SCP9 public

-- When the Key Usage extension appears in a certificate, at least one of the bits MUST be set to 1.
open SCP10 public

-- If subject naming information is present only in the Subject Alternative Name extension ,
-- then the Subject name MUST be an empty sequence and the Subject Alternative Name extension MUST be critical.
-- If the subject field contains an empty sequence, then the issuing CA MUST include a
-- subjectAltName extension that is marked as critical.
open SCP11 public

-- If the Subject Alternative Name extension is present, the sequence MUST contain at least one entry.
open SCP12 public

-- If the KeyCertSign bit is asserted, then the CA bit in the Basic Constraints extension MUST also be asserted.
open SCP13 public

-- A certificate MUST NOT include more than one instance of a particular Extension.
open SCP14 public

-- A certificate-using system MUST reject the certificate if it encounters a critical Extension
-- it does not recognize or a critical Extension that contains information that it cannot process.
open SCP15 public

-- A certificate policy OID MUST NOT appear more than once in a Certificate Policies extension.
open SCP16 public

-- While each of these fields is optional, a DistributionPoint MUST NOT consist of only the Reasons field;
-- either distributionPoint or CRLIssuer MUST be present.
open SCP17 public

-- The certificate Validity period includes the current time
open SCP18 public

--- consistency of certificate purposes based on key usage bits and extended key usage OIDs
open SCP19 public
