{-# OPTIONS --subtyping --inversion-max-depth=1000 #-}

open import Aeres.Binary
open import Aeres.Data.UTF8.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Option
import      Aeres.Grammar.Sum
open import Aeres.Prelude

module Aeres.Data.X509 where

open Base256
open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.IList       UInt8
open Aeres.Grammar.Option      UInt8
open Aeres.Grammar.Sum         UInt8

open import Aeres.Data.X690-DER             public
open import Aeres.Data.X509.Cert            public
open import Aeres.Data.X509.DirectoryString public
open import Aeres.Data.X509.DisplayText     public
open import Aeres.Data.X509.Extension       public
import      Aeres.Data.X509.Extension.TCB.OIDs as OIDs
open import Aeres.Data.X509.GeneralName     public
open import Aeres.Data.X509.IA5String       public
open import Aeres.Data.X509.PublicKey       public
open import Aeres.Data.X509.RDN             public
open import Aeres.Data.X509.SignAlg         public
open import Aeres.Data.X509.Strings         public
open import Aeres.Data.X509.TBSCert         public
open import Aeres.Data.X509.Validity        public

------------------------------X.509-----------------------------------------------------------

module X509 where

  -- module SOID where
  --   -- NOTE: These are proven to be OIDs after the fact (see Aeres.Data.X509.Decidable.OID)
  --   Md5Rsa : List UInt8
  --   Md5Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 4 ]

  --   Sha1Rsa : List UInt8
  --   Sha1Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 5 ]

  --   RsaPss : List UInt8
  --   RsaPss =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 10 ]

  --   Sha256Rsa : List UInt8
  --   Sha256Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 11 ]

  --   Sha384Rsa : List UInt8
  --   Sha384Rsa =  Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 12 ]

  --   Sha512Rsa : List UInt8
  --   Sha512Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 13 ]

  --   Sha224Rsa : List UInt8
  --   Sha224Rsa = Tag.ObjectIdentifier ∷ # 9 ∷ # 42 ∷ # 134 ∷ # 72 ∷ # 134 ∷ # 247 ∷ # 13 ∷ # 1 ∷ # 1 ∷ [ # 14 ]

  ExpNull : List UInt8
  ExpNull = # 5 ∷ [ # 0 ]


