open import Aeres.Binary
open import Aeres.Data.Base64
open import Aeres.Data.PEM.CertBoundary.TCB
open import Aeres.Data.PEM.CertText.TCB
open import Aeres.Data.PEM.CertText.FinalLine.TCB
open import Aeres.Data.PEM.CertText.FullLine.TCB
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
import      Aeres.Grammar.Parallel
open import Aeres.Prelude

module Aeres.Data.PEM.TCB where

open Aeres.Grammar.Definitions Char
open Aeres.Grammar.IList       Char
open Aeres.Grammar.Parallel    Char

record Cert (@0 bs : List Char) : Set where
  constructor mkCert
  field
    @0 {h b f} : List Char
    header : CertHeader h
    body   : CertText   b
    footer : CertFooter f
    @0 bs≡ : bs ≡ h ++ b ++ f

CertList = IList Cert

extractCert : ∀ {@0 bs} → Cert bs → List UInt8
extractCert (mkCert _ (mkCertText body final _) _ _) =
  eb body ++ ef final
  where
  eb : ∀ {@0 bs} → IList CertFullLine bs → List UInt8
  eb nil = []
  eb (cons (mkIListCons (mkCertFullLine (mk×ₚ line (─ len≡)) _ _) tail₁ _)) =
    decodeStr (mk64Str line (subst (λ x → x % 4 ≡ 0) (sym len≡) refl) (pad0 refl) refl) ++ eb tail₁

  ef : ∀ {@0 bs} → CertFinalLine bs → List UInt8
  ef (mkCertFinalLine line lineLen _ _) = decodeStr line

extractCerts : ∀ {@0 bs} → CertList bs → List UInt8
extractCerts nil = []
extractCerts (consIList c rest refl) =
  extractCert c ++ extractCerts rest


----------------------------------------
-- charToNat : Char → ℕ
-- charToNat c = Char.toNat c - Char.toNat '0'

-- stringToNat : List Char → ℕ
-- stringToNat [] = 0
-- stringToNat (c ∷ cs) = charToNat c + 10 * stringToNat cs

-- record CertListWithRootStore (@0 bs : List Char) : Set where
--   constructor mkCertListWithRootStore
--   field
--     @0 {cl n rl} : List Char
--     certs : CertList cl
--     rootcerts : CertList rl
--     @0 bs≡ : bs ≡ cl ++ n ++ rl
--     @0 length≡ : stringToNat n ≡ lengthIList certs
