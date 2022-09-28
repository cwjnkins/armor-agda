{-# OPTIONS --subtyping --guardedness --sized-types #-}

open import Aeres.Binary
open import Aeres.Data.X509
open import Aeres.Data.X509.Decidable.Chain
open import Aeres.Data.X509.Semantic.Cert
open import Aeres.Data.X509.Semantic.Chain
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.IList
open import Aeres.Grammar.Parser
import      Aeres.IO
open import Aeres.Foreign.ByteString
  hiding (foldl)
open import Aeres.Prelude
import      Data.Nat.Properties as Nat
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
  case runParser parseChain (toUInt8 bs) of λ where
    (mkLogged _ (yes _)) → Aeres.IO.exitSuccess
    (mkLogged log (no _)) →
      Aeres.IO.putStrLnErr (foldl String._++_ "" log) IO.>>
      Aeres.IO.exitFailure

  where
  runCheck : ∀ {@0 bs} → X509.Chain bs → String
             → {P : ∀ {@0 bs} → X509.Cert bs → Set}
             → (∀ {@0 bs} → (c : X509.Cert bs) → Dec (P c))
             → IO.IO ⊤
  runCheck c m d
    with IList.all? d (fstₚ c)
  ... | no ¬p =
    Aeres.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Aeres.IO.exitFailure
  ... | yes p = IO.return tt

  runChainCheck : ∀ {@0 bs} → X509.Chain bs → String
                  → {P : ∀ {@0 bs} → X509.Chain bs → Set}
                  → (∀ {@0 bs} → (c : X509.Chain bs) → Dec (P c))
                  → IO.IO ⊤
  runChainCheck c m d
    with d c
  ... | no ¬p =
    Aeres.IO.putStrLnErr (m String.++ ": failed") IO.>>
    Aeres.IO.exitFailure
  ... | yes p = IO.return tt

  runCertChecks : ∀ {@0 bs} → X509.Chain bs → IO.Main
  runCertChecks c = IO.run $
    runCheck c "SCP1" scp1 IO.>>
    runCheck c "SCP2" scp2 IO.>>
    runCheck c "SCP3" scp3 IO.>>
    runCheck c "SCP4" scp4 IO.>>
    runCheck c "SCP5" scp5 IO.>>
    runCheck c "SCP6" scp6 IO.>>
    runCheck c "SCP7(1)" scp7₁ IO.>>
    runCheck c "SCP7(2)" scp7₂ IO.>>
    runCheck c "SP8" scp8 IO.>>
    runCheck c "SP9" scp9 IO.>>
    runCheck c "SP10" scp10 IO.>>
    runCheck c "SP11" scp11 IO.>>
    runCheck c "SP12" scp12 IO.>>
    runCheck c "SP13" scp13 IO.>>
    runCheck c "SP14" scp14 IO.>>
    runCheck c "SP15" scp15 IO.>>
    runCheck c "SP16" scp16 IO.>>
    runCheck c "SP17" scp17 IO.>>
    Aeres.IO.getCurrentTime IO.>>= λ now →
    case Time.fromFFI now of λ where
      nothing →
        Aeres.IO.putStrLnErr "SCP18: failed to read time from system" IO.>>
        Aeres.IO.exitFailure
      (just (bs , t)) →
        runCheck c "SCP18" (λ c₁ → scp18 c₁ t) IO.>>
        runChainCheck c "CCP2" ccp2 IO.>>
        runChainCheck c "CCP5" ccp5 IO.>>
        runChainCheck c "CCP6" ccp6 IO.>>
        IO.return (Level.lift tt)
    where
    open ≡-Reasoning
--    runCheck c "SP18" scp18 IO.>>
--    Aeres.IO.exitSuccess
