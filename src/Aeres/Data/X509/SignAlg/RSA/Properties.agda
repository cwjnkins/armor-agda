{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open import Aeres.Data.X509.AlgorithmIdentifier
import      Aeres.Data.X509.SignAlg.TCB.OIDs            as OIDs
import      Aeres.Data.X509.SignAlg.RSA.TCB             as RSA
open import Aeres.Data.X509.SignAlg.RSA.PSS.TCB         as PSS
import      Aeres.Data.X509.SignAlg.RSA.PSS.Properties  as PSS
import      Aeres.Data.X509.HashAlg.TCB                 as HashAlg
import      Aeres.Data.X509.HashAlg.Properties          as HashAlg
import      Aeres.Data.X509.HashAlg.TCB.OIDs            as OIDs
open import Aeres.Data.X690-DER.OID
open import Aeres.Data.X690-DER.OctetString.TCB
open import Aeres.Data.X690-DER.TLV
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
open import Aeres.Prelude
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.SignAlg.RSA.Properties where

open Aeres.Grammar.Definitions UInt8
open Aeres.Grammar.Properties  UInt8
open Aeres.Grammar.Sum         UInt8

module Supported where
  @0 noConfusion : ∀ {@0 bs} → (o : OIDValue bs) → {_ : False (_≋?_{A = OIDValue} o OIDs.RSA.PSS)}
                → NoConfusion (HashAlg.SHA-Like o) PSS
  noConfusion o {t} =
    TLV.noconfusionVal λ where
     {xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkAlgIDFields{bs₁}{p} o (mk×ₚ _ o≡ refl) bs≡) (mkAlgIDFields{bs₁'}{p'} o' (mk×ₚ _ o'≡ refl) bs'≡) →
       let
         @0 ++≡ : bs₁ ++ p ++ ys₁ ≡ bs₁' ++ p' ++ ys₂
         ++≡ = begin
           bs₁ ++ p ++ ys₁ ≡⟨ solve (++-monoid UInt8) ⟩
           (bs₁ ++ p) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
           xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
           xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs'≡ ⟩
           (bs₁' ++ p') ++ ys₂ ≡⟨ solve (++-monoid UInt8) ⟩
           bs₁' ++ p' ++ ys₂ ∎
  
         @0 bs₁≡ : bs₁ ≡ bs₁'
         bs₁≡ = TLV.nonnesting ++≡ o o'
  
         @0 o≋o' : _≋_{OID} o o'
         o≋o' = mk≋ bs₁≡ (OID.unambiguous _ o')
       in
       contradiction
         (trans≋ (sym≋ o≡) (trans≋ (cong≋ (λ x → -, TLV.val x) o≋o') o'≡))
         (toWitnessFalse t)
    where
    open ≡-Reasoning

  @0 unambiguous : Unambiguous RSA.Supported
  unambiguous =
    unambiguousSum{A = RSA.MD2}
      (HashAlg.SHA-Like.unambiguous OIDs.RSA.MD2)
      (unambiguousSum{A = RSA.MD5}
        (HashAlg.SHA-Like.unambiguous OIDs.RSA.MD5)
        (unambiguousSum{A = RSA.SHA1}
          (HashAlg.SHA-Like.unambiguous OIDs.RSA.SHA1)
          (unambiguousSum{A = RSA.SHA224}
            (HashAlg.SHA-Like.unambiguous OIDs.RSA.SHA224)
            (unambiguousSum{A = RSA.SHA256}
              (HashAlg.SHA-Like.unambiguous OIDs.RSA.SHA256)
              (unambiguousSum{A = RSA.SHA384}
                (HashAlg.SHA-Like.unambiguous OIDs.RSA.SHA384)
                (unambiguousSum{A = RSA.SHA512}
                  (HashAlg.SHA-Like.unambiguous OIDs.RSA.SHA512)
                  PSS.unambiguous
                  (noConfusion OIDs.RSA.SHA512))
                (NoConfusion.sumₚ{A = RSA.SHA384}
                  (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA384 OIDs.RSA.SHA512)
                  (noConfusion OIDs.RSA.SHA384)))
              (NoConfusion.sumₚ{A = RSA.SHA256}
                (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA256 OIDs.RSA.SHA384)
                (NoConfusion.sumₚ{A = RSA.SHA256}
                  (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA256 OIDs.RSA.SHA512)
                  (noConfusion OIDs.RSA.SHA256))))
            (NoConfusion.sumₚ{A = RSA.SHA224}
              (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA224 OIDs.RSA.SHA256)
              (NoConfusion.sumₚ{A = RSA.SHA224}
                (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA224 OIDs.RSA.SHA384)
                (NoConfusion.sumₚ{A = RSA.SHA224}
                  (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA224 OIDs.RSA.SHA512)
                  (noConfusion OIDs.RSA.SHA224)))))
          (NoConfusion.sumₚ{A = RSA.SHA1}
            (HashAlg.SHA-Like.noConfusion OIDs.RSA.SHA1 OIDs.RSA.SHA224)
            (NoConfusion.sumₚ{A = RSA.SHA1}
              (HashAlg.SHA-Like.noConfusion _ _)
              (NoConfusion.sumₚ {A = RSA.SHA1}
                (HashAlg.SHA-Like.noConfusion _ _)
                (NoConfusion.sumₚ{A = RSA.SHA1}
                  (HashAlg.SHA-Like.noConfusion _ _)
                  (noConfusion OIDs.RSA.SHA1))))))
        (NoConfusion.sumₚ{A = RSA.MD5}
          (HashAlg.SHA-Like.noConfusion _ _)
          (NoConfusion.sumₚ{A = RSA.MD5}
            (HashAlg.SHA-Like.noConfusion _ _)
            (NoConfusion.sumₚ{A = RSA.MD5}
              (HashAlg.SHA-Like.noConfusion _ _)
              (NoConfusion.sumₚ{A = RSA.MD5}
                (HashAlg.SHA-Like.noConfusion _ _)
                (NoConfusion.sumₚ{A = RSA.MD5}
                  (HashAlg.SHA-Like.noConfusion _ _)
                  (noConfusion OIDs.RSA.MD5)))))))
      (NoConfusion.sumₚ{A = RSA.MD2}
        (HashAlg.SHA-Like.noConfusion _ _)
        (NoConfusion.sumₚ{A = RSA.MD2}
          (HashAlg.SHA-Like.noConfusion _ _)
          (NoConfusion.sumₚ{A = RSA.MD2} (HashAlg.SHA-Like.noConfusion _ _)
            (NoConfusion.sumₚ{A = RSA.MD2} (HashAlg.SHA-Like.noConfusion _ _)
              (NoConfusion.sumₚ{A = RSA.MD2} (HashAlg.SHA-Like.noConfusion _ _)
                (NoConfusion.sumₚ{A = RSA.MD2} (HashAlg.SHA-Like.noConfusion _ _)
                  (noConfusion OIDs.RSA.MD2)))))))
