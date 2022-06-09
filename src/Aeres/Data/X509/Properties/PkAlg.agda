{-# OPTIONS --subtyping --allow-unsolved-metas #-}

open import Aeres.Data.X509
import      Aeres.Grammar.Definitions
import      Aeres.Grammar.Properties
import      Aeres.Grammar.Sum
import      Aeres.Data.X509.Properties.TLV            as TLVProps
import      Aeres.Data.X509.Properties.Length         as LenProps
open import Aeres.Prelude
open import Aeres.Binary
open import Data.Nat.Properties
  hiding (_≟_)
open import Tactic.MonoidSolver using (solve ; solve-macro)

module Aeres.Data.X509.Properties.PkAlg where

open Base256
open Aeres.Grammar.Definitions Dig
open Aeres.Grammar.Properties  Dig
open import Aeres.Grammar.Sum Dig
open ≡-Reasoning


equivalent : Equivalent (Sum (Sum X509.RSAPkAlg X509.EcPkAlg) (Σₚ X509.SignAlg (λ _ sa → ¬ X509.SignAlg.getSignAlgOIDbs sa ∈ X509.PKOID.Supported))) X509.PkAlg
proj₁ equivalent (inj₁ (inj₁ x)) = X509.PkAlg.rsapkalg x
proj₁ equivalent (inj₁ (inj₂ x)) = X509.PkAlg.ecpkalg x
proj₁ equivalent (inj₂ (mk×ₚ fstₚ₁ sndₚ₁ refl)) = X509.PkAlg.otherpkalg fstₚ₁ sndₚ₁
proj₂ equivalent (X509.PkAlg.rsapkalg x) = inj₁ (inj₁ x)
proj₂ equivalent (X509.PkAlg.ecpkalg x) = inj₁ (inj₂ x)
proj₂ equivalent (X509.PkAlg.otherpkalg x o∉) = inj₂ (mk×ₚ x o∉ refl)

@0 noconfRSA-EC : NoConfusion X509.RSAPkAlg X509.EcPkAlg
noconfRSA-EC {xs₁ = xs₁}{ys₁}{xs₂}{ys₂} xs₁++ys₁≡xs₂++ys₂ (mkTLV{l} len (X509.mkRSAPkAlgFields (singleton _ refl) param refl) len≡ bs≡) (mkTLV{l₁} len₁ (X509.mkEcPkAlgFields{p = p} (singleton _ refl) param₁ refl) len≡₁ bs≡₁) =
  contradiction{P = X509.PKOID.RsaEncPk ++ Singleton.x param ++ ys₁ ≡ X509.PKOID.EcPk ++ p ++ ys₂ }
    (Lemmas.++-cancel≡ˡ _ _ l≡ (∷-injectiveʳ bs≡'))
    λ ()
  where
  @0 bs≡' : _≡_ {A = List UInt8}
              (Tag.Sequence ∷ l  ++ X509.PKOID.RsaEncPk ++ Singleton.x param ++ ys₁)
              (Tag.Sequence ∷ l₁ ++ X509.PKOID.EcPk ++ p ++ ys₂)
  bs≡' = begin
    _ ≡⟨ cong (Tag.Sequence ∷_) (sym (++-assoc l _ ys₁)) ⟩
    (Tag.Sequence ∷ l ++ X509.PKOID.RsaEncPk ++ Singleton.x param) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
    xs₁ ++ ys₁ ≡⟨ xs₁++ys₁≡xs₂++ys₂ ⟩
    xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
    (Tag.Sequence ∷ l₁ ++ X509.PKOID.EcPk ++ p) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (++-assoc l₁ _ ys₂) ⟩
    _ ∎

  @0 l≡ : l ≡ l₁
  l≡ = LenProps.nonnesting (∷-injectiveʳ bs≡') len len₁

@0 nonnesting : NonNesting X509.PkAlg
nonnesting =
  equivalent-nonnesting equivalent
    (NonNesting.sumRestriction
      (nonnestingSum TLVProps.nonnesting TLVProps.nonnesting noconfRSA-EC)
      (nonnestingΣₚ₁ TLVProps.nonnesting)
      restr)
  where
  @0 restr : NonNesting.Restriction (Sum X509.RSAPkAlg X509.EcPkAlg) (Σₚ X509.SignAlg _)
  restr{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ (inj₁ (mkTLV{l = l}{v} len val len≡ bs≡)) (mk×ₚ (mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) _ refl) =
    begin (xs₁ ≡⟨ bs≡ ⟩
          Tag.Sequence ∷ l  ++ v  ≡⟨ cong₂ (λ x y → Tag.Sequence ∷ x ++ y) l≡ v≡ ⟩
          Tag.Sequence ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
          xs₂                     ∎)
    where
    @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ v ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
    bs≡' = begin Tag.Sequence ∷ l ++ v ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 (Tag.Sequence ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                 xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                 (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎
    @0 l≡ : l ≡ l₁
    l≡ = LenProps.nonnesting (∷-injectiveʳ bs≡') len len₁

    @0 v≡ : v ≡ v₁
    v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                   (begin v ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                          v₁ ++ ys₂ ∎)
                   (begin (length v ≡⟨ sym len≡ ⟩
                          getLength len ≡⟨ LenProps.unambiguous-getLength l≡ len len₁ ⟩
                          getLength len₁ ≡⟨ len≡₁ ⟩
                          length v₁ ∎))
  restr{xs₁ = xs₁}{ys₁}{xs₂}{ys₂} ++≡ (inj₂ (mkTLV{l = l}{v} len val len≡ bs≡)) (mk×ₚ (mkTLV{l = l₁}{v₁} len₁ val₁ len≡₁ bs≡₁) _ refl) =
    begin (xs₁ ≡⟨ bs≡ ⟩
          Tag.Sequence ∷ l ++ v ≡⟨ cong₂ (λ x y → _ ∷ x ++ y) l≡ v≡ ⟩
          Tag.Sequence ∷ l₁ ++ v₁ ≡⟨ sym bs≡₁ ⟩
          xs₂ ∎)
    where
    @0 bs≡' : _≡_{A = List UInt8} (Tag.Sequence ∷ l ++ v ++ ys₁) (Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂)
    bs≡' = begin Tag.Sequence ∷ l ++ v ++ ys₁ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 (Tag.Sequence ∷ l ++ v) ++ ys₁ ≡⟨ cong (_++ ys₁) (sym bs≡) ⟩
                 xs₁ ++ ys₁ ≡⟨ ++≡ ⟩
                 xs₂ ++ ys₂ ≡⟨ cong (_++ ys₂) bs≡₁ ⟩
                 (Tag.Sequence ∷ l₁ ++ v₁) ++ ys₂ ≡⟨ cong (Tag.Sequence ∷_) (solve (++-monoid UInt8)) ⟩
                 Tag.Sequence ∷ l₁ ++ v₁ ++ ys₂ ∎

    @0 l≡ : l ≡ l₁
    l≡ = LenProps.nonnesting (∷-injectiveʳ bs≡') len len₁

    @0 v≡ : v ≡ v₁
    v≡ = proj₁ $ Lemmas.length-++-≡ v ys₁ v₁ ys₂
                   (begin v ++ ys₁ ≡⟨ Lemmas.++-cancel≡ˡ _ _ (cong (Tag.Sequence ∷_) l≡) bs≡' ⟩
                          v₁ ++ ys₂ ∎)
                   (begin (length v ≡⟨ sym len≡ ⟩
                          getLength len ≡⟨ LenProps.unambiguous-getLength l≡ len len₁ ⟩
                          getLength len₁ ≡⟨ len≡₁ ⟩
                          length v₁ ∎))

-- postulate
--   @0 unambiguous : Unambiguous X509.PkAlg
