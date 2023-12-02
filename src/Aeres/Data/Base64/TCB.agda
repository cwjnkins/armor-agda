open import Aeres.Binary
import      Aeres.Grammar.IList
open import Aeres.Prelude

module Aeres.Data.Base64.TCB where

open Aeres.Grammar.IList Char

record Base64Char (@0 bs : List Char) : Set where
  constructor mk64
  field
    @0 c : Char
    @0 c∈ : c ∈ Base64.charset
    i : Singleton (Any.index c∈)
    @0 bs≡ : bs ≡ [ c ]

record Base64Pad2 (@0 bs : List Char) : Set where
  constructor mk64P2
  field
    @0 {b₁ b₂} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    @0 pad : toℕ (↑ Base64Char.i c₂) % (2 ^ 4) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ '=' ∷ [ '=' ]

record Base64Pad1 (@0 bs : List Char) : Set where
  constructor mk64P1
  field
    @0 {b₁ b₂ b₃} : Char
    c₁ : Base64Char [ b₁ ]
    c₂ : Base64Char [ b₂ ]
    c₃ : Base64Char [ b₃ ]
    @0 pad : toℕ (↑ Base64Char.i c₃) % (2 ^ 2) ≡ 0
    @0 bs≡ : bs ≡ b₁ ∷ b₂ ∷ b₃ ∷ [ '=' ]

data Base64Pad (@0 bs : List Char) : Set where
  pad0 : bs ≡ []       → Base64Pad bs
  pad1 : Base64Pad1 bs → Base64Pad bs
  pad2 : Base64Pad2 bs → Base64Pad bs

record Base64Str (@0 bs : List Char) : Set where
  constructor mk64Str
  field
    @0 {s p} : List Char
    str : IList Base64Char s
    @0 strLen : length s % 4 ≡ 0
    pad : Base64Pad p
    @0 bs≡ : bs ≡ s ++ p

decodeStr : ∀ {@0 bs} → Base64Str bs → List UInt8
decodeStr (mk64Str str strLen pad bs≡) =
  helper₁ str strLen ++ helper₂ pad
  where
  helper₁ : ∀ {@0 bs} → IList Base64Char bs → @0 length bs % 4 ≡ 0
            → List UInt8
  helper₁ nil refl = []
  helper₁ (cons (mkIListCons (mk64 _ _ i refl) (cons (mkIListCons (mk64 _ _ i₁ refl) (cons (mkIListCons (mk64 _ _ i₂ refl) (cons (mkIListCons (mk64 _ _ i₃ refl) tail₁ refl)) refl)) refl)) refl)) pf =
       from-just
         (Digs.base64To256 (↑ i ∷ ↑ i₁ ∷ ↑ i₂ ∷ [ ↑ i₃ ]))
    ++ helper₁ tail₁ pf

  helper₂ : ∀ {@0 bs} → Base64Pad bs → List UInt8
  helper₂ (pad0 x) = []
  helper₂ (pad1 (mk64P1 (mk64 _ _ i _) (mk64 _ _ i₁ _) (mk64 _ _ i₂ _) _ _)) =
    from-just (Digs.base64To256 ((↑ i) ∷ (↑ i₁) ∷ [ ↑ i₂ ]))
  helper₂ (pad2 (mk64P2 (mk64 _ _ i _) (mk64 _ _ i₁ _) _ _)) =
    from-just (Digs.base64To256 ((↑ i) ∷ [ ↑ i₁ ]))
