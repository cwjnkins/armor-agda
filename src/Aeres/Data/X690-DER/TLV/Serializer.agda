{-# OPTIONS --subtyping #-}

open import Aeres.Binary
open        Base256
open import Aeres.Data.X690-DER.Length
open import Aeres.Data.X690-DER.TLV.TCB
open import Aeres.Prelude

module Aeres.Data.X690-DER.TLV.Serializer
  {@0 A : List UInt8 → Set} (ser : ∀ {@0 bs} → A bs → Singleton bs)
  where

serialize : ∀ {@0 bs} {t} → TLV t A bs → Singleton bs
serialize{t = t} (mkTLV len val len≡ bs≡)
  with Length.serialize len
  |    ser val
... | singleton l refl | singleton v refl =
  singleton (t ∷ l ++ v) (sym bs≡)
