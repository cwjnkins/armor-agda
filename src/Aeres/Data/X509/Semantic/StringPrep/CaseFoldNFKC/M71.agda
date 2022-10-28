
{-# OPTIONS --subtyping --sized-types #-}

open import Aeres.Binary
open import Aeres.Prelude
open import Aeres.Data.UTF8.TCB
open import Aeres.Data.UTF8.Trie
import      Aeres.Grammar.IList

module Aeres.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M71 where

open Base256
open Aeres.Grammar.IList UInt8

trie₇₁ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₇₁ = ((# 225 ∷ # 188 ∷ [ # 190 ]) , (─ (# 225 ∷ # 188 ∷ [ # 182 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 182 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 188 ∷ [ # 191 ]) , (─ (# 225 ∷ # 188 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 136 ]) , (─ (# 225 ∷ # 189 ∷ [ # 128 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 137 ]) , (─ (# 225 ∷ # 189 ∷ [ # 129 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 138 ]) , (─ (# 225 ∷ # 189 ∷ [ # 130 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 139 ]) , (─ (# 225 ∷ # 189 ∷ [ # 131 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 140 ]) , (─ (# 225 ∷ # 189 ∷ [ # 132 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 141 ]) , (─ (# 225 ∷ # 189 ∷ [ # 133 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 144 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ [ # 147 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 146 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 147 ∷ # 204 ∷ [ # 128 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 148 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 147 ∷ # 204 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 150 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 147 ∷ # 205 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 207 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 204 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 205 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 153 ]) , (─ (# 225 ∷ # 189 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 155 ]) , (─ (# 225 ∷ # 189 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 157 ]) , (─ (# 225 ∷ # 189 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 159 ]) , (─ (# 225 ∷ # 189 ∷ [ # 151 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 168 ]) , (─ (# 225 ∷ # 189 ∷ [ # 160 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 160 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 169 ]) , (─ (# 225 ∷ # 189 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 170 ]) , (─ (# 225 ∷ # 189 ∷ [ # 162 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 162 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 171 ]) , (─ (# 225 ∷ # 189 ∷ [ # 163 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 172 ]) , (─ (# 225 ∷ # 189 ∷ [ # 164 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 164 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 173 ]) , (─ (# 225 ∷ # 189 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 174 ]) , (─ (# 225 ∷ # 189 ∷ [ # 166 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 166 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 189 ∷ [ # 175 ]) , (─ (# 225 ∷ # 189 ∷ [ # 167 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 189 } tt) (toWitness {Q = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 128 ]) , (─ (# 225 ∷ # 188 ∷ # 128 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 129 ]) , (─ (# 225 ∷ # 188 ∷ # 129 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 130 ]) , (─ (# 225 ∷ # 188 ∷ # 130 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 131 ]) , (─ (# 225 ∷ # 188 ∷ # 131 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 132 ]) , (─ (# 225 ∷ # 188 ∷ # 132 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 133 ]) , (─ (# 225 ∷ # 188 ∷ # 133 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 134 ]) , (─ (# 225 ∷ # 188 ∷ # 134 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 135 ]) , (─ (# 225 ∷ # 188 ∷ # 135 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 136 ]) , (─ (# 225 ∷ # 188 ∷ # 128 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 128 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 137 ]) , (─ (# 225 ∷ # 188 ∷ # 129 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 129 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 138 ]) , (─ (# 225 ∷ # 188 ∷ # 130 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 130 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 139 ]) , (─ (# 225 ∷ # 188 ∷ # 131 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 131 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 140 ]) , (─ (# 225 ∷ # 188 ∷ # 132 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 132 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 141 ]) , (─ (# 225 ∷ # 188 ∷ # 133 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 142 ]) , (─ (# 225 ∷ # 188 ∷ # 134 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 134 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 143 ]) , (─ (# 225 ∷ # 188 ∷ # 135 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 135 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 144 ]) , (─ (# 225 ∷ # 188 ∷ # 160 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 160 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 190 ∷ [ # 145 ]) , (─ (# 225 ∷ # 188 ∷ # 161 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {Q = inRange? 224 239 225 } tt) (toWitness {Q = inRange? 128 191 188 } tt) (toWitness {Q = inRange? 128 191 161 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {Q = inRange? 192 223 206 } tt) (toWitness {Q = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ []

