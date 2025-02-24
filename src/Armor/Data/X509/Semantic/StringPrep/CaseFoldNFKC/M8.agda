{-# OPTIONS --erasure --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M8 where

open Armor.Grammar.IList UInt8

trie₈ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₈ = ((# 225 ∷ # 191 ∷ [ # 155 ]) , (─ (# 225 ∷ # 189 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 162 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 136 ∷ # 204 ∷ [ # 128 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 163 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 136 ∷ # 204 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 164 ]) , (─ (# 207 ∷ # 129 ∷ # 204 ∷ [ # 147 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 147 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 166 ]) , (─ (# 207 ∷ # 133 ∷ # 205 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 205 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 167 ]) , (─ (# 207 ∷ # 133 ∷ # 204 ∷ # 136 ∷ # 205 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 204 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 205 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 168 ]) , (─ (# 225 ∷ # 191 ∷ [ # 160 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 191 } tt) (toWitness {a? = inRange? 128 191 160 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 169 ]) , (─ (# 225 ∷ # 191 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 191 } tt) (toWitness {a? = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 170 ]) , (─ (# 225 ∷ # 189 ∷ [ # 186 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 186 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 171 ]) , (─ (# 225 ∷ # 189 ∷ [ # 187 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 172 ]) , (─ (# 225 ∷ # 191 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 191 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 178 ]) , (─ (# 225 ∷ # 189 ∷ # 188 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 188 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 179 ]) , (─ (# 207 ∷ # 137 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 180 ]) , (─ (# 207 ∷ # 142 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 142 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 182 ]) , (─ (# 207 ∷ # 137 ∷ # 205 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 205 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 183 ]) , (─ (# 207 ∷ # 137 ∷ # 205 ∷ # 130 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 205 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 184 ]) , (─ (# 225 ∷ # 189 ∷ [ # 184 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 185 ]) , (─ (# 225 ∷ # 189 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 186 ]) , (─ (# 225 ∷ # 189 ∷ [ # 188 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 188 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 187 ]) , (─ (# 225 ∷ # 189 ∷ [ # 189 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 225 } tt) (toWitness {a? = inRange? 128 191 189 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 225 ∷ # 191 ∷ [ # 188 ]) , (─ (# 207 ∷ # 137 ∷ # 206 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) (cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 130 ∷ [ # 168 ]) , (─ (# 114 ∷ [ # 115 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 115 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 130 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 131 ]) , (─ (# 194 ∷ # 176 ∷ [ # 99 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 194 } tt) (toWitness {a? = inRange? 128 191 176 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 135 ]) , (─ (# 201 ∷ [ # 155 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 201 } tt) (toWitness {a? = inRange? 128 191 155 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 137 ]) , (─ (# 194 ∷ # 176 ∷ [ # 102 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 194 } tt) (toWitness {a? = inRange? 128 191 176 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 102 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 139 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 140 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 141 ]) , (─ ([ # 104 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 144 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 145 ]) , (─ ([ # 105 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 105 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 146 ]) , (─ ([ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 108 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 149 ]) , (─ ([ # 110 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 110 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 150 ]) , (─ (# 110 ∷ [ # 111 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 110 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 111 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 153 ]) , (─ ([ # 112 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 112 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 154 ]) , (─ ([ # 113 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 113 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 155 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 156 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 157 ]) , (─ ([ # 114 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 114 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 160 ]) , (─ (# 115 ∷ [ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 115 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 161 ]) , (─ (# 116 ∷ # 101 ∷ [ # 108 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 116 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 101 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 108 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 162 ]) , (─ (# 116 ∷ [ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 116 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 164 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 166 ]) , (─ (# 207 ∷ [ # 137 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 168 ]) , (─ ([ # 122 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 122 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 170 ]) , (─ ([ # 107 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 107 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 171 ]) , (─ (# 195 ∷ [ # 165 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 195 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 172 ]) , (─ ([ # 98 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 98 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 173 ]) , (─ ([ # 99 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 99 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 176 ]) , (─ ([ # 101 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 101 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 177 ]) , (─ ([ # 102 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 102 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 179 ]) , (─ ([ # 109 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 109 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 190 ]) , (─ (# 206 ∷ [ # 179 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 206 } tt) (toWitness {a? = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 132 ∷ [ # 191 ]) , (─ (# 207 ∷ [ # 128 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 207 } tt) (toWitness {a? = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 133 ]) , (─ ([ # 100 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 100 <? 128 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 160 ]) , (─ (# 226 ∷ # 133 ∷ [ # 176 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 176 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 161 ]) , (─ (# 226 ∷ # 133 ∷ [ # 177 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 162 ]) , (─ (# 226 ∷ # 133 ∷ [ # 178 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 178 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 163 ]) , (─ (# 226 ∷ # 133 ∷ [ # 179 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 164 ]) , (─ (# 226 ∷ # 133 ∷ [ # 180 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 180 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 165 ]) , (─ (# 226 ∷ # 133 ∷ [ # 181 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 166 ]) , (─ (# 226 ∷ # 133 ∷ [ # 182 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 182 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 167 ]) , (─ (# 226 ∷ # 133 ∷ [ # 183 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 168 ]) , (─ (# 226 ∷ # 133 ∷ [ # 184 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 169 ]) , (─ (# 226 ∷ # 133 ∷ [ # 185 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 170 ]) , (─ (# 226 ∷ # 133 ∷ [ # 186 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 186 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 171 ]) , (─ (# 226 ∷ # 133 ∷ [ # 187 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 172 ]) , (─ (# 226 ∷ # 133 ∷ [ # 188 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 188 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 173 ]) , (─ (# 226 ∷ # 133 ∷ [ # 189 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 174 ]) , (─ (# 226 ∷ # 133 ∷ [ # 190 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 190 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 133 ∷ [ # 175 ]) , (─ (# 226 ∷ # 133 ∷ [ # 191 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 133 } tt) (toWitness {a? = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 182 ]) , (─ (# 226 ∷ # 147 ∷ [ # 144 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 144 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 183 ]) , (─ (# 226 ∷ # 147 ∷ [ # 145 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 184 ]) , (─ (# 226 ∷ # 147 ∷ [ # 146 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 146 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 185 ]) , (─ (# 226 ∷ # 147 ∷ [ # 147 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 186 ]) , (─ (# 226 ∷ # 147 ∷ [ # 148 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 148 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 187 ]) , (─ (# 226 ∷ # 147 ∷ [ # 149 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 188 ]) , (─ (# 226 ∷ # 147 ∷ [ # 150 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 150 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 189 ]) , (─ (# 226 ∷ # 147 ∷ [ # 151 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 190 ]) , (─ (# 226 ∷ # 147 ∷ [ # 152 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 152 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 146 ∷ [ # 191 ]) , (─ (# 226 ∷ # 147 ∷ [ # 153 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 153 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 128 ]) , (─ (# 226 ∷ # 147 ∷ [ # 154 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 154 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 129 ]) , (─ (# 226 ∷ # 147 ∷ [ # 155 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 155 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 130 ]) , (─ (# 226 ∷ # 147 ∷ [ # 156 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 156 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 131 ]) , (─ (# 226 ∷ # 147 ∷ [ # 157 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 157 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 132 ]) , (─ (# 226 ∷ # 147 ∷ [ # 158 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 158 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 133 ]) , (─ (# 226 ∷ # 147 ∷ [ # 159 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 159 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 134 ]) , (─ (# 226 ∷ # 147 ∷ [ # 160 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 160 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 135 ]) , (─ (# 226 ∷ # 147 ∷ [ # 161 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 136 ]) , (─ (# 226 ∷ # 147 ∷ [ # 162 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 162 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 137 ]) , (─ (# 226 ∷ # 147 ∷ [ # 163 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 138 ]) , (─ (# 226 ∷ # 147 ∷ [ # 164 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 164 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 139 ]) , (─ (# 226 ∷ # 147 ∷ [ # 165 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 140 ]) , (─ (# 226 ∷ # 147 ∷ [ # 166 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 166 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 141 ]) , (─ (# 226 ∷ # 147 ∷ [ # 167 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 142 ]) , (─ (# 226 ∷ # 147 ∷ [ # 168 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 168 } tt) refl)) nil refl)))
          ∷ ((# 226 ∷ # 147 ∷ [ # 143 ]) , (─ (# 226 ∷ # 147 ∷ [ # 169 ]) , cons (mkIListCons (utf83 (mkUTF8Char3 _ _ _ (toWitness {a? = inRange? 224 239 226 } tt) (toWitness {a? = inRange? 128 191 147 } tt) (toWitness {a? = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 227 ∷ # 141 ∷ [ # 177 ]) , (─ (# 104 ∷ # 112 ∷ [ # 97 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 104 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 112 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 97 <? 128 } tt) refl)) nil refl)) refl)) refl)))
          ∷ ((# 227 ∷ # 141 ∷ [ # 179 ]) , (─ (# 97 ∷ [ # 117 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 97 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 117 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ ((# 227 ∷ # 141 ∷ [ # 181 ]) , (─ (# 111 ∷ [ # 118 ]) , cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 111 <? 128 } tt) refl)) (cons (mkIListCons (utf81 (mkUTF8Char1 _ (toWitness {a? = 118 <? 128 } tt) refl)) nil refl)) refl)))
          ∷ []


