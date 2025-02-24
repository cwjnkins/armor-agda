{-# OPTIONS --erasure --sized-types #-}

open import Armor.Binary
open import Armor.Prelude
open import Armor.Data.Unicode.UTF8.TCB
open import Armor.Data.Unicode.UTF8.Trie
import      Armor.Grammar.IList

module Armor.Data.X509.Semantic.StringPrep.CaseFoldNFKC.M4 where

open Armor.Grammar.IList UInt8

trie₄ : List (List UInt8 × Exists─ (List UInt8) UTF8)
trie₄ = ((# 208 ∷ [ # 148 ]) , (─ (# 208 ∷ [ # 180 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 180 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 149 ]) , (─ (# 208 ∷ [ # 181 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 150 ]) , (─ (# 208 ∷ [ # 182 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 182 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 151 ]) , (─ (# 208 ∷ [ # 183 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 152 ]) , (─ (# 208 ∷ [ # 184 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 184 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 153 ]) , (─ (# 208 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 154 ]) , (─ (# 208 ∷ [ # 186 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 186 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 155 ]) , (─ (# 208 ∷ [ # 187 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 156 ]) , (─ (# 208 ∷ [ # 188 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 188 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 157 ]) , (─ (# 208 ∷ [ # 189 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 158 ]) , (─ (# 208 ∷ [ # 190 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 190 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 159 ]) , (─ (# 208 ∷ [ # 191 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 208 } tt) (toWitness {a? = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 160 ]) , (─ (# 209 ∷ [ # 128 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 128 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 161 ]) , (─ (# 209 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 162 ]) , (─ (# 209 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 163 ]) , (─ (# 209 ∷ [ # 131 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 131 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 164 ]) , (─ (# 209 ∷ [ # 132 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 165 ]) , (─ (# 209 ∷ [ # 133 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 133 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 166 ]) , (─ (# 209 ∷ [ # 134 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 167 ]) , (─ (# 209 ∷ [ # 135 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 135 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 168 ]) , (─ (# 209 ∷ [ # 136 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 169 ]) , (─ (# 209 ∷ [ # 137 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 137 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 170 ]) , (─ (# 209 ∷ [ # 138 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 138 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 171 ]) , (─ (# 209 ∷ [ # 139 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 172 ]) , (─ (# 209 ∷ [ # 140 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 140 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 173 ]) , (─ (# 209 ∷ [ # 141 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 174 ]) , (─ (# 209 ∷ [ # 142 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 142 } tt) refl)) nil refl)))
          ∷ ((# 208 ∷ [ # 175 ]) , (─ (# 209 ∷ [ # 143 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 143 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 160 ]) , (─ (# 209 ∷ [ # 161 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 162 ]) , (─ (# 209 ∷ [ # 163 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 164 ]) , (─ (# 209 ∷ [ # 165 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 166 ]) , (─ (# 209 ∷ [ # 167 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 168 ]) , (─ (# 209 ∷ [ # 169 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 170 ]) , (─ (# 209 ∷ [ # 171 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 172 ]) , (─ (# 209 ∷ [ # 173 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 174 ]) , (─ (# 209 ∷ [ # 175 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 176 ]) , (─ (# 209 ∷ [ # 177 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 178 ]) , (─ (# 209 ∷ [ # 179 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 180 ]) , (─ (# 209 ∷ [ # 181 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 182 ]) , (─ (# 209 ∷ [ # 183 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 184 ]) , (─ (# 209 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 186 ]) , (─ (# 209 ∷ [ # 187 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 188 ]) , (─ (# 209 ∷ [ # 189 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 209 ∷ [ # 190 ]) , (─ (# 209 ∷ [ # 191 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 209 } tt) (toWitness {a? = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 128 ]) , (─ (# 210 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 138 ]) , (─ (# 210 ∷ [ # 139 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 139 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 140 ]) , (─ (# 210 ∷ [ # 141 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 141 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 142 ]) , (─ (# 210 ∷ [ # 143 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 143 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 144 ]) , (─ (# 210 ∷ [ # 145 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 146 ]) , (─ (# 210 ∷ [ # 147 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 148 ]) , (─ (# 210 ∷ [ # 149 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 150 ]) , (─ (# 210 ∷ [ # 151 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 152 ]) , (─ (# 210 ∷ [ # 153 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 153 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 154 ]) , (─ (# 210 ∷ [ # 155 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 155 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 156 ]) , (─ (# 210 ∷ [ # 157 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 157 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 158 ]) , (─ (# 210 ∷ [ # 159 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 159 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 160 ]) , (─ (# 210 ∷ [ # 161 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 162 ]) , (─ (# 210 ∷ [ # 163 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 164 ]) , (─ (# 210 ∷ [ # 165 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 166 ]) , (─ (# 210 ∷ [ # 167 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 168 ]) , (─ (# 210 ∷ [ # 169 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 170 ]) , (─ (# 210 ∷ [ # 171 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 172 ]) , (─ (# 210 ∷ [ # 173 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 174 ]) , (─ (# 210 ∷ [ # 175 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 176 ]) , (─ (# 210 ∷ [ # 177 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 178 ]) , (─ (# 210 ∷ [ # 179 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 180 ]) , (─ (# 210 ∷ [ # 181 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 182 ]) , (─ (# 210 ∷ [ # 183 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 183 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 184 ]) , (─ (# 210 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 186 ]) , (─ (# 210 ∷ [ # 187 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 187 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 188 ]) , (─ (# 210 ∷ [ # 189 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 189 } tt) refl)) nil refl)))
          ∷ ((# 210 ∷ [ # 190 ]) , (─ (# 210 ∷ [ # 191 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 210 } tt) (toWitness {a? = inRange? 128 191 191 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 129 ]) , (─ (# 211 ∷ [ # 130 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 130 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 131 ]) , (─ (# 211 ∷ [ # 132 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 132 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 133 ]) , (─ (# 211 ∷ [ # 134 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 134 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 135 ]) , (─ (# 211 ∷ [ # 136 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 136 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 137 ]) , (─ (# 211 ∷ [ # 138 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 138 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 139 ]) , (─ (# 211 ∷ [ # 140 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 140 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 141 ]) , (─ (# 211 ∷ [ # 142 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 142 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 144 ]) , (─ (# 211 ∷ [ # 145 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 145 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 146 ]) , (─ (# 211 ∷ [ # 147 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 147 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 148 ]) , (─ (# 211 ∷ [ # 149 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 149 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 150 ]) , (─ (# 211 ∷ [ # 151 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 151 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 152 ]) , (─ (# 211 ∷ [ # 153 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 153 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 154 ]) , (─ (# 211 ∷ [ # 155 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 155 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 156 ]) , (─ (# 211 ∷ [ # 157 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 157 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 158 ]) , (─ (# 211 ∷ [ # 159 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 159 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 160 ]) , (─ (# 211 ∷ [ # 161 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 161 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 162 ]) , (─ (# 211 ∷ [ # 163 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 163 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 164 ]) , (─ (# 211 ∷ [ # 165 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 165 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 166 ]) , (─ (# 211 ∷ [ # 167 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 167 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 168 ]) , (─ (# 211 ∷ [ # 169 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 169 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 170 ]) , (─ (# 211 ∷ [ # 171 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 171 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 172 ]) , (─ (# 211 ∷ [ # 173 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 173 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 174 ]) , (─ (# 211 ∷ [ # 175 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 175 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 176 ]) , (─ (# 211 ∷ [ # 177 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 177 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 178 ]) , (─ (# 211 ∷ [ # 179 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 179 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 180 ]) , (─ (# 211 ∷ [ # 181 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 181 } tt) refl)) nil refl)))
          ∷ ((# 211 ∷ [ # 184 ]) , (─ (# 211 ∷ [ # 185 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 211 } tt) (toWitness {a? = inRange? 128 191 185 } tt) refl)) nil refl)))
          ∷ ((# 212 ∷ [ # 128 ]) , (─ (# 212 ∷ [ # 129 ]) , cons (mkIListCons (utf82 (mkUTF8Char2 _ _ (toWitness {a? = inRange? 192 223 212 } tt) (toWitness {a? = inRange? 128 191 129 } tt) refl)) nil refl)))
          ∷ []


