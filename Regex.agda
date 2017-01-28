{-# OPTIONS --type-in-type #-}

module Regex Token where

open import Data.List

open import Language Token

infixr 5 _∣_
infixr 6 _∙_

data Regex : Set where
  ε : Regex
  ⟨_⟩ : Token → Regex
  _∣_ _∙_ : Regex → Regex → Regex
  _+ : Regex → Regex

_* : Regex → Regex
r * = ε ∣ r +

data Match : Regex → Language where
  ε : Match ε []
  ⟨_⟩ : ∀ c → Match ⟨ c ⟩ [ c ]
  left : ∀ {r q w} → Match r w → Match (r ∣ q) w
  right : ∀ {r q w} → Match q w → Match (r ∣ q) w
  _∙_ : ∀ {r q w v} → Match r w → Match q v → Match (r ∙ q) (w ++ v)
  _∷[] : ∀ {r w} → Match r w → Match (r +) w
  _∷_ : ∀ {r w v} → Match r w → Match (r +) v → Match (r +) (w ++ v)
