{-# OPTIONS --type-in-type #-}

module DFA Token where

open import Data.List
open import Function

open import Language Token

record DFA : Set where
  field
    State : Set
    start : State
    Final : State → Set
    step : State → Token → State

  eval : State → String → State
  eval = foldl step

  Accept : Language
  Accept = Final ∘ eval start
