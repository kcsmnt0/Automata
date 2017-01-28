{-# OPTIONS --type-in-type #-}

module Language Token where

open import Data.List

String : Set
String = List Token

Language : Set
Language = String → Set
