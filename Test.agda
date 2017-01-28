{-# OPTIONS --type-in-type #-}

module Test where

open import Data.Bool
open import Data.List

open import Conversion Bool
open import DFA Bool
open import Language Bool
open import NFA Bool
open import Regex Bool

module _ where
  private
    open Regex→NFA
  
    regex : Regex
    regex = ⟨ true ⟩ ∙ ⟨ false ⟩ + ∙ ⟨ true ⟩
    
    regexNFA = Regex→NFA.nfa regex
    
    open NFA regexNFA
    open NFA→DFA regexNFA
  
    regexDFA = NFA→DFA.dfa regexNFA
  
    open DFA regexDFA
    
    accept : DFA.Accept regexDFA (true ∷ false ∷ false ∷ true ∷ [])
    accept =
      (((([] ,
      (stepLeft-∙ step-⟨ true ⟩ ,
      (stepOver-∙ end-⟨ true ⟩ ∷ []))) ,
      (stepRight-∙ (stepLeft-∙ (step-+ step-⟨ false ⟩)) ,
      (stepRight-∙ (stepLeft-∙ (loop-+ end-⟨ false ⟩)) ∷ []))) ,
      (stepRight-∙ (stepLeft-∙ (step-+ step-⟨ false ⟩)) ,
      (stepRight-∙ (stepOver-∙ (end-+ end-⟨ false ⟩)) ∷ []))) ,
      (stepRight-∙ (stepRight-∙ step-⟨ true ⟩) ,
      [])) ,
      end-∙ (end-∙ end-⟨ true ⟩)
