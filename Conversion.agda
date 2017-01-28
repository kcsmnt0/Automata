{-# OPTIONS --type-in-type #-}

module Conversion Token where

open import Data.Empty
open import Data.List as List hiding (map; _++_; _∷ʳ_)
open import Data.Maybe as Maybe hiding (map)
open import Data.Product as × hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary

open import DFA Token
open import Language Token
open import NFA Token
open import Regex Token

-- powerset/subset construction
module NFA→DFA (nfa : NFA) where
  open NFA nfa

  record Stride m w n : Set where
    constructor _,_
    field
      {middle} : State
      step : Step m (just w) middle
      ε-path : ε-Path middle n

  open Stride public

  data Walk m : String → State → Set where
    [] : Walk m [] m
    _∷_ : ∀ {n o w ws} → Stride m w n → Walk n ws o → Walk m (w ∷ ws) o

  record Walk^ m n ws : Set where
    constructor _,_
    field
      {middle} : State
      ε-path : ε-Path m middle
      walk : Walk middle n ws

  pathWalk : ∀ {m n ws} → Path m n ws → Walk^ m n ws
  pathWalk [] = [] , []
  pathWalk (_∷_ {w = just _} p ps) = case pathWalk ps of λ where (qs , rs) → [] , ((p , qs) ∷ rs)
  pathWalk (_∷_ {w = nothing} p ps) = case pathWalk ps of λ where (qs , rs) → (p ∷ qs) , rs
  
  StartSubset : State → Set
  StartSubset = ε-Path start

  record StepSubset (P : State → Set) s w : Set where
    constructor _,_
    field
      {state} : State
      element : P state
      steppable : Stride state s w

  open StepSubset public

  record FinalSubset (P : State → Set) : Set where
    constructor _,_
    field
      {state} : State
      element : P state
      final : Final state

  open FinalSubset public

  dfa : DFA
  dfa = record
    { State = State → Set
    ; start = StartSubset
    ; Final = FinalSubset
    ; step = StepSubset
    }

  open DFA dfa

  walkEval : ∀ {P m n ws} → P m → Walk m ws n → eval P ws n
  walkEval p [] = p
  walkEval p (q ∷ qs) = walkEval (p , q) qs

  acceptsEval : ∀ {ws} → NFA.Accept nfa ws → DFA.Accept dfa ws
  acceptsEval (ps , e) = let (qs , rs) = pathWalk ps in walkEval qs rs , e

module DFA→NFA (dfa : DFA) where
  open DFA dfa

  data DeterminedStep s : Maybe Token → State → Set where
    go : ∀ {t} → DeterminedStep s (just t) (step s t)

  nfa : NFA
  nfa = record
    { State = State
    ; start = start
    ; Final = Final
    ; Step = DeterminedStep
    }

  open NFA nfa

  pathEval : ∀ {ws s s′} → eval s ws ≡ s′ → Path s ws s′
  pathEval {[]} refl = []
  pathEval {_ ∷ _} refl = go ∷ pathEval refl

  acceptsEval : ∀ {ws} → DFA.Accept dfa ws → NFA.Accept nfa ws
  acceptsEval {[]} p = [] , p
  acceptsEval {_ ∷ _} p = pathEval refl , p

-- Thompson's construction
module Regex→NFA where
  data State : Regex → Set where
    ε : State ε

    start-⟨_⟩ end-⟨_⟩ : ∀ c → State ⟨ c ⟩

    start-∣ : ∀ {r s} → State (r ∣ s)
    left-∣ : ∀ {s r} → State r → State (r ∣ s)
    right-∣ : ∀ {r s} → State s → State (r ∣ s)

    left-∙ : ∀ {s r} → State r → State (r ∙ s)
    right-∙ : ∀ {r s} → State s → State (r ∙ s)

    in-+ : ∀ {r} → State r → State (r +)

  start : ∀ r → State r
  start ε = ε
  start ⟨ c ⟩ = start-⟨ c ⟩
  start (r ∣ s) = start-∣
  start (r ∙ s) = left-∙ (start r)
  start (r +) = in-+ (start r)

  data Final : ∀ {r} → State r → Set where
    end-ε : Final ε
    end-⟨_⟩ : ∀ c → Final end-⟨ c ⟩
    endLeft-∣ : ∀ {r s} {m : State r} → Final m → Final (left-∣ {s} m)
    endRight-∣ : ∀ {r s} {m : State s} → Final m → Final (right-∣ {r} m)
    end-∙ : ∀ {r s} {m : State s} → Final m → Final (right-∙ {r} m)
    end-+ : ∀ {r} {m : State r} → Final m → Final (in-+ m)

  data Step : ∀ {r s} → State r → Maybe Token → State s → Set where
    step-⟨_⟩ : ∀ c → Step start-⟨ c ⟩ (just c) end-⟨ c ⟩

    startLeft-∣ : ∀ {r s} → Step (start-∣ {r} {s}) nothing (left-∣ {s} (start r))
    stepLeft-∣ : ∀ {r s t w} {m : State r} {n : State t} → Step m w n → Step (left-∣ {s} m) w (left-∣ {s} n)
    startRight-∣ : ∀ {r s} → Step (start-∣ {r} {s}) nothing (right-∣ {r} (start s))
    stepRight-∣ : ∀ {r s t w} {m : State r} {n : State t} → Step m w n → Step (right-∣ {s} m) w (right-∣ {s} n)

    stepLeft-∙ : ∀ {r s t w} {m : State r} {n : State t} → Step m w n → Step (left-∙ {s} m) w (left-∙ {s} n)
    stepOver-∙ : ∀ {r s} {m : State r} → Final m → Step (left-∙ {s} m) nothing (right-∙ {r} (start s))
    stepRight-∙ : ∀ {r s t w} {m : State s} {n : State t} → Step m w n → Step (right-∙ {r} m) w (right-∙ {r} n)

    step-+ : ∀ {r s w} {m : State r} {n : State s} → Step m w n → Step (in-+ m) w (in-+ n)
    loop-+ : ∀ {r} {m : State r} → Final m → Step (in-+ m) nothing (in-+ (start r))
  
  nfa : Regex → NFA
  nfa r = record
    { State = State r
    ; start = start r
    ; Final = Final
    ; Step = Step
    }

  open NFA using (Path; []; _∷_; _,_)
  open module RegexNFA {n} = NFA (nfa n) using (_++_; _∷ʳ_)

  map :
    {f : Regex → Regex} →
    {g : ∀ {r} → State r → State (f r)} →
    (∀ {r w} {m n : State r} → Step m w n → Step (g m) w (g n)) →
    ∀ {r m n w} →
    Path (nfa r) m w n →
    Path (nfa (f r)) (g m) w (g n)
  map h [] = []
  map h (p ∷ ps) = h p ∷ map h ps

  matchAccept : ∀ {r w} → Match r w → NFA.Accept (nfa r) w
  matchAccept ε = [] , end-ε
  matchAccept ⟨ c ⟩ = (step-⟨ c ⟩ ∷ []) , end-⟨ c ⟩
  matchAccept (left p) =
    let
      a , e = matchAccept p
    in
      startLeft-∣ ∷ map stepLeft-∣ a , endLeft-∣ e
  matchAccept (right p) =
    let
      a , e = matchAccept p
    in
      startRight-∣ ∷ map stepRight-∣ a , endRight-∣ e
  matchAccept {r ∙ s} (p ∙ q) =
    let
      a , e = matchAccept p
      b , e′ = matchAccept q
    in
      map stepLeft-∙ a ++ (stepOver-∙ e ∷ map stepRight-∙ b) , end-∙ e′
  matchAccept (p ∷[]) =
    let
      a , e = matchAccept p
    in
      map step-+ a , end-+ e
  matchAccept {r +} (p ∷ ps) =
    let
      a , e = matchAccept p
      b , e′ = matchAccept ps
    in
      map step-+ a ++ (loop-+ e ∷ b) , e′

  unmapLeft-∣ : ∀ {r s m n w} → Path (nfa (r ∣ s)) (left-∣ m) w (left-∣ n) → Path (nfa r) m w n
  unmapLeft-∣ [] = []
  unmapLeft-∣ (stepLeft-∣ p ∷ ps) = p ∷ unmapLeft-∣ ps

  unmapRight-∣ : ∀ {r s m n w} → Path (nfa (r ∣ s)) (right-∣ m) w (right-∣ n) → Path (nfa s) m w n
  unmapRight-∣ [] = []
  unmapRight-∣ (stepRight-∣ p ∷ ps) = p ∷ unmapRight-∣ ps

  noLeftToRight-∣ : ∀ {r s m n w} → ¬ Path (nfa (r ∣ s)) (left-∣ m) w (right-∣ n)
  noLeftToRight-∣ (stepLeft-∣ p ∷ ps) = noLeftToRight-∣ ps

  noRightToLeft-∣ : ∀ {r s m n w} → ¬ Path (nfa (r ∣ s)) (right-∣ m) w (left-∣ n)
  noRightToLeft-∣ (stepRight-∣ p ∷ ps) = noRightToLeft-∣ ps

  noRightToLeft-∙ : ∀ {r s m n w} → ¬ Path (nfa (r ∙ s)) (right-∙ m) w (left-∙ n)
  noRightToLeft-∙ (stepRight-∙ p ∷ ps) = noRightToLeft-∙ ps

  unmapLeft-∙ : ∀ {r s m n w} → Path (nfa (r ∙ s)) (left-∙ m) w (left-∙ n) → Path (nfa r) m w n
  unmapLeft-∙ [] = []
  unmapLeft-∙ (stepLeft-∙ p ∷ ps) = p ∷ unmapLeft-∙ ps
  unmapLeft-∙ (stepOver-∙ e ∷ ps) = ⊥-elim (noRightToLeft-∙ ps)

  unmapRight-∙ : ∀ {r s m n w} → Path (nfa (r ∙ s)) (right-∙ m) w (right-∙ n) → Path (nfa s) m w n
  unmapRight-∙ [] = []
  unmapRight-∙ (stepRight-∙ p ∷ ps) = p ∷ unmapRight-∙ ps

  data Split-∙ : ∀ {r s} → State r → String → State s → Set where
    split : ∀ {r s ws vs} {m : State r} {n : State r} {o : State s} →
      Path (nfa r) m ws n →
      Final n →
      Path (nfa s) (start s) vs o →
      Split-∙ (left-∙ {s} m) (ws List.++ vs) (right-∙ {r} o)

  split-∙ : ∀ {r s m n ws} → Path (nfa (r ∙ s)) (left-∙ m) ws (right-∙ n) → Split-∙ (left-∙ {s} m) ws (right-∙ {r} n)
  split-∙ (_∷_ {w = w} (stepLeft-∙ p) ps) with split-∙ ps
  … | split qs e rs = subst (λ w → Split-∙ _ w _) (sym (assoc-:?:-++ w)) (split (p ∷ qs) e rs)
  split-∙ (stepOver-∙ e ∷ ps) = split [] e (unmapRight-∙ ps)

  data Split-+ : ∀ {r} → State r → String → State r → Set where
    split1 : ∀ {r ws} {m n : State r} →
      Path (nfa r) m ws n →
      Split-+ (in-+ m) ws (in-+ n)

    split+ : ∀ {r ws vs} {m n o : State r} →
      Path (nfa r) m ws n →
      Final n →
      Split-+ (in-+ (start r)) vs (in-+ o) →
      Split-+ (in-+ m) (ws List.++ vs) (in-+ o)

  split-+ : ∀ {r m n ws} → Path (nfa (r +)) m ws n → Split-+ m ws n
  split-+ {m = in-+ _} [] = split1 []
  split-+ (_∷_ {w = w} (step-+ p) ps) with split-+ ps
  … | split1 qs = split1 (p ∷ qs)
  … | split+ qs e rs = subst (λ w → Split-+ _ w _) (sym (assoc-:?:-++ w)) (split+ (p ∷ qs) e rs)
  split-+ {n = in-+ _} (loop-+ e ∷ ps) = split+ [] e (split-+ ps)

  acceptMatch : ∀ {r w} → NFA.Accept (nfa r) w → Match r w
  acceptMatch {ε} ([] , end-ε) = ε
  acceptMatch {ε} ((() ∷ _) , end-ε)

  acceptMatch {⟨ c ⟩} ((step-⟨ .c ⟩ ∷ []) , end-⟨ .c ⟩) = ⟨ c ⟩
  acceptMatch {⟨ c ⟩} ((step-⟨ .c ⟩ ∷ (() ∷ _)) , end-⟨ .c ⟩)

  acceptMatch {r ∣ s} ((startLeft-∣ ∷ ps) , endLeft-∣ e) = left (acceptMatch (unmapLeft-∣ ps , e))
  acceptMatch {r ∣ s} ((startRight-∣ ∷ ps) , endRight-∣ e) = right (acceptMatch (unmapRight-∣ ps , e))
  acceptMatch {r ∣ s} ((startLeft-∣ ∷ ps) , endRight-∣ e) = ⊥-elim (noLeftToRight-∣ ps)
  acceptMatch {r ∣ s} ((startRight-∣ ∷ ps) , endLeft-∣ e) = ⊥-elim (noRightToLeft-∣ ps)

  acceptMatch {r ∙ s} (ps , end-∙ e′) with split-∙ ps
  … | split qs e rs = acceptMatch (qs , e) ∙ acceptMatch (rs , e′)

  acceptMatch {r +} (ps , end-+ e) = lem (split-+ ps) e
    where
      lem : ∀ {m ws} → Split-+ (in-+ (start r)) ws (in-+ m) → Final m → Match (r +) ws
      lem (split1 ps) e = acceptMatch (ps , e) ∷[]
      lem (split+ ps e qs) e′ = acceptMatch (ps , e) ∷ lem qs e′
