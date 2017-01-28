{-# OPTIONS --type-in-type #-}

module NFA Token where

open import Data.List as List using (List; []; _∷_; [_])
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Function
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Language Token

infixr 5 _:?:_ _:?:ʳ_

_:?:_ : Maybe Token → String → String
just w :?: ws = w ∷ ws
nothing :?: ws = ws

_:?:ʳ_ : String → Maybe Token → String
ws :?:ʳ just w = ws List.∷ʳ w
ws :?:ʳ nothing = ws

commute-[]-:?:ʳ : ∀ w → [] :?:ʳ w ≡ w :?: []
commute-[]-:?:ʳ (just _) = refl
commute-[]-:?:ʳ nothing = refl

assoc-∷-:?:ʳ : ∀ u v {ws} → u ∷ (ws :?:ʳ v) ≡ (u ∷ ws) :?:ʳ v
assoc-∷-:?:ʳ u (just _) = refl
assoc-∷-:?:ʳ u nothing = refl

assoc-:?:-:?:ʳ : ∀ u v {ws} → u :?: (ws :?:ʳ v) ≡ (u :?: ws) :?:ʳ v
assoc-:?:-:?:ʳ (just _) (just _) = refl
assoc-:?:-:?:ʳ (just _) nothing = refl
assoc-:?:-:?:ʳ nothing _ = refl

assoc-:?:-++ : ∀ u {ws vs} → u :?: (ws List.++ vs) ≡ (u :?: ws) List.++ vs
assoc-:?:-++ (just u) = refl
assoc-:?:-++ nothing = refl

data Foldr {A B} {P : A → Set} (f : A → B → B) (b : B) : List A → B → Set where
  [] : Foldr f b [] b
  _∷_ : ∀ {x y xs} → P x → Foldr {P = P} f b xs y → Foldr f b (x ∷ xs) (f x y)

record NFA : Set where
  infixr 5 _∷ʳ_

  field
    State : Set
    start : State
    Final : State → Set
    Step : State → Maybe Token → State → Set

  data Path m : String → State → Set where
    [] : Path m [] m
    _∷_ : ∀ {n o w ws} → Step m w n → Path n ws o → Path m (w :?: ws) o

  steps : ∀ {m n ws} (p : Path m ws n) → List State
  steps {m} [] = [ m ]
  steps {m} (_ ∷ ps) = m ∷ steps ps

  ε-Path : State → State → Set
  ε-Path m n = Path m [] n

  record Accept ws : Set where
    constructor _,_
    field
      {end} : State
      walk : Path start ws end
      final : Final end

  open Accept public

  _∷ʳ_ : ∀ {m n o w ws} → Path m ws n → Step n w o → Path m (ws :?:ʳ w) o
  _∷ʳ_ {w = w} [] q = subst (λ w → Path _ w _) (sym (commute-[]-:?:ʳ w)) (q ∷ [])
  _∷ʳ_ {w = v} (_∷_ {w = w} p ps) q = subst (λ w → Path _ w _) (assoc-:?:-:?:ʳ w v) (p ∷ ps ∷ʳ q)

  _++_ : ∀ {m n o ws vs} → Path m ws n → Path n vs o → Path m (ws List.++ vs) o
  [] ++ qs = qs
  (_∷_ {w = w} p ps) ++ qs = subst (λ w → Path _ w _) (assoc-:?:-++ w) (p ∷ ps ++ qs)
