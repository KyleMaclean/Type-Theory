-- developed with Agda version 2.6.2.1

-- true (Set with one element)

record ⊤ : Set where
  constructor t

-- false (Set without elements)

data ⊥ : Set where

-- conjunction

infixr 2 _×_
infixr 4 _,_
record _×_ (A B : Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public
infix 3 _∧_
_∧_ : Set → Set → Set
A ∧ B = A × B

-- disjunction

infixr 1 _⊎_
data _⊎_(A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B
infix 2 _∨_
_∨_ : Set → Set → Set
A ∨ B = A ⊎ B

-- implication

infixr 1 _⇒_
_⇒_ :  Set → Set → Set
A ⇒ B = A → B

-- equivalence

infix 0 _⇔_
_⇔_ :  Set → Set → Set
A ⇔ B = (A ⇒ B) ∧ (B ⇒ A)

-- negation

¬_ : Set → Set
¬ A = A ⇒ ⊥

-- reductio ad absurdo

RAA : Set → Set
RAA A = ¬ ¬ A ⇒ A