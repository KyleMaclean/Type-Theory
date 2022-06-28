-- developed with Agda version 2.6.2.1

open import library-of-propositional-logic

variable A B C : Set

infix 2 _∨'_
_∨'_ : Set → Set → Set
A ∨' B = ¬ (¬ A ∧ ¬ B)

tnd' : A ∨' ¬ A
tnd' (¬p , ¬¬p) = ¬¬p ¬p

inj₁' : A → A ∨' B
inj₁' p (¬p , ¬q) = ¬p p

inj₂' : B → A ∨' B
inj₂' q (¬p , ¬q) = ¬q q

case' : RAA C → (A → C) → (B → C) → A ∨' B → C
case' raar p→r q→r p∨q = raar λ ¬r → p∨q ((λ p → ¬r (p→r p)) , λ q → ¬r (q→r q))

∧' : RAA A → RAA B → RAA (A ∧ B)
proj₁ (∧' raap raaq ¬¬p∧q) = raap λ ¬p → ¬¬p∧q λ p∧q → ¬p (proj₁ p∧q)
proj₂ (∧' raap raaq ¬¬p∧q) = raaq λ ¬q → ¬¬p∧q λ p∧q → ¬q (proj₂ p∧q)

⇒' : RAA B → RAA (A → B)
⇒' raaq ¬¬p→q p = raaq λ ¬q → ¬¬p→q λ p→q → ¬q (p→q p)
