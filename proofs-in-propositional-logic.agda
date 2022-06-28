-- developed with Agda version 2.6.2.1

open import library-of-propositional-logic

variable A B C : Set

-- proving the intuitionistic (i) truth of some propositions

i1 : (A ⇒ B) ⇒ ¬ B ⇒ ¬ A
i1 p⇒q ¬q p = ¬q (p⇒q p)

i2 : ¬ (A ⇔ ¬ A)
i2 (p⇒¬p , ¬p⇒p) = p⇒¬p (¬p⇒p λ p → p⇒¬p p p) (¬p⇒p λ p → p⇒¬p p p)

i3 :  ¬ (¬ (¬ A)) ⇒ ¬ A
i3 ¬¬¬p p = ¬¬¬p λ ¬p → ¬p p

-- proving the classical (c) truth of some propositions

postulate
  raa : ¬ ¬ A ⇒ A -- reductio ad absurdo
  tnd : A ∨ ¬ A -- tertium non datur

c1 : ((A ⇒ B) ⇒ A) ⇒ A
c1 x = raa (λ ¬p → ¬p (x (λ p → case⊥ (¬p p))))
  where
    case⊥ : ⊥ → A 
    case⊥ ()

c2 : (A ⇒ B) ⇒ ¬ A ∨ B
c2 {A} p→q with tnd {A}
... | inj₁ p = inj₂ (p→q p)
... | inj₂ p→⊥ = inj₁ p→⊥

c3 : (¬ (¬ A) ⇒ A) ⇒ A ∨ ¬ A
c3 _ = raa ¬¬a∨¬a
  where
    ¬¬a∨¬a : ¬ ¬ (A ∨ ¬ A)
    ¬¬a∨¬a x = x (inj₂ (λ a → x (inj₁ a)))

c4 : A ∨ ¬ A ⇒ (¬ (¬ A) ⇒ A)
c4 _ ¬¬p = raa ¬¬p

c5 : ¬ A ∨ B ⇒ (A ⇒ B)
c5 (inj₁ ¬p) p = raa λ y → ¬p p
c5 (inj₂ q) p = q

-- proving the falsity (f) of some propositions by instantiating impossible cases

f1 : ({A : Set} → ¬ (A ∨ ¬ A)) → ⊥
f1 h = h {⊤} (inj₁ t)

f2 : ({A B : Set} → (A ⇒ B) ⇒ ¬ A ⇒ ¬ B) → ⊥ 
f2 h = h {⊥} {⊤} (λ ⊥_ → t) (λ ⊥_ → ⊥_) t