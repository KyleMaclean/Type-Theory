-- developed with Agda version 2.6.2.1

open import library-of-propositional-logic

data Bool : Set where
  false : Bool
  true : Bool

-- definitions of quantification

record Σ (A : Set)(B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ
syntax Σ A (λ x → B)  = Σ[ x ∈ A ] B

infix 0 every
every : (A : Set)(B : A → Set) → Set
every A B = (x : A) → B x
syntax every A (λ x → B) = ∀[ x ∈ A ] B 

infix 0 exists
exists : (A : Set)(B : A → Set) → Set
exists A B = Σ[ x ∈ A ] B x
syntax exists A (λ x → B) = ∃[ x ∈ A ] B

-- proving the intuitionistic (i) truth of some predicated propositions

i1 : ({A B : Set}{C : A → B → Set} → 
      (∃[ y ∈ B ] (∀[ x ∈ A ] C x y)) → (∀[ x ∈ A ] (∃[ y ∈ B ] C x y))) 
i1 (b , ∀aλx→Cxb) a =  b , ∀aλx→Cxb a

i2 : ({A : Set}{B : A → Set} → 
      ¬ (∃[ x ∈ A ] B x) → ∀[ x ∈  A ] ¬ (B x))
i2 ¬∃ab a ba = ¬∃ab (a , ba)

i3 : ({A : Set}{B : A → Set} → 
      (∀[ x ∈ A ] ¬ (B x)) → ¬ (∃[ x ∈  A ] B x)) 
i3 ∀[x∈A]¬Bx (a , Ba) = ∀[x∈A]¬Bx a Ba

i4 : ({A : Set}{B : A → Set} → 
      (∃[ x ∈ A ] ¬ (B x)) → (¬ (∀[ x ∈ A ] B x)))
i4 (a , ¬ba) ∀ab = ¬ba (∀ab a)

i5 : ({A : Set}{B : A → Set} → 
      (¬ (¬ (∀[ x ∈ A ] B x))) → ∀[ x ∈  A ] ¬ (¬ (B x))) 
i5 ¬¬∀ab a ¬ba = ¬¬∀ab (λ ∀ab → ¬ba (∀ab a))

-- proving the falsity (f) of some predicated propositions by instantiating impossible cases

f1 : ({A B : Set}{C : A → B → Set} → 
      ((∀[ x ∈  A ] ∃[ y ∈ B ] C x y)) → (∃[ y ∈ B ] ∀[ x ∈ A ] C x y)) → ⊥ 
f1 h = lem (h {A = Bool} {B = Bool} {C = f})
      where 
            f : Bool → Bool → Set
            f true true = ⊥
            f false false = ⊥
            f false true = ⊤ 
            f true false = ⊤ 
            l : ((∀[ x ∈  Bool ] ∃[ y ∈ Bool ] f x y))
            l false = true , t
            l true = false , t
            r : ¬ (∃[ y ∈ Bool ] ∀[ x ∈ Bool ] f x y)
            r (false , proj₄) = proj₄ false
            r (true , proj₄) = proj₄ true
            lem : ¬ (((∀[ x ∈  Bool ] ∃[ y ∈ Bool ] f x y)) 
                  → (∃[ y ∈ Bool ] ∀[ x ∈ Bool ] f x y))
            lem p = r (p l)

f2 : ({A : Set}{B : A → Set} → 
      (∃[ x ∈ A ] ⊤) → (∃[ x ∈ A ] B x) → ∀[ x ∈ A ] B x) → ⊥
f2 h = lem (h {A = Bool} {B = f})
      where 
            f : Bool → Set 
            f false = ⊤
            f true = ⊥
            l : exists Bool (λ x₁ → ⊤)
            l = false , t
            rl : exists Bool (λ x₁ → f x₁)
            rl = false , t
            rr : ¬ (every Bool (λ x₁ → f x₁))
            rr x = x true
            r : ¬ (exists Bool (λ x₁ → f x₁) → every Bool (λ x₁ → f x₁))
            r x = rr (x rl)
            lem : ¬ ((∃[ x ∈ Bool ] ⊤) → (∃[ x ∈ Bool ] f x) → ∀[ x ∈ Bool ] f x)
            lem x = r (x l)

-- proving the classical (c) truth of some predicated propositions

c1 : ({A : Set} → RAA A) → 
      ({A : Set}{B : A → Set} → (¬ (∀[ x ∈ A ] B x)) → ∃[ x ∈ A ] ¬ (B x)) 
c1 raa ¬∀ab = raa λ ¬∃aλx→¬bx → ¬∀ab (λ a → raa λ ¬ba → ¬∃aλx→¬bx (a , ¬ba))

c2 : ({A : Set} → RAA A) → 
      ({A : Set}{B : A → Set} → (∀[ x ∈  A ] ¬ (¬ (B x))) → (¬ (¬ (∀[ x ∈ A ] B x))))
c2 raa ∀aλx→¬¬bx ¬∀ab = ¬∀ab λ a → raa (∀aλx→¬¬bx a)