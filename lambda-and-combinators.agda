-- developed with Agda version 2.6.2.1

variable A B C : Set

-- combinator definitions

K : A → B → A
K = λ a → λ b → a

S : (A → B → C) → (A → B) → A → C
S = λ f → λ g → λ x → f x (g x)

I : A → A
I {A} = S K (K {B = A})

{-
functions are defined with λ-abstraction () and then combinators only (').
the derivation is accomplished using these translations:
    λ x → x         I
    λ x → M₁ M₂     S (λ x → M₁) (λ x → M₂)
    λ x → M         K M
    λ x → f x       f
-}

v : (A → A → B) → (A → B)
v = λ f → λ a → f a a
v' : (A → A → B) → (A → B)
-- v' = λ f → λ a → f a a
-- v' = λ f → S (λ a → f a) (λ a → a)
-- v' = λ f → S (λ a → f a) I
-- v' = λ f → S f I
-- v' = S (λ f → S f) (λ f → I)
-- v' = S (λ f → S f) (K I)
v' = S S (K I)

w : (A → B → C) → B → A → C 
w = λ f → λ x → λ y → f y x 
w' : (A → B → C) → B → A → C 
-- w' = λ f → λ x → λ y → (f y) x 
-- w' = λ f → λ x → S (λ y → (f y)) (λ y → x) 
-- w' = λ f → λ x → S (λ y → (f y)) (K x) 
-- w' = λ f → λ x → (S (λ y → (f y))) (K x) 
-- w' = λ f → S (λ x → (S (λ y → (f y)))) (λ x → K x) 
-- w' = λ f → S (K (S (λ y → (f y)))) (λ x → K x) 
-- w' = λ f → S (K (S (λ y → (f y)))) K 
-- w' = λ f → S (K (S (f))) K 
-- w' = S (λ f → S (K (S (f)))) (λ f → K) 
-- w' = S (λ f → S (K (S (f)))) (K K) 
-- w' = S (S (λ f → S) (λ f → (K (S (f))))) (K K)
-- w' = S (S (K S) (λ f → (K (S (f))))) (K K)
-- w' = S (S (K S) (λ f → K (S f))) (K K)
-- w' = S (S (K S) (S (λ f → K) (λ f → S f))) (K K)
-- w' = S (S (K S) (S (K K) (λ f → S f))) (K K)
w' = S (S (K S) (S (K K) (S))) (K K)

x : A → ((A → B) → B)
x = λ a → λ f → f a
x' : A → ((A → B) → B)
-- x' = λ a → S (λ f → f) (λ f → a)
-- x' = λ a → S I (λ f → a)
-- x' = λ a → S I (K a)
-- x' = S (λ a → S I) (λ a → K a)
-- x' = S (K (S I)) (λ a → K a)
x' = S (K (S I)) K

y : (A → B) → (A → A → B)
y = λ f → λ a → λ _ → f a
y' : (A → B) → (A → A → B)
-- y' = λ f → λ a → K (f a)
-- y' = λ f → S (λ a → K) (λ a → f a)
-- y' = λ f → S (K K) (λ a → f a)
-- y' = λ f → S (K K) f
y' = S (K K)

z : (A → B) → ((A → C) → C) → ((B → C) → C)
z = λ f → λ g → λ h → g λ a → h (f a)
z' : (A → B) → ((A → C) → C) → ((B → C) → C)
-- z' = λ f → λ g → λ h → g (λ a → h (f a))
-- z' = λ f → λ g → λ h → g (S (λ a → h) (λ a → f a))
-- z' = λ f → λ g → λ h → g (S (K h) (λ a → f a))
-- z' = λ f → λ g → λ h → g (S (K h) f)
-- z' = λ f → λ g → S (λ h → g) (λ h → (S (K h) f))
-- z' = λ f → λ g → S (K g) (λ h → (S (K h) f))
-- z' = λ f → λ g → S (K g) (λ h → S (K h) f)
-- z' = λ f → λ g → S (K g) (λ h → (S (K h)) f)
-- z' = λ f → λ g → S (K g) (S (λ h → (S (K h))) (λ h → f))
-- z' = λ f → λ g → S (K g) (S (λ h → (S (K h))) (K f))
-- z' = λ f → λ g → S (K g) (S (λ h → S (K h)) (K f))
-- z' = λ f → λ g → S (K g) (S (S (λ h → S) (λ h → K h)) (K f))
-- z' = λ f → λ g → S (K g) (S (S (K S) (λ h → K h)) (K f))
-- z' = λ f → λ g → S (K g) (S (S (K S) K) (K f))
-- z' = λ f → S (λ g → S (K g)) (λ g → S (S (K S) K) (K f))
-- z' = λ f → S (λ g → S (K g)) (K (S (S (K S) K) (K f)))
-- z' = λ f → S (S (λ g → S) (λ g → K g)) (K (S (S (K S) K) (K f)))
-- z' = λ f → S (S (λ g → S) K) (K (S (S (K S) K) (K f)))
-- z' = λ f → S (S (K S) K) (K (S (S (K S) K) (K f)))
-- z' = S (λ f → S (S (K S) K)) (λ f → (K (S (S (K S) K) (K f))))
-- z' = S (K (S (S (K S) K))) (λ f → (K (S (S (K S) K) (K f))))
-- z' = S (K (S (S (K S) K))) (λ f → K (S (S (K S) K) (K f)))
-- z' = S (K (S (S (K S) K))) (S (λ f → K) (λ f → S (S (K S) K) (K f)))
-- z' = S (K (S (S (K S) K))) (S (K K) (λ f → S (S (K S) K) (K f)))
-- z' = S (K (S (S (K S) K))) (S (K K) (S (λ f → S (S (K S) K)) (λ f → K f)))
-- z' = S (K (S (S (K S) K))) (S (K K) (S (K (S (S (K S) K))) (λ f → K f)))
z' = S (K (S (S (K S) K))) (S (K K) (S (K (S (S (K S) K))) K))
 