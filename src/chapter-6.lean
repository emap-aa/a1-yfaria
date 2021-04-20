import tactic
import data.list
import data.real.basic 
import init.function
open function


namespace Naturals

-- constant mynat : Type (versus)

inductive mynat : Type
 | z : mynat 
 | s : mynat → mynat

#check mynat.s $ mynat.s mynat.z

/--
It does not work

def exp1 (a : Type) (x : a) (n : ℕ) : a := x * (exp x (n - 1))

def exp2 {a : Type} [has_mul a] : a → ℕ → a  
 | x 0            := 1
 | x (nat.succ n) := x * exp1 x n
--/

def exp : ℕ → ℕ → ℕ   
 | x 0            := 1
 | x (nat.succ n) := x * exp x n

#print prefix exp

-- Exercicio A
-- https://leanprover-community.github.io/mathematics_in_lean/basics.html
example (x y z : ℕ) : (x + y) * z = (x * z) + (y * z) :=
begin
 ring,
end

example {x m n : ℕ} : exp x (m + n) = exp x m * exp x n := 
begin
 induction m with a ha,
 -- coluna 1
 rw zero_add,
 -- coluna 2
 rw exp,
 rw one_mul,
 -- norm_num,

 -- coluna 1
 rw nat.succ_add,
 rw exp, rw ha,

 -- coluna 2
 rw exp,
 rw mul_assoc,
end

end Naturals


namespace Lists

example {a : Type} {xs ys zs : list a} : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
begin
 induction xs with b hb,
 apply list.append.equations._eqn_1,
 sorry
end

def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def reverse { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse xs) ++ [x]


lemma rev_aux {a : Type } (x : a) (ys : list a) : reverse (ys ++ [x]) = x :: reverse ys :=
begin
 induction ys with b bs hi,
 simp [reverse, append],

 rw list.cons_append,
 rw reverse, 
 rw hi,
 rw reverse.equations._eqn_2, 
 rw list.cons_append,
end

theorem rev_rev_eq {a : Type} : ∀ xs : list a, reverse (reverse xs) = xs :=
begin
 intro xs,
 induction xs with b bs hi,
 simp [reverse,append],
 
 rw reverse,
 rw rev_aux,
 rw hi,
end


theorem rev_rev_id {a : Type} : (reverse ∘ reverse) = (id : list a → list a) :=
begin
 unfold comp, 
 funext,
 induction x with b bs hi,

 simp [reverse,append],
 
 rw reverse,
 rw rev_aux,
 rw hi, 
 unfold id, -- or simp
end


example (a b c : Type) (f : b → c) (g : a → b) (xs : list a) : 
 (map f ∘ map g) xs = map (f ∘ g) xs :=
begin
 unfold comp,
 induction xs with xa xha xhi,
 repeat { rw map },
 simp, 
 rw ← xhi,
end

example (a b c : Type) (f : b → c) (g : a → b) : 
 (map f ∘ map g) = map (f ∘ g) :=
begin
 unfold comp,
 funext,
 induction x with xa xha xhi,
 repeat { rw map },
 { simp, 
   rw ← xhi, },
end

-- #print list.cons_append

example {a b : Type} (f : a → b) [inhabited a] [inhabited b] : 
  list.head ∘ map f = f ∘ list.head :=
begin
 unfold comp,
 funext, 
 induction x with b bs hi, 
 rw list.head,
 rw map, rw list.head,
 sorry -- aparece que nao podemos provar sem saber mais sobre F
end


end Lists


namespace Foldr

def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def sum₁ : list ℕ → ℕ 
 | []        := 0
 | (x :: xs) := x + sum₁ xs 

def concat {a : Type} : list (list a) → list a 
 | []          := []
 | (xs :: xss) := xs ++ concat xss 

def filter {a : Type} : (a → bool) → list a → list a
 | p []         := []
 | p (x :: xs)  := if (p x) then (x :: filter p xs) else filter p xs


-- tests

#reduce concat [[1,2],[3,4],[5]]
#reduce sum₁ [0,1,2,3]
#reduce foldr (λ x y, x + y) 0 [1,2,3]
#reduce map (λ x : ℕ, x + 1) [1,2,3]
#reduce reverse [1,2,3]
#reduce filter (λ x, if x < 4 then tt else ff) [1,2,3,4]


theorem sum'_eq_sum'' {xs : list ℕ} : sum₁ xs = sum₂ xs := sorry


theorem sum_of_append {xs ys : list ℕ} : sum₁ (xs ++ ys) = sum₁ xs + sum₁ ys := sorry


theorem concat_of_apend { a : Type} {xss yss : list (list a)} : 
  concat (xss ++ yss) = concat xss ++ concat yss := sorry


theorem foldr_law {a b : Type} (f : a → b → b) (g : b → b → b) (e : b) (xs ys : list a) 
  (h1 : ∀ x, g e x = x) 
  (h2 : ∀ x y z, f x (g y z) = g (f x y) z) : 
  foldr f e (xs ++ ys) = g (foldr f e xs) (foldr f e ys) := sorry

end Foldr


namespace Fusion

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def map₁ {a b :Type} (g : a → b) : list a → list b := foldr ((::) ∘ g) []

def sum₂ : list ℕ → ℕ  := foldr (+) 0

def length := foldr (λ a b : ℕ, 1 + b) 0

def concat {a : Type} := foldr (++) ([] : list a)

def double (n : ℕ) := n + n


theorem funsion_law {a b : Type} (f : a → b) (g : b → a → a) (h : b → b → b) 
  (xa : a) (xb : b)
  (h1 : f xa = xb) 
  (h2 : ∀ x y, f (g x y) = h x (f y)) : 
  f ∘ foldr g xa = foldr h xb := 
begin
 funext xs,
 induction xs with d hd, 
 rw foldr, rw comp, dsimp, rw foldr, exact h1, 
 sorry
end


lemma funsion1 {α β : Type} (a : α) 
 (f :  β → α → α) (h : α → α → α) (g : α → β) 
 (h1 : foldr f a [] = a)
 (h2 : ∀ x y, foldr f a (((::) ∘ g) x y) = h x (foldr f a y))
 : foldr f a ∘ map₁ g = foldr h a := sorry


example {a : Type} (xs : list ℕ) : (double ∘ sum₂) xs = foldr ((+) ∘ double) 0 xs := sorry

example {a : Type} (xs : list a) : (length ∘ concat) = foldr ((+) ∘ length) 0 := sorry


end Fusion



namespace Foldl

def foldl {a b: Type} : (b → a → b) → b → list a → b 
 | f e [] := e
 | f e (x :: xs) := foldl f (f e x) xs

def flip {a b c : Type} : (a → b → c) → b → a → c 
 | f x y := f y x

def reverse₁ { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse₁ xs) ++ [x]

def reverse₂ {a : Type} := foldl (flip (::)) ([] : list a)

#reduce reverse₁ [1,2,3,4]


example : ∀ xs : list ℕ, reverse₁ xs = reverse₂ xs := sorry

end Foldl


namespace ExercicioF

def foldl {a b: Type} : (b → a → b) → b → list a → b 
 | f e [] := e
 | f e (x :: xs) := foldl f (f e x) xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def flip {a b c : Type} : (a → b → c) → b → a → c 
 | f x y := f y x

def reverse₁ { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse₁ xs) ++ [x]


-- completar tipos e condicoes extras

example : foldl f e xs = foldr (flip f) e (reverse₁ xs) := sorry

end ExercicioF


namespace mss

-- completar definicoes e tentar provar teorema, lemas adicionais
-- podem ser necessários.

def max : ℕ → ℕ → ℕ 
 | a b := if a >= b then a else b 

def maximum {x : ℕ} {xs : list ℕ} : list ℕ → ℕ 
 | []        := 0
 | (x :: xs) := max x (maximum xs)

def tails {a : Type} : list a → list (list a)
 | []  := [[]]
 | (x :: xs) := (x::xs) :: tails xs


def segments {a : Type} : list a := concat ∘ map inits ∘ tails

def mss₁ := maximum ∘ map sum ∘ segments


def mss₂ := 
  let f x y := max 0 (x + y) in maximum . scanr f 0 


theorem mss_eq : mss₁ = mss₂ := sorry

end mss

