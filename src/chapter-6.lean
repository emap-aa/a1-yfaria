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

#print list.cons_append

example {a : Type} {xs ys zs : list a} : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
begin
 induction xs with b hb,
 apply list.append.equations._eqn_1,
 rw list.cons_append,
 rw list.cons_append,
 rw list.cons_append,
 rw xs_ih
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

def sum₂ : list ℕ → ℕ  := foldr (+) 0

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



theorem sum'_eq_sum'' {xs : list ℕ} : sum₁ xs = sum₂ xs := 
begin
 induction xs with x xs h,
 rw sum₁,
 rw sum₂,
 rw foldr,

 rw sum₁,
 rw sum₂,
 rw foldr,
 rw← sum₂,
 rw h,
end


theorem sum_of_append {xs ys : list ℕ} : sum₁ (xs ++ ys) = sum₁ xs + sum₁ ys := 
begin
 induction xs with x xs h,
 rw sum₁,
 -- apply list.append.equations._eqn_1,
 dsimp,
 rw nat.zero_add,
 
 rw sum₁,
 dsimp,
 rw sum₁,
 rw h,
 rw nat.add_assoc
end


theorem concat_of_apend { a : Type} {xss yss : list (list a)} : 
  concat (xss ++ yss) = concat xss ++ concat yss :=
begin
 induction xss with xs xss hx,
 rw concat,
 simp,
   
 rw concat,
 simp,
 rw concat,
 rw hx
end


theorem foldr_law {a b : Type} (f : a → b → b) (g : b → b → b) (e : b) (xs ys : list a) 
  (h1 : ∀ x, g e x = x) 
  (h2 : ∀ x y z, f x (g y z) = g (f x y) z) : 
  foldr f e (xs ++ ys) = g (foldr f e xs) (foldr f e ys) :=
begin
 induction xs with x xs hx,
 rw foldr,
 dsimp,
 rw h1,

 rw foldr,
 dsimp,
 rw foldr,
 rw← h2,
 rw hx
end

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
 
 rw comp, 
 dsimp,
 rw foldr,
 rw foldr,
 rw h2,
 rw comp at xs_ih,
 dsimp at xs_ih,
 rw xs_ih

end


lemma funsion2 {α β : Type} (a : α) 
 (f :  β → α → α) (g : α → β)
 : foldr f a ∘ map₁ g = foldr (f ∘ g) a :=
begin
 rw map₁,
 dsimp,
 rw funsion_law,
 rw foldr,
 intro x,
 intro ys,
 rw comp,
 dsimp,
 rw foldr
end

/-
Relendo, acho que isso até faz sentido mas queríamos o resultado acima.

lemma funsion1 {α β : Type} (a : α) 
 (f :  β → α → α) (h : α → α → α) (g : α → β) 
 (h1 : foldr f a [] = a)
 (h2 : ∀ x y, foldr f a (((::) ∘ g) x y) = h x (foldr f a y))
 : foldr f a ∘ map₁ g = foldr h a :=
begin
 rw map₁,
 dsimp,
 rw funsion_law,
 exact h1,
 exact h2,
end
-/

example {a : Type} (xs : list ℕ) : (double ∘ sum₂) xs = foldr ((+) ∘ double) 0 xs := 
begin
 rw sum₂,
 rw funsion_law,
 rw double,
 rw comp,
 dsimp,
 intro x,
 intro y,
 rw double,
 rw double,
 rw double,
 ring -- comutatividade e associatividade da soma.
end

/-
O livro fala pra usar a fusion law aqui, mas não é tão simples.
Para a lei precisaríamos de colocar f = length, g = (++) e h = ((+) ∘ length),
mas quando formulamos nossa restrição é f: a → b - então a seria o nosso list ℕ e b seria ℕ - e g : b → a → a , e essa tipagem já quebra o que queríamos fazer pois a função append recebe duas listas de um mesmo tipo.
example (xs : list ℕ) : (length ∘ concat) = foldr ((+) ∘ length) 0 := 
begin
 rw concat,
 rw funsion_law length (++) ,
 sorry
end
-/

lemma sum_lengths (xs ys : list ℕ): 
length (xs ++ ys) = length xs + length ys :=
begin
 rw length, dsimp,
 induction xs with x xs h,
 rw foldr,
 dsimp,
 rw zero_add,
 
 rw foldr,
 rw list.cons_append,
 rw foldr,
 rw h,
 ring
end

example (xs : list ℕ) : (length ∘ concat) = foldr ((+) ∘ length) 0 := 
begin
 rw concat,
 funext xss,
 induction xss with xs xss h,
 
 rw comp,
 dsimp,
 rw comp,
 rw foldr,
 rw length,
 rw foldr,
 rw foldr,

 rw comp, dsimp,
 rw foldr,
 rw foldr,
 rw← h,
 rw comp, dsimp,
 rw sum_lengths
end


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

lemma rev2_eq : ∀ x: ℕ, ∀ xs : list ℕ , reverse₂ xs ++ [x] = reverse₂ (x :: xs) :=
begin
 rw reverse₂, dsimp,
 intro x, intro xs,
 rw foldl, rw flip,
 induction xs with y ys h,
 rw foldl, rw foldl, dsimp, refl,
 rw foldl, rw foldl, rw flip, rw flip,
 sorry
end

example : ∀ xs : list ℕ, reverse₁ xs = reverse₂ xs := 
begin
 intro xs,
 induction xs with x xs h,
 rw reverse₂, dsimp, rw reverse₁, rw foldl,

 rw reverse₁,
 rw h,
 rw rev2_eq, -- falta provar.
 -- rw foldl,
 -- rw flip,
 -- rw h,
 -- sorry
end

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
lemma foldr_atom_flip {a : Type} (f : a → a → a) (e : a) (x : a) : foldr (flip f) e [x] = f e x :=
begin
 rw foldr,
 rw foldr,
 rw flip
end

lemma foldr_atom {a : Type} (f : a → a → a) (e : a) (x : a) : 
foldr f e [x] = f x e := begin rw foldr, rw foldr end

lemma foldr_open_tail {a : Type} (f : a → a → a) (e : a) (x : a) (xs : list a): foldr f e (xs ++ [x]) = foldr f (f x e) xs :=
begin
 induction xs with y ys hs,
 simp,
 rw foldr_atom,
 rw foldr,
 
 rw foldr,
 rw← hs,
 refl
end


lemma flip_ {a : Type} (x : a) (e : a) (f: a → a → a): flip f x e = f e x := 
by refl

theorem rev_foldl_foldr1 {a : Type} (f : a → a → a) (e : a) (xs : list a) : foldl f e xs = foldr (flip f) e (reverse₁ xs) :=
begin
 induction xs with x xs hs,
 
 rw foldl,
 rw reverse₁, 
 rw foldr,

 rw foldl, 
 rw reverse₁,
 rw foldr_open_tail,
 rw flip_,
 sorry -- o que não consegui
end

theorem rev_foldl_foldr2 {a : Type} (f : a → a → a) (xs : list a) : ∀ e : a, foldl f e xs = foldr (flip f) e (reverse₁ xs) :=
begin
 induction xs with x xs hs,
 intro e,
 rw foldl,
 rw reverse₁, 
 rw foldr,

 intro,

 rw foldl, 
 rw reverse₁,
 rw foldr_open_tail,
 rw flip_,
 apply hs (f e x)
end

/- Incompleto da segunda pergunta:

theorem foldeq {a : Type} (f g : a → a → a) (e : a) (xs : list a) : (∀ x y z, g (f x y) z = f x (g y z)) → (∀ x, g e x = f x e) → foldl g e xs = foldr f e xs :=
begin 
 intro h1,
 intro h2,
 induction xs with x xs hs,

 refl,
 
 rw foldl,
 rw h2 x,
 rw foldr,
 rw← hs,

--    using the book:
 induction xs with y ys hs2,
 rw foldl,
 rw foldl,
 
 rw foldl,
 rw h1,
 rw h2,
 
 rw foldl,
 sorry
end

theorem foldeq2 {a : Type} (f g : a → a → a) (xs : list a) : (∀ x y z, g (f x y) z = f x (g y z)) → (∀ x e, g e x = f x e) → ∀ e, foldl g e xs = foldr f e xs :=
begin 
 intro h1,
 intro h2,
 induction xs with x xs hs,

 intro,
 unfold foldl,
 unfold foldr,
 
 unfold foldl,
 specialize h2 x,
 intro e,
 rw h2,
 rw foldr,
 rw← hs,

-- using the book:

 induction xs with z zs hs2,
 rw foldl,
 rw foldl,
 
 rw foldl,
 rw h1,
 rw foldl,

 
end

lemma foldeq2_aux {a : Type} (f g : a → a → a) (ys : list a) : ∀ y, 
  (∀ (e : a), foldl g e (y :: ys) = foldr f e (y :: ys))
    → (∀ (e : a), foldl g e ys = foldr f e ys) :=
begin
  intro y,
  intro h,
  induction ys with z zs hs,
  unfold foldl,
  unfold foldr,
  intro e,
  refl,
  
  unfold foldl at h,
  unfold foldr at h,
  
  
end


-/

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

def foldr {a b : Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def map {a b : Type} (g : a → b) : list a → list b := foldr ((::) ∘ g) []

def concat {a : Type} := foldr (++) ([] : list a)

def inits {a : Type} : list a → list (list a)
| [] := [[]]
| (x :: xs) := [] :: (map ((::) x) (inits xs))

def segments: list ℕ → list (list ℕ) := concat ∘ map inits ∘ tails

def scanr {a b : Type} [inhabited b]: (a → b → b) → b → list a → list b
| f e [] := [e]
| f e (x :: xs) := f x (list.head $ scanr f e xs) :: (scanr f e xs)
 
#check list.head

#check map list.sum ∘ segments

#check maximum ∘ (map list.sum ∘ segments) 

#reduce list.maximum $ ((map list.sum ∘ segments)) [1,5,6,9,10]

#reduce max 78 2

-- Não sei o erro de maximum ∘ (map list.sum ∘ segments), mas não avalia

def mss₁ := 
list.maximum ∘ map list.sum ∘ segments

def mss₂ := list.maximum ∘ scanr (λ x y, max 0 (x+y)) 0 

theorem mss_eq : mss₁ = mss₂ := 
begin
 funext xs,
 rw mss₁,
 rw mss₂,
 induction xs with x xs h,
 rw comp, dsimp,
 rw segments, rw comp, dsimp, rw tails,
 rw map, dsimp, rw map, dsimp, rw foldr, rw foldr, rw comp, dsimp, rw concat,
 rw foldr, rw inits, rw foldr, dsimp, rw foldr, rw foldr, simp,
 rw scanr, simp,

 sorry
end
end mss
