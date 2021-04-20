import tactic
import data.list
import data.real.basic 
import init.function
open function


-- constant mynat : Type (versus)

inductive mynat : Type
 | z : mynat 
 | s : mynat → mynat

#check mynat.s $ mynat.s mynat.z


/--
def exp1 (a : Type) (x : a) (n : ℕ) : a := x * (exp x (n - 1))

def exp2 {a : Type} [has_mul a] : a → ℕ → a  
 | x 0            := 1
 | x (nat.succ n) := x * exp1 x n
--/

def exp : ℕ → ℕ → ℕ   
 | x 0            := 1
 | x (nat.succ n) := x * exp x n


-- #print prefix exp

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


example {a : Type} {xs ys zs : list a} : (xs ++ ys) ++ zs = xs ++ (ys ++ zs) :=
begin
 induction xs with b hb,
 apply list.append.equations._eqn_1,
 
 sorry
end


-- page 112

def reverse { a : Type } : list a -> list a
| []      := []
| (x::xs) := (reverse xs) ++ [x]

def map {a b : Type} : (a → b) → list a → list b
| f [] := []
| f (x :: xs) := f x :: map f xs

def foldr {a b: Type} : (a → b → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := f x (foldr f e xs)

def foldl {a b: Type} : (b → a → b) → b → list a → b 
| f e [] := e
| f e (x :: xs) := foldl f (f e x) xs


#reduce foldr (λ x y, x + y) 0 [1,2,3]
#reduce map (λ x : ℕ, x + 1) [1,2,3]
#reduce reverse [1,2,3]

theorem map_distr_comp₁ (a b c : Type) (f : b → c) (g : a → b) (xs : list a) : 
 (map f ∘ map g) xs = map (f ∘ g) xs :=
begin
 unfold comp,
 induction xs with xa xha xhi,
 repeat { rw map },
 simp, 
 rw ← xhi,
end

theorem map_distr_comp₂ (a b c : Type) (f : b → c) (g : a → b) : 
 (map f ∘ map g) = map (f ∘ g) :=
begin
 unfold comp,
 funext,
 induction x with xa xha xhi,
 repeat { rw map },
 { simp, 
   rw ← xhi, },
end

#print list.cons_append


-- Exercicio B

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


theorem rev_rev_eq {a : Type} (xs : list a) : reverse (reverse xs) = xs :=
begin
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


-- Exercicio C 

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

-- Exercicio F

lemma foldr_atom_flip {a : Type} (f : a → a → a) (e : a) (x : a) : foldr (flip f) e [x] = f e x :=
begin
 rw foldr,
 rw foldr,
 rw flip
end

lemma foldr_atom {a : Type} (f : a → a → a) (e : a) (x : a) : foldr f e [x] = f x e :=
begin
 rw foldr,
 rw foldr
end

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

theorem rev_foldl_foldr1 {a : Type} (f : a → a → a) (e : a) (xs : list a) : foldl f e xs = foldr (flip f) e (reverse xs) :=
begin
 induction xs with x xs hs,
 
 rw foldl,
 rw reverse, 
 rw foldr,

 rw foldl, 
 rw reverse,
 rw foldr_open_tail,
 rw flip_,
 sorry
end

theorem rev_foldl_foldr2 {a : Type} (f : a → a → a) (xs : list a) : ∀ e : a, foldl f e xs = foldr (flip f) e (reverse xs) :=
begin
 induction xs with x xs hs,
 intro e,
 rw foldl,
 rw reverse, 
 rw foldr,

 intro,

 rw foldl, 
 rw reverse,
 rw foldr_open_tail,
 rw flip_,
 apply hs (f e x)
end

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
