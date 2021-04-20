import tactic
import data.list
import data.real.basic 
import init.function
open function


def splitAt1 {a : Type} : ℕ → (list a) → (list a × list a)
 |              0 xs := ([], xs)
 |              _ [] := ([], [])
 | (n + 1) (x :: xs) := (x :: (splitAt1 n xs).1, (splitAt1 n xs).2)

def splitAt2 {a : Type} : ℕ → (list a) → (list a × list a) 
 |                   0 xs := ([], xs)
 |                   _ [] := ([], [])
 | (nat.succ n) (x :: xs) := let (ys,zs) := splitAt2 n xs in (x :: ys, zs)

#reduce splitAt2 2 [1,2,3,4]
#reduce splitAt1 2 [1,2,3,4]

example : splitAt1 2 [1,2,3,4] = ([1,2],[3,4]) :=
begin
  rw splitAt1,
  rw splitAt1, 
  rw splitAt1, -- como fazer passo-a-passo
end

example (a : Type) (n : ℕ) (xs : list a) :
 (λ x, (prod.fst x) ++ (prod.snd x) = xs) (splitAt1 n xs) :=
begin
  induction xs with d hd IH generalizing n,
  { induction n with m hm;
    simp [splitAt1], },
  { induction n with m hm,
    { simp [splitAt1], },
    { simp [splitAt1, IH, hm], } }
end

-- #print prefix splitAt1

example : splitAt2 2 [1,2,3,4] = ([1,2],[3,4]) := 
begin
 rw splitAt2, 
 rw splitAt2, 
 rw splitAt2,
 rw splitAt2._match_1,
 rw splitAt2._match_1,
end

  
example (a : Type) (n : ℕ) (xs : list a) : 
 (λ x, (prod.fst x) ++ (prod.snd x) == xs) (splitAt2 n xs) :=
begin
 induction xs with d hd ih generalizing n,
 induction n with m hm,
 simp [splitAt2],
 simp [splitAt2],
 
 induction n with m hm,
 simp [splitAt2],
 have h2 := ih m,
 simp [splitAt2, hm, h2, splitAt2._match_1], 
 sorry
end




