
import tactic

lemma test  (P: Prop) : ∀ P, ¬ ¬ (P ∨ ¬ P) :=
begin
 finish,
end
