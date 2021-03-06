-- import group_theory.level1 --hide


/-
# Level 2: Union of two open sets
-/

/- Lemma
The union of two open sets is open.
-/
-- lemma open_of_union {X : Type} [topological_space X] {U V : set X}
-- (hU : is_open U) (hV : is_open V): is_open (U ∪ V) :=
-- begin
--   let I : set (set X) := {U, V},
--   have H : ⋃₀ I = U ∪ V := sUnion_pair U V,
--   rw ←H,
--   apply union I,
--   intros B hB,
--   replace hB : B = U ∨ B = V, by tauto,
--   cases hB; {rw hB, assumption},




-- end
