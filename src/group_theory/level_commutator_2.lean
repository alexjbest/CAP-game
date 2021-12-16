import group_theory.level_commutator



/- Lemma
-/
lemma conjugate_self {G : Type*} [group G] {x : G} : x ^ x = x :=
begin
  rw [conjugate_def, inv_mul_self, one_mul],
end
