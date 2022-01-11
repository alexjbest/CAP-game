import group_theory.level_commutator_2

/- Lemma :
-/
lemma commutator_inv {G : Type*} [group G] {x y : G} : [y, x] = [x, y]⁻¹ :=
begin
  rw [commutator_def, commutator_def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
    mul_assoc, mul_assoc],















end
