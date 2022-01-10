import .level_commutator_3

-- ex2
/- Lemma
-/
lemma commutator_mul {G : Type*} [group G] {x y z : G} : [x, z * y] = [x, y] * [x, z]^y :=
begin
  rw [commutator_def, commutator_def, commutator_def, conjugate_def, mul_inv_rev],
  assoc_rw [mul_inv_self],
  rw mul_one,
  assoc_rw [mul_inv_self],
  rw mul_one,
  simp [mul_assoc],
end
