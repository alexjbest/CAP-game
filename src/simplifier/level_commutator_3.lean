import simplifier.level_commutator_2

/-
Here you might want to use `simp` together with the fact that multiplication is associative 
(this lemma is called `mul_assoc` as you might have guessed). Recall that you can tell 
`simp` to use lemma `h` when simplifying by writing `simp[h]`.  
-/

/- Lemma :
-/
lemma commutator_inv {G : Type*} [group G] {x y : G} : [y, x] = [x, y]⁻¹ :=
begin
  rw [commutator_def, commutator_def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
    mul_assoc, mul_assoc],















end
