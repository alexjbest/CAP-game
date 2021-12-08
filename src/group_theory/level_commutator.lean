import group_theory.general_commutator

/-!
# Commutator identities

In these exercises we will write the proofs of the identities in
https://en.wikipedia.org/wiki/Commutator#Identities_(group_theory)
in the Lean interactive theorem prover.

-/
notation `[`x`, `y`]` := has_bracket.bracket x y
def commutator {G : Type*} [group G] : G → G → G := λ x y, x⁻¹ * y⁻¹ * x * y
instance group.has_bracket {G : Type*} [group G] : has_bracket G G := ⟨commutator⟩
def conjugate {G : Type*} [group G] : G → G → G := λ x y, y⁻¹ * x * y
instance group.has_pow {G : Type*} [group G] : has_pow G G := ⟨conjugate⟩
lemma commutator_def {G : Type*} [group G] {x y : G} : [x, y] = x⁻¹ * y⁻¹ * x * y := rfl
lemma conjugate_def {G : Type*} [group G] {x y : G} : y^x = x⁻¹ * y * x := rfl

/- Lemma
-/
lemma commutator_inv {G : Type*} [group G] {x y : G} : [y, x] = [x, y]⁻¹ :=
begin
  rw [commutator_def, commutator_def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
    mul_assoc, mul_assoc],
end


-- open tactic
-- meta def tactic.ac_refl' : tactic unit :=
-- do
--  (lhs, rhs) ← target >>= match_eq,
--    trace lhs,
--    s ← return $ cc_state.mk,
--    trace lhs,
--    s ← s.internalize lhs,
--    s ← s.internalize rhs,
--    trace lhs,
--    trace rhs,
--    b ← s.is_eqv lhs rhs,
--    trace $ s.pp_core ff,
--    trace b,
--    if b then do {
--      s.eqv_proof lhs rhs >>= exact
--    } else do {
--      fail "ac_refl failed"
--    }

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
  -- ac_refl, -- fails
end

-- ex3
/- Lemma
-/
lemma hall_witt {G : Type*} [group G] {x y z : G} :
  [[x, y⁻¹], z] ^ y * [[y, z⁻¹], x] ^ z * [[z, x⁻¹], y] ^ x = 1 :=
begin
  rw commutator_def,
  rw commutator_def,
  rw commutator_def,
  rw commutator_def,
  rw commutator_def,
  rw commutator_def,
  rw inv_inv,
  rw inv_inv,
  rw inv_inv,
  rw conjugate_def,
  rw conjugate_def,
  rw conjugate_def,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw mul_inv_rev,
  rw inv_inv,
  rw inv_inv,
  rw inv_inv,
  assoc_rw [inv_mul_self],
  assoc_rw [inv_mul_self],
  assoc_rw [inv_mul_self],
  -- group,
  simp [one_mul, mul_one],

end
