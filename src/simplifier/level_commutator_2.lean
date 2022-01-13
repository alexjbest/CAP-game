import simplifier.level_commutator_1

/-
How far will simp get you here?
-/
namespace bloop--hide
@[simp]
lemma inv_mul_self {G : Type} [group G] (a : G) : a⁻¹ * a = 1
:= mul_left_inv a --hide
@[simp]
lemma one_mul {G : Type} [group G] (a : G) : 1 * a = a
:= one_mul _ --hide

end bloop--hide

/- Lemma :
-/
lemma conjugate_self {G : Type*} [group G] {x : G} : x ^ x = x :=
begin
  rw [conjugate_def, inv_mul_self, one_mul],



end
