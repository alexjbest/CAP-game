import group_theory.level_commutator_1

namespace bloop--hide
lemma inv_mul_self {G : Type} [group G] (a : G) : a⁻¹ * a = 1
:= mul_left_inv a --hide
lemma one_mul {G : Type} [group G] (a : G) : 1 * a = a
:= one_mul _ --hide

end bloop--hide

/- Lemma :
-/
lemma conjugate_self {G : Type*} [group G] {x : G} : x ^ x = x :=
begin
  rw [conjugate_def, inv_mul_self, one_mul],



end
