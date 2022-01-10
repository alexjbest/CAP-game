import topology.continuous_function.polynomial

open polynomial
lemma poly_continuous : continuous (λ x : ℝ, 5 * x ^ 2 + x + 6) :=
begin
  apply continuous.add,
  apply continuous.add,
  apply continuous.mul,
  apply continuous_const,
  apply continuous.pow,
  apply continuous_id,
  apply continuous_id,
  apply continuous_const,



end