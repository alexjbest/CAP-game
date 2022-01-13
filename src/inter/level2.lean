import topology.continuous_function.polynomial -- hide

/- # Using apply
In this problem you will show that a specific polynomial is continuous, you can do this using
the basic facts in the left sidebar: that adding continuous functions is continuous,
likewise multiplying continuous functions remains continuous, constant functions are continuous,
and the identity function is continuous. The way these lemmas are stated is very general, they work
for any continuous functions on arbitrary topological spaces, but by using `apply` we can let Lean
work out the details automatically.

But how do we talk about the functions themselves?
The basic method to speak about an unnamed function in Lean makes use of the lambda syntax.
In mathematics we might just write $x ^ 3 + 7$ to describe a polynomial function, leaving it
implicit that $x$ is the variable.
In Lean we use the symbol λ (`\lambda`) to describe a function by placing the name of the variable
after the lambda.
So `λ x, x^3 + 7` defines the function which takes input `x` and outputs `x^3 + 7` in Lean.

Watch out! Some of these lemmas have names with a dot like `continuous.add` (these ones
prove continuity of a combination of functions) and some have an underscore like
`continuous_const` (these ones state that some specific function is continuous).

-/
open polynomial-- hide
/- Axiom : Adding two continuous functions is continuous
continuous.add : ∀ {X M : Type} [topological_space X] [topological_space M] [has_add M]
  [has_continuous_add M] {f g : X → M},
  continuous f → continuous g → continuous (λ (x : X), f x + g x)
-/
/- Axiom : Multiplying two continuous functions is continuous
continuous.mul : ∀ {X M : Type} [topological_space X] [ topological_space M]
  [has_mul M] [has_continuous_mul M] {f g : X → M},
  continuous f → continuous g → continuous (λ (x : X), f x * g x)
-/
/- Axiom :
continuous.pow : ∀ {X M : Type} [topological_space X] [topological_space M] [monoid M]
  [has_continuous_mul M] {f : X → M},
  continuous f → ∀ (n : ℕ), continuous (λ (b : X), f b ^ n)
-/
/- Axiom : A constant function is continuous
continuous_const : ∀ {α β : Type} [topological_space α] [topological_space β] {b : β},
  continuous (λ (a : α), b)
-/
/- Axiom : The identity function is continuous
continuous_id : ∀ {α : Type} [topological_space α], continuous (λ x, x)
-/

/- Lemma : no-side-bar
-/
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
