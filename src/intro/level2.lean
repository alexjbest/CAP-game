import .level1 --hide
/-
We can state lemmas assuming hypotheses with similar notation as we made a lemma
dependent on natural numbers before.

The `rewrite` tactic can then be used to rewrite a hypothesis, after all we can substitute
things we know to be equal in facts we know as well as substituting into what we are trying to prove.

### Example:
You can use `rewrite` to change a hypothesis as well.
For example, if your goal state looks like this:
```
n m : ℕ
h1 : n + 1 = 7
h2 : m = n + 1
⊢ m + 2 = 9
```
then `rewrite h2 at h1` will turn `h1` into `h1 : m = 7`.

Below are two useful results you can use to finish this level.
-/

/- Axiom :
lemma add_zero : ∀ x, x + 0 = x
-/
lemma add_zero : ∀ x, x + 0 = x
:= nat.add_zero --hide
/- Axiom :
lemma one_mul : ∀ x, 1 * x = x
-/
lemma one_mul : ∀ x, 1 * x = x
:= nat.one_mul --hide

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rw h,` (don't forget the comma!). Lean tries `refl` afterwards,
so you will see that this suffices.
-/

/- Lemma : no-side-bar
-/
lemma level2 (x y : ℕ) (hx : x + 0 = 1 * y) : x + y = y + y :=
begin
  rw add_zero at hx,
  rw one_mul at hx,
  rw hx,



end
