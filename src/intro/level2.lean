import .level1 --hide
/-
We can state lemmas assuming hypotheses with similar notation as we made a lemma
dependent on natural numbers before.

The `rewrite` tactic can then be used to rewrite a hypothesis, after all we can substitute
things we know to be equal in facts we know as well as things we are trying to prove.

### Example:
You can use `rewrite` to change a hypothesis as well.
For example, if your goal state looks like this:
```
A B C D : set X
h1 : A = B ∩ C
h2 : B ∪ A = D
⊢ D = B
```
then `rw h1 at h2` will turn `h2` into `h2 : B ∪ B ∩ C = D` (remember operator precedence).
-/

/- Axiom : The commutativity of addition
add_comm : ∀ x y, x + y = y + x
-/

/-
The next tactic we will learn is *rw* (from rewrite). It rewrites equalities. That is,
if we have a proof `h : x = 3` and we want to prove `⊢ x + 1 = 4`, then after `rw h` the goal
will become `⊢ 3 + 1 = 4`, which seems reasonable.

-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rw h,` (don't forget the comma!). Lean tries `refl` afterwards,
so you will see that this suffices.
-/

lemma level2 (x y : ℕ) (hx : x + 0 = 1 * y) : x + y = y + y :=
begin
  rw add_zero at hx,
  rw one_mul at hx,
  rw hx,



end
