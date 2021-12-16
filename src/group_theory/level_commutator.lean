import algebra.group.basic
import data.bracket
/- Tactic : rw

## Summary

If `h` is a proof of `X = Y`, then `rw h,` will change
all `X`s in the goal to `Y`s.

Variants: `rw ← h` changes
`Y` to `X` and
`rw h at h2` changes `X` to `Y` in hypothesis `h2` instead
of the goal.

## Details

The `rw` tactic is a way to do "substituting in". There
are two distinct situations where use this tactics.

1) If `h : A = B` is a hypothesis (i.e., a proof of `A = B`)
in your local context (the box in the top right)
and if your goal contains one or more `A`s, then `rw h`
will change them all to `B`'s.

2) The `rw` tactic will also work with proofs of theorems
which are equalities (look for them in the drop down
menu on the left, within Theorem Statements).

Important note: if `h` is not a proof of the form `A = B`
or `A ↔ B` (for example if `h` is a function, an implication,
or perhaps even a proposition itself rather than its proof),
then `rw` is not the tactic you want to use. For example,
`rw (P = Q)` is never correct: `P = Q` is the true-false
statement itself, not the proof.
If `h : P = Q` is its proof, then `rw h` will work.

Pro tip 1: If `h : A = B` and you want to change
`B`s to `A`s instead, try `rw ←h` (get the arrow with `\l`,
note that this is a small letter L, not a number 1).

### Example:
If it looks like this in the top right hand box:
```
A B C : set X
h : A = B ∪ C
⊢ A ∪ B = B ∪ C
```

then

`rw h,`

will change the goal into `⊢ B ∪ C ∪ B = B ∪ C`.

### Example:
You can use `rw` to change a hypothesis as well.
For example, if your local context looks like this:
```
A B C D : set X
h1 : A = B ∩ C
h2 : B ∪ A = D
⊢ D = B
```
then `rw h1 at h2` will turn `h2` into `h2 : B ∪ B ∩ C = D` (remember operator precedence).
-/


/-
The next tactic we will learn is *rw* (from rewrite). It rewrites equalities. That is,
if we have a proof `h : x = 3` and we want to prove `⊢ x + 1 = 4`, then after `rw h` the goal
will become `⊢ 3 + 1 = 4`, which seems reasonable.

-/

/-
# Commutator identities

In these exercises we will write the proofs of the identities in
https://en.wikipedia.org/wiki/Commutator#Identities_(group_theory)
in the Lean interactive theorem prover.

-/
notation `[`x`, `y`]` := has_bracket.bracket x y -- hide
def commutator {G : Type*} [group G] : G → G → G := λ x y, x⁻¹ * y⁻¹ * x * y
instance group.has_bracket {G : Type*} [group G] : has_bracket G G := ⟨commutator⟩ -- hide
def conjugate {G : Type*} [group G] : G → G → G := λ x y, y⁻¹ * x * y
instance group.has_pow {G : Type*} [group G] : has_pow G G := ⟨conjugate⟩ -- hide
/- Axiom : The definition of commutator
commutator_def : [x, y] = x⁻¹ * y⁻¹ * x * y
-/
lemma commutator_def {G : Type*} [group G] {x y : G} : [x, y] = x⁻¹ * y⁻¹ * x * y := rfl
/- Axiom : The definition of conjugate
conjugate_def : y^x = x⁻¹ * y * x := rfl
-/
lemma conjugate_def {G : Type*} [group G] {x y : G} : y^x = x⁻¹ * y * x := rfl

/- Lemma
-/
lemma commutator_self {G : Type*} [group G] {x : G} : [x, x] = 1 :=
begin
  rw [commutator_def, inv_mul_cancel_right, inv_mul_self],
end

/- Lemma
-/
lemma conjugate_self {G : Type*} [group G] {x : G} : x ^ x = x :=
begin
  rw [conjugate_def, inv_mul_self, one_mul],
end

/- Lemma
-/
lemma commutator_inv {G : Type*} [group G] {x y : G} : [y, x] = [x, y]⁻¹ :=
begin
  rw [commutator_def, commutator_def, mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv,
    mul_assoc, mul_assoc],
end
