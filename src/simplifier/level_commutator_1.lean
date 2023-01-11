import algebra.group.basic
import data.bracket

/- # The simplifier
Up till now we have been using `rewrite` to manually instruct Lean which steps to take one at a time.
This is a very useful tool, but after a while you will notice that there are some rewrites that
will always make things easier when substituted.
For example we almost always want to use the fact that multiplying by 1 or adding 0 doesn't
change things.
-/

/- Tactic : simp

## Summary

The `simp` tactic is a high-level tactic which tries
to prove equalities using facts in its database.

## Details

The `simp` tactic does basic automation.
For example, some proofs involve a tedious number of rewrites of `add_assoc` and `add_comm`, 
the same is true of `mul_assoc` and `mul_comm` in the case of multiplication. 
We can use `simp` to do this automatically. 
To tell `simp` to use some lemma `h` when simplifying, write `simp[h]`. More generally, 
for `simp` to include additional lemmas `h1`, `h2`, ..., `hn` when simplifying, write 
`simp[h1, h2, ..., hn]`. 

### Example:
If our goal is this:
```
⊢ a + b + c + d + e = a + (b + (c + d) + e)
```

we can solve this with `simp` using `simp[add_assoc]`. 

### Example:
If our goal is this:
```
⊢ a * b * c = c * b * a
```
-/
/-


# Commutator identities

In these exercises we will write the proofs of the identities in
<https://en.wikipedia.org/wiki/Commutator#Identities_(group_theory)>
in Lean.

First we will set up the basic definitions, in World 1, we didn't make any new mathematical
definitions, we just made use of the natural numbers, propositions, and some lemmas Lean
already knew about.

-/
notation `[`x`, `y`]` := has_bracket.bracket x y -- hide
definition commutator {G : Type*} [group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y
instance group.has_bracket {G : Type*} [group G] : has_bracket G G := ⟨commutator⟩ -- hide
definition conjugate {G : Type*} [group G] (x y : G) : G := y⁻¹ * x * y
instance group.has_pow {G : Type*} [group G] : has_pow G G := ⟨conjugate⟩ -- hide
/- Axiom : The definition of commutator
commutator_def : [x, y] = x⁻¹ * y⁻¹ * x * y
-/
lemma commutator_def {G : Type*} [group G] {x y : G} : [x, y] = x⁻¹ * y⁻¹ * x * y := rfl
/- Axiom : The definition of conjugate
conjugate_def : y^x = x⁻¹ * y * x := rfl
-/
lemma conjugate_def {G : Type*} [group G] {x y : G} : y^x = x⁻¹ * y * x := rfl

/- Axiom : cancelling inverses on the right
inv_mul_cancel_right : ∀ {G : Type} [_inst_1 : group G] (a b : G), a * b⁻¹ * b = a
-/

/- Axiom : cancelling an element with its own inverse
inv_mul_self : ∀ {G : Type} [_inst_1 : group G] (a : G), a⁻¹ * a = 1
-/

/-
Remember to check out the panel on the left for some useful lemmas
-/

/- Lemma :
-/
@[simp]
lemma commutator_self {G : Type} [group G] {x : G} : [x, x] = 1 :=
begin
  rw commutator_def,
  rw inv_mul_cancel_right,
  rw inv_mul_self,




end
