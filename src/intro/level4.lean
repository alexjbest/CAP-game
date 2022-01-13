import logic.basic --hide

/-
## Exact

Sometimes after rewriting the hypotheses and goal enough we reach a point where the goal is
exactly the same as one of the hypothesis.
In this case we want to tell Lean that we are finished, one of our hypotheses now matches
the conclusion we needed to get to.

The tactic to do this is called `exact`, and to use it we just need to supply the name of
the hypothesis we want to use.

For example if we were trying to prove that 3 divides some natural number `n` and we
ended up with the goal state:
```
n : ℕ
h : 3 ∣ n
⊢ 3 ∣ n
```
then `exact h,` would complete the proof.

-/

/- Tactic : exact

## Summary

If the goal is `⊢ X` then `exact x` will close the goal if
and only if `x` is a term of type `X`.

## Details

Say $P$, $Q$ and $R$ are types (i.e., what a mathematician
might think of as either sets or propositions),
and the local context looks like this:

```
p : P,
h : P → Q,
j : Q → R
⊢ R
```

If you can spot how to make a term of type `R`, then you
can just make it and say you're done using the `exact` tactic
together with the formula you have spotted. For example the
above goal could be solved with

`exact j(h(p)),`

because $j(h(p))$ is easily checked to be a term of type $R$
(i.e., an element of the set $R$, or a proof of the proposition $R$).

-/

/- Axiom :
or_and_distrib_right : ∀ {a b c : Prop}, (a ∨ b) ∧ c ↔ a ∧ c ∨ b ∧ c
-/

/- Axiom :
not_and_self (a : Prop) : (¬a ∧ a) ↔ false
-/

/- Axiom :
or_false (a : Prop) : (a ∨ false) ↔ a
-/

/- Axiom :
and_comm : ∀ (a b : Prop), a ∧ b ↔ b ∧ a
-/

/- Axiom :
and_assoc : ∀ {c : Prop} (a b : Prop), (a ∧ b) ∧ c ↔ a ∧ b ∧ c
-/

/- Axiom :
and_self : ∀ (a : Prop), a ∧ a ↔ a
-/

/- Lemma : no-side-bar
-/
lemma prop_prop (P Q : Prop) (h : Q ∧ P ∧ Q) :
  (P ∨ ¬ Q) ∧ Q :=
begin
  rw or_and_distrib_right,
  rw not_and_self,
  rw or_false,
  rw and_comm at h,
  rw and_assoc at h,
  rw and_self at h,
  exact h,
end
