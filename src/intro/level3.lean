import logic.basic --hide

/-
So far we've worked with numbers in Lean and seen how we can substitute equalities
of natural numbers using `rewrite`.
In Lean we don't just work with objects like numbers, but we can also manipulate and prove things
that are far more abstract, and deal with propositions themselves as objects we want to prove things about.

In Lean these are called *propositions* and denoted `P : Prop`, exactly the same as how we had `n : ℕ`
before.
A proposition itself is a statement we might be trying to prove or disprove, but we can use the
same tool we used so far, rewriting, to manipulate them.
When dealing with concrete objects like numbers, we substitute equal numbers when proving.
For propositions we can subsitute equivalent propositions, where propositions are equivalent
if they are related by and if and only if. For instance one simple fact is that
-/
namespace bloop --hide
lemma or_comm : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P
:= or_comm --hide
end bloop --hide
/-
So if we wanted to show `⊢ x = 2 ∨ y = 1` we could `rewrite or_comm,` to change the goal to
`⊢ y = 1 ∨ x = 2`, which might then match one of our hypotheses better.

Check out the left sidebar for some new lemmas that you can use to prove the statement below.
One subtlety, note the curly (instead of round) brackets used in `{P : Prop}` in the `not_not` lemma statement.
This signals that `P` is a so-called implicit argument to `not_not`, meaning that syntax like `rewrite not_not P,` is not correct,
and instead `rewrite not_not,` should be used (where the argument `P` is then infered automatically).
-/

/- Axiom : iff_self
∀ (P : Prop), (P ↔ P) ↔ true
-/

/- Axiom : iff_true
∀ (P : Prop), (P ↔ true) ↔ P
-/

/- Axiom : not_not
∀ {P : Prop}, ¬ ¬ P ↔ P
-/

/- Lemma :
-/
lemma prop_prop (P Q R : Prop) (hPQ : P ↔ Q) (hQR : Q ↔ ¬R) :
  (¬P ↔ (Q ↔ P)) ↔ R :=
begin
  rw hPQ,
  rw iff_self,
  rw iff_true,
  rw hQR,
  rw not_not,




end
