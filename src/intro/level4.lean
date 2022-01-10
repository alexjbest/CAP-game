

/-
## Applying lemmas

So far we have only discussed `rewrite`s, but of course there are many other important
methods of proof. Rewrites work when we want to substitute two things we know to be equal
into each other or change a proof using an `iff` statement.
When we only have an implication in one direction (`P` implies `Q`,
rather than `P` iff `Q`) we cannot substitute `Q` for `P` when
trying to prove `P`, but we could use the fact that `P` implies `Q`
when trying to prove `Q` to say that we only need to prove `P`.

In Lean the symbol used to denote an implication is `→`, which you can
type using `\to`. This is the same symbol that is used for functions
from one set to another (e.g. `f : ℚ → ℝ`). This is for a good reason, you can think
of an implication as a function, one that takes a proof of `P` and
gives you a proof of `Q`.

The basic tool for doing this in Lean is called `apply`, and it
works as follows:
If `h : P → Q` is the satement that `P` implies `Q` and the goal is `⊢ Q`, then
apply `h` will change the goal to `⊢ P` instead.

You can also use apply when you have a proof `h : P` and the goal is `⊢ P`.
In that case `apply h` will finish the proof. There is another tactic called `exact`, which
is better for when the goal is exactly one of the hypotheses, so we can use `exact h` here instead.

Try these new tactics out below:

-/
/- Tactic : apply
## Summary
TODO
-/
/- Tactic : exact
## Summary
TODO
-/

lemma double_imply (P Q R : Prop) (h : P) (h_PtoQ : P → Q) (h_QtoR : Q → R) : R :=
begin
  apply h_QtoR,
  apply h_PtoQ,
  apply h,






end