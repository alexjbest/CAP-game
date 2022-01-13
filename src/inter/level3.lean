import tactic

/- Tactic : split
When given a goal that is an `∧` (and) of two propositions, the `split` tactic
will produce two goals, one for each side. That can be solved individually.
-/

/- Axiom : nat.lt_succ_self : ∀ (n : ℕ), n < n.succ
-/
/- Lemma :
-/
lemma split : 4 < 5 ∧ 5 < 6 :=
begin
  split,
  exact nat.lt_succ_self 4,
  exact nat.lt_succ_self 5,
end
