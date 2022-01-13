import inter.level3
import tactic

/- Tactic : use
When the goal is to prove an existential, `∃` we can
supply the witness (an example that has the desired property)
using the tactic `use`.

For example :
If the goal is
```
⊢ ∃ n : ℕ, n + 1 = 1
```
then we have to take `n` to be zero, so we type `use 0`.
The remaining goal will then be that
`0 + 1 = 1`
which is provable with `zero_add`.
-/


/- Lemma :
-/
lemma exists_betwn : ∃ n : ℕ, 8 < n ∧ n < 10 :=
begin
  use 9,
  split,
  exact nat.lt_succ_self 8,
  exact nat.lt_succ_self 9,
end
