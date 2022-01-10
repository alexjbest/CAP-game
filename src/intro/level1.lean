import data.nat.basic --hide

--image of compact is compact
-- use hints
/-
## The setup
Welcome to Lean! You should see a few sections on this page, they are all part of using Lean, lets go through them one by one.

Us
The middle one is where you tell Lean what steps you want to make in your proof.
By typing statements here in precise language we instruct Lean how we want the proof to go.
Right now this text is frozen, but at the bottom you will be able to type your first Lean
proof.

On the right hand side you can see a window with `goal` at the top.
This panel represents what Lean thinks the current state of your proof is, most importantly
the facts and hypothesis you already know, and the statement (or statements) you are trying to show, these come after
the `⊢` symbol to make it clear which is which.
For example a valid state might look like
```
n : ℕ
h : is_even n
⊢ is_odd (n + 1)
```
which means that we have assumed `n` is a natural number and that `n` is even, and we are trying to show that `n + 1` is
odd.
In order to prove this we will need to use more than what is written here however, we might need the definition of
an even and an odd number, so in addition to the current hypotheses we also will make use of a library of lemmas that
we have proved so far.

Below this there will be more information about the word your cursor is currently on, and feedback about any errors
in your current proof.

Lets now discuss the language Lean uses to represent statements.

## The language

A lemma in Lean is written using a specific syntax, that is designed to look similar to written
mathematics, but is more restricted in how statements can be constructed.
Here is an example of a lemma statement in Lean:
-/

namespace boop --hide
lemma add_comm : ∀ (x : ℕ) (y : ℕ), x + y = y + x
:= add_comm --hide
end boop --hide

/-
This lemma states that for all natural numbers `x` and `y` that addition of `x` and `y` commutes.
Note the first word `lemma` is a keyword (highlighted in blue) and means we are stating a new
lemma.
The second word is simply a name we give to the lemma so we can refer to it later, naming lemmas
works much better than numbering lemmas when you have many lemmas to refer to.
This is especially true if you give the lemmas sensible names, so that you can remember them
later, and so that when you apply them its clear what the lemma you are referring to does, just
from its name.
In this case `add_comm` to say that addition is commutative, seems like a pretty good choice.

Note the use of the symbol `:` to say that `x` and `y` are natural numbers, whereas we would
normally use `x ∈ ℕ`.
The symbol `:` is also used after the name of the lemma, and it has the same meaning!
Here within the lemma `x : ℕ` gives a name to a natural number and
`add_comm : ∀ x y, x + y = y + x` gives a name to the statement that addition is commutative.

The lemma `add_comm` is a forall statement, so in order to get the statement that addition
commutes for some _specific_ natural numbers rather than any, we place them after the name,
for instance `add_comm 2 3` means `2 + 3 = 3 + 2`.


### Rewriting
Rewriting is one of the most basic methods of proof, we substitute a part of something we want
to prove with something we know to be equal to it.

If `h` is a proof of `X = Y`, then `rewrite h,` will change
all `X`s in the goal to `Y`s.

-/

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
then `rw h1 at h2` will turn `h2` into `h2 : B ∪ B ∩ C = D` (remember operator precedence).-/

/- Axiom : The commutativity of addition
add_comm : ∀ x y, x + y = y + x
-/

/-
The next tactic we will learn is *rw* (from rewrite). It rewrites equalities. That is,
if we have a proof `h : x = 3` and we want to prove `⊢ x + 1 = 4`, then after `rw h` the goal
will become `⊢ 3 + 1 = 4`, which seems reasonable.

-/

/- Hint : Click here for a hint, in case you get stuck.
Delete `sorry` and type `rewrite add_comm x y,` (don't forget the comma!). Lean tries `refl` afterwards,
so you will see that this suffices.
-/

/- Lemma : 
-/
lemma level1 (x y z w : ℕ) : x + y + (z + w) = (w + z) + (y + x) :=
begin
  rw add_comm x y,
  rw add_comm w z,
  rw add_comm,







end
