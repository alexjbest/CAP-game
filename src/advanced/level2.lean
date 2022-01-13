import topology.subset_properties

/-
In this problem you will look at proving that the image of a compact set in a topological space
along a continuous map is also compact.

Some things you should know:
- A subset of a space `X` is an element of the type `set X` in Lean
- The notation for image of a set `U` along a map `f` is `f '' U`
- The simplifier `simp,`,
  is very useful, especially simplifying your hypotheses  `simp at ht` !
  You can use `simp at *,` to simplify as much as possible everywhere
- there is a new helpful lemma in the sidebar
-/
/- Hint : click here for the first few lines of the proof
```
rw is_compact_iff_finite_subcover, -- rewrite the definition of compactness
rw is_compact_iff_finite_subcover at h,  -- rewrite the definition of compactness
intros ι V hV hVu, -- we are proving a forall, so introduce everything
obtain ⟨t, ht⟩ := h (λ i, f ⁻¹' (V i)) _ _, -- pull back the open sets from Y to X
```
-/
/- Axiom : continuous.is_open_preimage : ∀ {α β : Type} [_inst_1 : topological_space α]
  [_inst_2 : topological_space β] {f : α → β},
  continuous f → ∀ (s : set β), is_open s → is_open (f ⁻¹' s)
-/
/- Lemma :
-/
lemma image_compact
  (X : Type)
  [topological_space X]
  (V : set X)
  (h : is_compact V)
  (Y : Type)
  [topological_space Y]
  (f : X → Y)
  (hf : continuous f) :
  is_compact (f '' V) :=
begin
  rw is_compact_iff_finite_subcover,
  rw is_compact_iff_finite_subcover at h,
  intros ι V hV hVu,
  obtain ⟨t, ht⟩ := h (λ i, f ⁻¹' (V i)) _ _,
  use t,
  simp [ht],
  intro i,
  simp,
  apply continuous.is_open_preimage hf (V i) (hV i),
  simp at hVu,
  simp [hVu],
end
