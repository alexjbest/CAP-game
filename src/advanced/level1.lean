import topology.basic

/-
In this problem you will look at proving that the composition of two continuous maps is
continuous

Some things you should know:
- A subset of a space `X` is an element of the type `set X` in Lean
- The notation for the preimage of a set `U` along a map `f` is `f ⁻¹' U`
-/
/- Axiom : continuous_def : ∀ {α : Type} {β : Type} [topological_space α]
  [topological_space β] {f : α → β},
  continuous f ↔ ∀ (s : set β),is_open s → is_open (f ⁻¹' s)
-/
/- Axiom : set.preimage_comp : ∀ {α β γ : Type} {f : α → β} {g : β → γ} {s : set γ},
g ∘ f ⁻¹' s = f ⁻¹' (g ⁻¹' s)
-/
/-
You will need to the tactics intros, rewrite, and apply for this problem!
-/
/- Lemma :
-/
lemma image_compact
  (X Y Z : Type)
  [topological_space X]
  [topological_space Y]
  [topological_space Z]
  (f : X → Y)
  (g : Y → Z)
  (hf : continuous f)
  (hg : continuous g) :
  continuous (g ∘ f) :=
begin
  rw continuous_def at *,
  intros S hS,
  rw [set.preimage_comp],
  apply hf,
  apply hg,
  apply hS,
end
