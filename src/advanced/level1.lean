import topology.subset_properties
--image of compact is compac
#check is_compact

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
