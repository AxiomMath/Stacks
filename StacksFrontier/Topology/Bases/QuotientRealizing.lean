module

public import Mathlib.Topology.Bases

/-!
# Quotient topology realizing a prescribed basis

Given a set `X` and a family `B ⊆ 𝒫(X)` that covers `X` and is closed under finite intersections
up to refinement (every pairwise intersection of members of `B` is a union of members of `B`
contained in it), the space `Y` realizing `B` as a basis is the quotient of `X` by the equivalence
relation `x ≈ y ↔ ∀ U ∈ B, x ∈ U ↔ y ∈ U`, and `f` is the quotient map.

## Main results

* `stacksSetoid`, `stacksF`: the equivalence relation cutting `X` down to the information visible
  through `B`, and the associated quotient map.
* `create_map_from_subcollection` (Stacks 0D5Q): there is a continuous `f : X → Y` such that for
  `U ∈ B` the image `f '' U` is open, `f ⁻¹' (f '' U) = U`, and the sets `f '' U` form a
  topological basis of `Y`.
-/

@[expose] public section

universe u

/-- The setoid on `X` defined by: `x ≈ y` iff for all `U ∈ B`, `x ∈ U ↔ y ∈ U`. -/
def stacksSetoid {X : Type u} (B : Set (Set X)) : Setoid X where
  r x y := ∀ U ∈ B, (x ∈ U ↔ y ∈ U)
  iseqv :=
    { refl := fun _ _ _ => Iff.rfl
      symm := fun h U hU => (h U hU).symm
      trans := fun h₁ h₂ U hU => (h₁ U hU).trans (h₂ U hU) }

/-- The quotient map `X → X / stacksSetoid B`. -/
def stacksF {X : Type u} (B : Set (Set X)) : X → Quotient (stacksSetoid B) :=
  Quotient.mk (stacksSetoid B)

/-- For `U ∈ B`, the preimage of the image of `U` under the quotient map equals `U`: membership in
`U` is one of the conditions defining the equivalence relation. -/
lemma stacksF_preimage_image {X : Type u} (B : Set (Set X)) (U : Set X) (hU : U ∈ B) :
    stacksF B ⁻¹' (stacksF B '' U) = U := by
  ext x
  refine ⟨?_, fun hx => ⟨x, hx, rfl⟩⟩
  rintro ⟨y, hyU, hxy⟩
  exact (Quotient.exact hxy U hU).mp hyU

/-- The collection `{f '' U | U ∈ B}` covers the quotient, provided `B` covers `X`. -/
lemma stacksF_image_sUnion_eq_univ {X : Type u} (B : Set (Set X))
    (h_cover : ⋃₀ B = Set.univ) :
    ⋃₀ ((fun U => stacksF B '' U) '' B) = (Set.univ : Set (Quotient (stacksSetoid B))) := by
  refine Set.eq_univ_of_forall fun q => ?_
  obtain ⟨x, hx⟩ := Quotient.exists_rep q
  obtain ⟨U, hU, hxU⟩ : x ∈ ⋃₀ B := h_cover ▸ Set.mem_univ x
  exact ⟨stacksF B '' U, ⟨U, hU, rfl⟩, x, hxU, hx⟩

/-- The collection `{f '' U | U ∈ B}` satisfies the refinement-of-intersections property required
of a topological basis, provided `B` does. -/
lemma stacksF_image_exists_subset_inter {X : Type u} (B : Set (Set X))
    (h_inter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V = ⋃₀ {W ∈ B | W ⊆ U ∩ V}) :
    ∀ t₁ ∈ (fun U => stacksF B '' U) '' B,
    ∀ t₂ ∈ (fun U => stacksF B '' U) '' B,
    ∀ q ∈ t₁ ∩ t₂, ∃ t₃ ∈ (fun U => stacksF B '' U) '' B, q ∈ t₃ ∧ t₃ ⊆ t₁ ∩ t₂ := by
  rintro _ ⟨U₁, hU₁B, rfl⟩ _ ⟨U₂, hU₂B, rfl⟩ q ⟨⟨x₁, hx₁U₁, hx₁q⟩, ⟨x₂, hx₂U₂, hx₂q⟩⟩
  have hxx : (stacksSetoid B).r x₁ x₂ := Quotient.exact (hx₁q.trans hx₂q.symm)
  have hx₁_inter : x₁ ∈ U₁ ∩ U₂ := ⟨hx₁U₁, (hxx U₂ hU₂B).mpr hx₂U₂⟩
  rw [h_inter U₁ hU₁B U₂ hU₂B] at hx₁_inter
  obtain ⟨W, ⟨hWB, hWsub⟩, hx₁W⟩ := hx₁_inter
  refine ⟨stacksF B '' W, ⟨W, hWB, rfl⟩, ⟨x₁, hx₁W, hx₁q⟩, ?_⟩
  rintro y ⟨w, hwW, rfl⟩
  exact ⟨⟨w, (hWsub hwW).1, rfl⟩, ⟨w, (hWsub hwW).2, rfl⟩⟩

/-- **Stacks 0D5Q.** Given a collection `B` of opens covering `X` such that every pairwise
intersection of members of `B` is a union of members of `B` contained in it, there is a continuous
map `f : X → Y` of topological spaces such that for `U ∈ B` the image `f '' U` is open,
`f ⁻¹' (f '' U) = U`, and the opens `f '' U` form a basis for the topology on `Y`. -/
@[stacks 0D5Q]
theorem create_map_from_subcollection {X : Type u} [TopologicalSpace X] (B : Set (Set X))
    (hB_open : ∀ U ∈ B, IsOpen U)
    (h_cover : ⋃₀ B = Set.univ)
    (h_inter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V = ⋃₀ {W ∈ B | W ⊆ U ∩ V}) :
    ∃ (Y : Type u) (τ : TopologicalSpace Y) (f : X → Y),
      @Continuous X Y _ τ f ∧
      (∀ U ∈ B, @IsOpen Y τ (f '' U)) ∧
      (∀ U ∈ B, f ⁻¹' (f '' U) = U) ∧
      @TopologicalSpace.IsTopologicalBasis Y τ ((fun U => f '' U) '' B) := by
  let C : Set (Set (Quotient (stacksSetoid B))) := (fun U => stacksF B '' U) '' B
  let τ : TopologicalSpace (Quotient (stacksSetoid B)) := TopologicalSpace.generateFrom C
  refine ⟨Quotient (stacksSetoid B), τ, stacksF B, ?_,
    fun U hU => TopologicalSpace.GenerateOpen.basic _ ⟨U, hU, rfl⟩,
    stacksF_preimage_image B,
    .mk (stacksF_image_exists_subset_inter B h_inter)
      (stacksF_image_sUnion_eq_univ B h_cover) rfl⟩
  refine continuous_generateFrom_iff.mpr ?_
  rintro t ⟨U, hU, rfl⟩
  rw [stacksF_preimage_image B U hU]
  exact hB_open U hU
