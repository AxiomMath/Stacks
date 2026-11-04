module

public import Mathlib.Topology.Spectral.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Spectral.ConstructiblyClosedStable
public import StacksFrontier.Topology.Spectral.QuasiCompactOpenInter

/-!
# Extending a decomposition of a closed subset of a spectral space

Let `Z` be a closed subset of a spectral space. If the intersection of `Z` with the closure of
every point is connected and nonempty, then every decomposition of `Z` into two relatively
closed subsets extends to a decomposition of the whole space into two closed subsets.

## Main results

* `exists_isClosed_partition`: a relatively closed partition of `Z` extends to a closed
  partition of the ambient spectral space.

## Implementation notes

Relative closedness of `Z₁` and `Z₂` is expressed in the subtype `Z`. Both the given
decomposition and the resulting decomposition are expressed by a union equality together with
disjointness. The extension is built by taking generalizations: the set of generalizations of a
quasi-compact set is closed in the constructible topology and stable under generalization, and
the connectedness hypothesis makes the two sets of generalizations cover and stay disjoint, so
each is closed for the original topology.

## References

* [Stacks Project, Tag 0CAM](https://stacks.math.columbia.edu/tag/0CAM)
-/

@[expose] public section

open Set


private lemma compact_piece {X : Type*} [TopologicalSpace X] {Z E : Set X}
    [CompactSpace Z] (h : IsClosed ((Subtype.val : Z → X) ⁻¹' E))
    (hEZ : E ⊆ Z) : IsCompact E := by
  have him := h.isCompact.image continuous_subtype_val
  rwa [Set.image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hEZ] at him

private lemma generalizations_closed_constructible {X : Type*}
    [TopologicalSpace X] [SpectralSpace X] (E : Set X) (hE : IsCompact E) :
    @IsClosed X (constructibleTopology X) (SpectralSubset.generalizationsOf E) := by
  obtain ⟨S, hS, hScompact⟩ :=
    (SpectralSubset.characterizations_equiv (SpectralSubset.generalizationsOf E)).2.2.1.mp
      ⟨E, hE, rfl⟩
  rw [hS]
  exact @isClosed_sInter X (constructibleTopology X) S (fun U hU =>
    ((hScompact U hU).2.isClopen_constructibleTopology (hScompact U hU).1).1)

private lemma piece_inter_generalizations {X : Type*} [TopologicalSpace X]
    {Z E F : Set X} (hunion : E ∪ F = Z) (hdisjoint : Disjoint E F)
    (hF : IsClosed ((Subtype.val : Z → X) ⁻¹' F)) :
    E = Z ∩ SpectralSubset.generalizationsOf E := by
  have hEsub : E ⊆ Z := fun _ hx => hunion ▸ Or.inl hx
  ext x
  refine ⟨fun hx => ⟨hEsub hx, x, hx, specializes_refl x⟩, ?_⟩
  rintro ⟨hxZ, z, hzE, hxz⟩
  have hsub : ((⟨x, hxZ⟩ : Z) ⤳ (⟨z, hEsub hzE⟩ : Z)) :=
    (subtype_specializes_iff _ _).mpr hxz
  by_contra hxE
  have hxF : (⟨x, hxZ⟩ : Z) ∈ (Subtype.val ⁻¹' F) :=
    (hunion.symm ▸ hxZ : x ∈ E ∪ F).resolve_left hxE
  exact Set.disjoint_left.mp hdisjoint hzE (hsub.mem_closed hF hxF)

private lemma stableUnderSpecialization_of_partition {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hcover : A ∪ B = univ) (hdisj : Disjoint A B)
    (hB : StableUnderGeneralization B) : StableUnderSpecialization A :=
  fun _ y hxy hx => (hcover.symm ▸ mem_univ y : y ∈ A ∪ B).resolve_right
    fun hy => Set.disjoint_left.mp hdisj hx (hB hxy hy)

private lemma generalizations_stable {X : Type*} [TopologicalSpace X] (E : Set X) :
    StableUnderGeneralization (SpectralSubset.generalizationsOf E) :=
  fun _ _ hxy ⟨z, hz, hyz⟩ => ⟨z, hz, hxy.trans hyz⟩

private lemma generalizationsOf_union_eq_univ {X : Type*} [TopologicalSpace X]
    {Z Z₁ Z₂ : Set X} (hne : ∀ x : X, (Z ∩ closure ({x} : Set X)).Nonempty)
    (hunion : Z₁ ∪ Z₂ = Z) :
    SpectralSubset.generalizationsOf Z₁ ∪ SpectralSubset.generalizationsOf Z₂ = univ := by
  refine eq_univ_of_forall fun x => ?_
  obtain ⟨z, hzZ, hzx⟩ := hne x
  rw [← hunion] at hzZ
  have h := specializes_iff_mem_closure.mpr hzx
  exact hzZ.imp (⟨z, ·, h⟩) (⟨z, ·, h⟩)

private lemma disjoint_generalizationsOf_of_isConnected {X : Type*} [TopologicalSpace X]
    {Z Z₁ Z₂ : Set X} (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (hZ₁ : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₁))
    (hZ₂ : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₂))
    (hunion : Z₁ ∪ Z₂ = Z) (hdisjoint : Disjoint Z₁ Z₂) :
    Disjoint (SpectralSubset.generalizationsOf Z₁) (SpectralSubset.generalizationsOf Z₂) := by
  rw [Set.disjoint_left]
  rintro x ⟨z₁, hz₁, hxz₁⟩ ⟨z₂, hz₂, hxz₂⟩
  let C : Set X := Z ∩ closure ({x} : Set X)
  let A : Set C := (Subtype.val : C → X) ⁻¹' Z₁
  let B : Set C := (Subtype.val : C → X) ⁻¹' Z₂
  have hAB : Aᶜ = B := by
    ext y
    simp only [A, B, Set.mem_compl_iff, Set.mem_preimage]
    exact ⟨fun hy => (hunion.symm ▸ y.2.1 : (y : X) ∈ Z₁ ∪ Z₂).resolve_left hy,
      fun hy hy₁ => Set.disjoint_left.mp hdisjoint hy₁ hy⟩
  have : ConnectedSpace C := isConnected_iff_connectedSpace.mp (hconnected x)
  have hAclopen : IsClopen A :=
    ⟨hZ₁.preimage (continuous_inclusion inter_subset_left), by
      rw [← isClosed_compl_iff, hAB]
      exact hZ₂.preimage (continuous_inclusion inter_subset_left)⟩
  have hz₁C : (⟨z₁, ⟨hunion ▸ Or.inl hz₁, specializes_iff_mem_closure.mp hxz₁⟩⟩ : C) ∈ A := hz₁
  have hz₂A : (⟨z₂, ⟨hunion ▸ Or.inr hz₂, specializes_iff_mem_closure.mp hxz₂⟩⟩ : C) ∈ A :=
    isPreconnected_univ.subset_isClopen hAclopen ⟨_, mem_univ _, hz₁C⟩ (mem_univ _)
  exact Set.disjoint_left.mp hdisjoint hz₂A hz₂

/-- The generalizations of a relatively closed piece `E` of a decomposition `E ∪ F = Z` into
disjoint generalization sets are closed. -/
private lemma isClosed_generalizationsOf_piece {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    {Z E F : Set X} [CompactSpace Z] (hne : ∀ x : X, (Z ∩ closure ({x} : Set X)).Nonempty)
    (hE : IsClosed ((Subtype.val : Z → X) ⁻¹' E)) (hunion : E ∪ F = Z)
    (hdisj : Disjoint (SpectralSubset.generalizationsOf E)
      (SpectralSubset.generalizationsOf F)) :
    IsClosed (SpectralSubset.generalizationsOf E) :=
  isClosed_of_isClosed_constructibleTopology_of_stableUnderSpecialization
    (generalizations_closed_constructible E (compact_piece hE fun _ hx => hunion ▸ Or.inl hx))
    (stableUnderSpecialization_of_partition (generalizationsOf_union_eq_univ hne hunion) hdisj
      (generalizations_stable F))

/-- A partition of a closed subset `Z` into two relatively closed pieces extends to a
partition of the ambient spectral space into two closed pieces, provided `Z` meets the
closure of each point in a connected set. -/
@[stacks 0CAM]
public lemma exists_isClosed_partition
    {X : Type*} [TopologicalSpace X] [SpectralSpace X]
    {Z Z₁ Z₂ : Set X} (hZ : IsClosed Z)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (hZ₁ : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₁))
    (hZ₂ : IsClosed ((Subtype.val : Z → X) ⁻¹' Z₂))
    (hunion : Z₁ ∪ Z₂ = Z) (hdisjoint : Disjoint Z₁ Z₂) :
    ∃ X₁ X₂ : Set X,
      IsClosed X₁ ∧ IsClosed X₂ ∧ X₁ ∪ X₂ = univ ∧ Disjoint X₁ X₂ ∧
        Z₁ = Z ∩ X₁ ∧ Z₂ = Z ∩ X₂ :=
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hZ.isCompact
  have hne := fun x => (hconnected x).nonempty
  have hdisj := disjoint_generalizationsOf_of_isConnected hconnected hZ₁ hZ₂ hunion hdisjoint
  ⟨_, _, isClosed_generalizationsOf_piece hne hZ₁ hunion hdisj,
    isClosed_generalizationsOf_piece hne hZ₂ (union_comm _ _ ▸ hunion) hdisj.symm,
    generalizationsOf_union_eq_univ hne hunion, hdisj,
    piece_inter_generalizations hunion hdisjoint hZ₂,
    piece_inter_generalizations (union_comm Z₂ Z₁ ▸ hunion) hdisjoint.symm hZ₁⟩
