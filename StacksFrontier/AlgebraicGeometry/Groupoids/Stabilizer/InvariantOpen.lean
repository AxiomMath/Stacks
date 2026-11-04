module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Images of quasi-compact opens under a flat groupoid

For a groupoid scheme with quasi-compact flat source and target over a quasi-separated object
scheme, the target-image of the source-preimage of a quasi-compact open is an intersection of a
nonempty family of quasi-compact opens.

## Main results

* `AlgebraicGeometry.GroupoidScheme.target_image_source_preimage_eq_iInter_compact_open`
  expresses the indicated image as such an intersection.

## References

* [Stacks Project, Tag 0APA](https://stacks.math.columbia.edu/tag/0APA)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Groupoids

universe u

/-- A compact set stable under generalization in a prespectral space is the intersection of a
nonempty family of quasi-compact opens. -/
private theorem compact_stable_eq_iInter_compact_open
    {X : Type u} [TopologicalSpace X] [PrespectralSpace X]
    {K : Set X} (hK : IsCompact K) (hgen : StableUnderGeneralization K) :
    ∃ (I : Type u) (_ : Nonempty I) (V : I → Set X),
      (∀ i, IsOpen (V i) ∧ IsCompact (V i)) ∧ K = ⋂ i, V i := by
  let I := {V : Set X // IsOpen V ∧ IsCompact V ∧ K ⊆ V}
  obtain ⟨V₀, hV₀c, hV₀o, hKV₀, _⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hK isOpen_univ (Set.subset_univ K)
  refine ⟨I, ⟨⟨V₀, hV₀o, hV₀c, hKV₀⟩⟩, Subtype.val,
    fun i => ⟨i.2.1, i.2.2.1⟩, ?_⟩
  obtain ⟨S, hSo, hS⟩ := stableUnderGeneralization_iff_exists_sInter_eq.mp hgen
  apply Set.Subset.antisymm
  · intro x hx
    exact Set.mem_iInter.mpr (fun i => i.2.2.2 hx)
  · intro x hx
    rw [← hS]
    refine Set.mem_sInter.mpr (fun U hUS => ?_)
    obtain ⟨V, hVc, hVo, hKV, hVU⟩ :=
      PrespectralSpace.exists_isCompact_and_isOpen_between hK (hSo U hUS)
        (hS ▸ Set.sInter_subset_of_mem hUS)
    exact hVU (Set.mem_iInter.mp hx ⟨V, hVo, hVc, hKV⟩)

namespace AlgebraicGeometry.GroupoidScheme

/-- The target-image of the source-preimage of a quasi-compact open in the object scheme of a
flat quasi-compact groupoid is an intersection of a nonempty family of quasi-compact opens. -/
@[stacks 0APA]
theorem target_image_source_preimage_eq_iInter_compact_open
    {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    [QuasiCompact G.source.left] [Flat G.source.left]
    [QuasiCompact G.target.left] [Flat G.target.left]
    [QuasiSeparatedSpace G.objects.left]
    (W : G.objects.left.Opens) (hW : IsCompact (W : Set G.objects.left)) :
    ∃ (I : Type u) (_ : Nonempty I) (V : I → Set G.objects.left),
      (∀ i, IsOpen (V i) ∧ IsCompact (V i)) ∧
        G.target.left.base '' (G.source.left.base ⁻¹' (W : Set G.objects.left)) = ⋂ i, V i :=
  compact_stable_eq_iInter_compact_open
    ((QuasiCompact.isCompact_preimage _ W.2 hW).image G.target.left.continuous)
    ((Flat.generalizingMap G.target.left).stableUnderGeneralization_image
      (W.2.stableUnderGeneralization.preimage G.source.left.continuous))

end AlgebraicGeometry.GroupoidScheme

end
