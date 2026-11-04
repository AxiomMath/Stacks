module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentCriterion
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree

/-!
# Ampleness on a proper curve from a section vanishing somewhere on every component

Let `X` be a proper scheme of dimension at most one over a field `k` and `𝓛` an invertible
`𝒪_X`-module with a global section `s`. If `s` does not vanish at the generic point of any
one-dimensional irreducible component of `X`, but vanishes at some point of each of them, then
`𝓛` is ample.

This is the criterion through which an effective Cartier divisor `D` meeting every
one-dimensional component of a proper curve makes `𝒪_X(D)` ample: the canonical section `1_D`
vanishes exactly on `D`, which contains no generic point of a one-dimensional component.

## The argument

By the direction (2) ⟹ (1) of [Stacks, Tag 0B5Y] it suffices that the restriction of `𝓛` to every
one-dimensional component `C`, with its reduced induced structure, has positive degree. The
pullback of `s` to the integral scheme `C` does not vanish at the generic point of `C`, so it is
nonzero, and it vanishes at a point of `C`; so the degree is positive by part (2) of
[Stacks, Tag 0B40].

## Main results

* `AlgebraicGeometry.isAmple_of_mem_nonvanishingLocus_genericPointsOne`: the criterion.

## References

* [Stacks Project, Tag 0B5Y](https://stacks.math.columbia.edu/tag/0B5Y)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace AlgebraicGeometry

/-- **Ampleness on a proper curve from a section.** Let `X` be proper over a field `k` with
`dim X ≤ 1`, `𝓛` an invertible `𝒪_X`-module and `s` a global section of `𝓛` which does not
vanish at the generic point of any one-dimensional irreducible component of `X` and vanishes at
some point of each of them. Then `𝓛` is ample. -/
theorem isAmple_of_mem_nonvanishingLocus_genericPointsOne (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L] (s : Γ(L, ⊤))
    (hgen : ∀ ζ ∈ genericPointsOne X, ζ ∈ Stacks.Ample.nonvanishingLocus L s)
    (hzero : ∀ ζ ∈ genericPointsOne X, ∃ y ∈ closure ({ζ} : Set X),
      y ∉ Stacks.Ample.nonvanishingLocus L s) :
    Scheme.Modules.IsAmple X L := by
  refine (isAmple_iff_forall_invertibleCurveDegree_reducedComponent_pos k f hdim L).mpr
    fun ζ => ?_
  have := isIntegral_reducedComponent X ζ
  have := isProper_reducedComponentι_comp k f ζ
  let ι := reducedComponentι X ζ
  let L' := (Scheme.Modules.pullback ι).obj L
  let s' : Γ(L', ⊤) := pullbackGlobalSections ι L s
  have hNV : ι.base ⁻¹' Stacks.Ample.nonvanishingLocus L s =
      Stacks.Ample.nonvanishingLocus L' s' :=
    Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections ι L s
  have hrange : Set.range ι.base = closure ({ζ.1} : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    rfl
  obtain ⟨y, hy, hyNV⟩ := hzero ζ.1 ζ.2
  obtain ⟨y', rfl⟩ : y ∈ Set.range ι.base := hrange ▸ hy
  have hgen' : genericPoint (reducedComponent X ζ) ∈ Stacks.Ample.nonvanishingLocus L' s' := by
    rw [← hNV, Set.mem_preimage]
    rw [reducedComponentι_genericPoint X ζ]
    exact hgen ζ.1 ζ.2
  have hs' : s' ≠ 0 := by
    rintro h
    rw [h, Stacks.Ample.mem_nonvanishingLocus_iff, map_zero] at hgen'
    exact hgen' (zero_mem _)
  exact @invertibleCurveDegree_pos_of_eval_top_ne_zero k _ (reducedComponent X ζ) (ι ≫ f) _ _
    (topologicalKrullDim_reducedComponent_le X hdim ζ) L'
    (SheafOfModules.isInvertible_pullback ι L) (Stacks.SheafOfModules.sectionsOfTop L' s')
    ((Stacks.SheafOfModules.sectionsOfTop_eval_top L' s').trans_ne hs')
    ⟨y', by rw [nonvanishingLocus_sectionsOfTop_eq L' s', ← hNV]; exact hyNV⟩

end AlgebraicGeometry

end
