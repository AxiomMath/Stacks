module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Algebra.Homology.PseudoCoherent.CohomologyBoundedAbove
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RestrictHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A pseudo-coherent object on a quasi-compact scheme is bounded above

Let `X` be a quasi-compact scheme and let `E` be an `m`-pseudo-coherent object of the derived
category of `𝒪_X`-modules. Then `Hʲ(E) = 0` for all sufficiently large `j`.

An `m`-pseudo-coherent object is bounded above near every point, because its local strictly
perfect approximation has only finitely many nonzero terms
(`AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict`). Quasi-compactness
turns the resulting covering into a finite one, so the local bounds have a maximum; above that
maximum every point of `X` has a neighbourhood on which `Hʲ(E)` restricts to zero, so `Hʲ(E)` has
empty support and is therefore zero.

## Main results

* `AlgebraicGeometry.isBoundedAbove_of_isPseudoCoherentFrom`: the global bound.

## Implementation notes

The passage from "zero on a neighbourhood of every point" to "zero" goes through the support:
`Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules` removes a
point from the support of a module whose restriction to a neighbourhood of it vanishes, and
`Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty` makes a module with empty
support zero.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect TopologicalSpace

namespace AlgebraicGeometry

universe d u

/-- **On a quasi-compact scheme the cohomology of an `m`-pseudo-coherent object of the derived
category of `𝒪_X`-modules vanishes in all sufficiently large degrees.** -/
@[sga "6 III 1.2.1" "special case"]
public theorem isBoundedAbove_of_isPseudoCoherentFrom (X : Scheme.{u})
    [CompactSpace X.toRingedSpace.carrier]
    [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]
    [∀ U : Opens X.toRingedSpace.carrier,
      HasDerivedCategory.{d} (OXMod.{u, u} (X.toRingedSpace.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) (m : ℤ)
    (hE : RingedSpace.IsPseudoCoherentFrom (X := X.toRingedSpace) E m) :
    DerivedCategoryB.IsBoundedAbove E := by
  classical
  choose U hxU b hb using fun x : X.toRingedSpace.carrier =>
    RingedSpace.exists_isZero_homology_gt_derivedRestrict (X := X.toRingedSpace) E m hE x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.toRingedSpace.carrier => (U x : Set X.toRingedSpace.carrier))
    (fun x => (U x).isOpen) fun x _ => Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨c, hc⟩ := (s.finite_toSet.image b).bddAbove
  refine ⟨c, fun j hj => ?_⟩
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty
    (X := X) _ (Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_)
  obtain ⟨x, hxs, hyU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ y))
  have hzero : IsZero ((RingedSpace.restrictModules X.toRingedSpace (U x)).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) j).obj E)) :=
    (hb x j (lt_of_le_of_lt (hc (Set.mem_image_of_mem b hxs)) hj)).of_iso
      (RingedSpace.derivedRestrictHomologyIso (X := X.toRingedSpace) (U x) j E).symm
  exact Stacks.AlgebraicGeometry.PerfectCohomology.notMem_supp_of_isZero_restrictModules
    X (U x) _ hzero y hyU hy

end AlgebraicGeometry

end
