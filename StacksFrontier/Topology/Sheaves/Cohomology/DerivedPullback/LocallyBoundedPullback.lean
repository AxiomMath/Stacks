module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackLocality
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.BoundedOnACompactOpen
import StacksCore.Tactic.StacksAttribute

/-!
# Pulling a locally bounded complex back to an open immersion over a compact open

Let `i : P ⟶ Z` be an open immersion of ringed spaces whose image lies in an open `W` of `Z`,
and let `ℱ^•` be a complex of `𝒪_Z`-modules. If `ℱ^•` is bounded on `W` then `i^*ℱ^•` has only
finitely many nonzero terms: a term whose restriction to `W` vanishes has vanishing pullback
along `i`, the pullback factoring through the restriction to the image of `i`, which is an open
inside `W`.

Combined with `Stacks.SheafOfModules.OnSpace.isBoundedOn_of_isLocallyBounded_of_isCompact` this
turns *local* boundedness of `ℱ^•` into a *global* bound on `i^*ℱ^•`, provided `W` is compact.
That is the reduction [Stacks, Tag 0FML] performs when it passes to an affine base: the fibre
product over an affine open of the base is an open immersion into the total space whose image
lies in the quasi-compact preimage of that affine open.

## Main results

* `Stacks.Cohomology.LocallyBoundedPullback.isZero_modulePullback_of_isZero_over`: a module
  whose restriction to `W` vanishes has vanishing pullback along an open immersion with image
  in `W`.
* `Stacks.Cohomology.LocallyBoundedPullback.finite_support_modulePullback_of_isLocallyBounded`:
  the pullback of a locally bounded complex along an open immersion whose image lies in a
  compact open has finitely many nonzero terms.

## References

* [Stacks Project, Tag 0FML](https://stacks.math.columbia.edu/tag/0FML)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry RingedSpaceModuleAdjunction
open Stacks.Cohomology.RelativeMayerVietoris

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.LocallyBoundedPullback

/-- **A module whose restriction to `W` vanishes has vanishing pullback along an open immersion
whose image lies in `W`.**

The pullback along `i` factors, by
`Stacks.Cohomology.RelativeMayerVietoris.modulePullbackOpenImmersionIso`, through the pullback
along the inclusion of the open subspace cut out by the image of `i`; that image is an open
contained in `W`, so the restriction of the module to it vanishes
(`Stacks.SheafOfModules.OnSpace.isZero_over_of_le`), and pullback along the inclusion of an
open subspace vanishes exactly when the restriction to the slice over that open does
(`Stacks.Cohomology.DerivedOpenImmersion.isZero_modulePullback_ofRestrict_iff`). -/
theorem isZero_modulePullback_of_isZero_over {Z P : RingedSpace.{u, u}} (i : P ⟶ Z)
    [SheafedSpace.IsOpenImmersion i] (W : Opens Z.carrier)
    (hW : Set.range i.hom.base ⊆ (W : Set Z.carrier))
    (M : SheafOfModules.{u} (structureSheafRing Z)) (hM : IsZero (M.over W)) :
    IsZero ((modulePullback i).obj M) := by
  have hle : immImage i ≤ W := hW
  have h : IsZero ((modulePullback
      (Stacks.Cohomology.HigherDirectImage.openSubspaceInclusion Z (immImage i))).obj M) :=
    (Stacks.Cohomology.DerivedOpenImmersion.isZero_modulePullback_ofRestrict_iff Z
      (immImage i) M).2 (Stacks.SheafOfModules.OnSpace.isZero_over_of_le Z hle hM)
  have : (modulePullback (openImmersionImageIso i).hom).Additive :=
    RingedSpaceModuleAdjunction.modulePullback_additive _
  exact (Functor.map_isZero (modulePullback (openImmersionImageIso i).hom) h).of_iso
    ((modulePullbackOpenImmersionIso i).app M)

/-- **The pullback of a locally bounded complex along an open immersion whose image lies in a
compact open has finitely many nonzero terms.**

`Stacks.SheafOfModules.OnSpace.isBoundedOn_of_isLocallyBounded_of_isCompact` turns the local
hypothesis into a single `Finset` of degrees outside which the restriction of the complex to the
compact open `W` vanishes, and `isZero_modulePullback_of_isZero_over` turns each such vanishing
into vanishing of the corresponding term of the pullback. -/
theorem finite_support_modulePullback_of_isLocallyBounded {Z P : RingedSpace.{u, u}} (i : P ⟶ Z)
    [SheafedSpace.IsOpenImmersion i]
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ)
    (hF : Stacks.SheafOfModules.OnSpace.IsLocallyBounded Z F)
    (W : Opens Z.carrier) (hWc : IsCompact (W : Set Z.carrier))
    (hW : Set.range i.hom.base ⊆ (W : Set Z.carrier)) :
    {j : ℤ | ¬ IsZero ((((modulePullback i).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F).X j)}.Finite := by
  obtain ⟨s, hs⟩ :=
    Stacks.SheafOfModules.OnSpace.isBoundedOn_of_isLocallyBounded_of_isCompact Z F hF W hWc
  refine Set.Finite.subset s.finite_toSet fun j hj => ?_
  by_contra hjs
  exact hj (isZero_modulePullback_of_isZero_over i W hW (F.X j) (hs j hjs))

end Stacks.Cohomology.LocallyBoundedPullback

end
