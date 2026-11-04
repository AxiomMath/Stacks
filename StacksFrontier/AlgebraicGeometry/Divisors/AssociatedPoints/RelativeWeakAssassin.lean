module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksCore.Tactic.StacksAttribute

/-!
# The relative weak assassin

For a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `F`, the *relative weak assassin*
`WeakAss_{X/S}(F)` is the union over the points of `S` of the images in `X` of the weakly
associated points of the restriction of `F` to the scheme-theoretic fibre. For a morphism
locally of finite type it coincides with the relative assassin `Ass_{X/S}(F)`.

## Main definitions

* `AlgebraicGeometry.relativeWeaklyAssociatedPoints` is the relative weak assassin.

## Main results

* `AlgebraicGeometry.relativeWeaklyAssociatedPoints_eq_relativeAssassin`: for a morphism
  locally of finite type the relative weak assassin is the relative assassin
  `Stacks.Divisors.relativeAssassin`.
* `AlgebraicGeometry.relativeAssassin_subset_relativeWeaklyAssociatedPoints`: the relative
  assassin is contained in the relative weak assassin, with no hypothesis.

## Implementation notes

The set lives in the total space: the weakly associated points of each fibre are carried into
`X` by the canonical fibre inclusion `AlgebraicGeometry.Scheme.Hom.fiberι`, exactly as for
`Stacks.Divisors.relativeAssassin`. Quasi-coherence is not needed to form the set, so the
definition applies to every sheaf of modules; and the fibres of a morphism locally of finite
type are locally Noetherian, where weakly associated and associated points agree for every
module, so the source's quasi-coherence hypothesis is unnecessary in the comparison too.

## References

* [Stacks Project, Tag 05AV](https://stacks.math.columbia.edu/tag/05AV)
* [Stacks Project, Tag 05F2](https://stacks.math.columbia.edu/tag/05F2)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05AV.** The relative weak assassin of an `𝒪_X`-module `F` along
`f : X ⟶ S`, viewed as a set of points of `X`. -/
@[stacks 05AV]
noncomputable abbrev relativeWeaklyAssociatedPoints {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) : Set X :=
  ⋃ s : S, (f.fiberι s) ''
    (Stacks.Divisors.weaklyAssociatedPoints ((Scheme.Modules.pullback (f.fiberι s)).obj F))

/-- **Stacks Project, Tag 05F2.** For a morphism locally of finite type the relative weak
assassin of a module is its relative assassin. -/
@[stacks 05F2]
theorem relativeWeaklyAssociatedPoints_eq_relativeAssassin {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (F : X.Modules) :
    relativeWeaklyAssociatedPoints f F = Stacks.Divisors.relativeAssassin f F := by
  unfold relativeWeaklyAssociatedPoints Stacks.Divisors.relativeAssassin
  congr 1
  funext s
  have hnoeth : IsLocallyNoetherian (f.fiber s) := by
    have hspec : IsLocallyNoetherian (Spec (S.residueField s)) := inferInstance
    have hft : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
      change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  rw [associatedPoints_eq_weaklyAssociatedPoints]

/-- The relative assassin is contained in the relative weak assassin, with no hypothesis: on
each fibre the associated points of the restricted module are weakly associated, by
Stacks 0589. -/
theorem relativeAssassin_subset_relativeWeaklyAssociatedPoints {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) :
    Stacks.Divisors.relativeAssassin f F ⊆ relativeWeaklyAssociatedPoints f F :=
  Set.iUnion_mono fun s ↦ Set.image_mono
    (Stacks.Divisors.associatedPoints_subset
      ((Scheme.Modules.pullback (f.fiberι s)).obj F))

end AlgebraicGeometry
