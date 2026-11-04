module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsitePicard
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.DenseSubsiteRingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.InvertibleRankOneEssentiallySmall

/-!
# First cohomology of the units and the Picard group of an essentially small ringed site

`Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup` proves Tag 040E for a ringed
site all three of whose universes agree. That excludes the small étale ringed site of an
algebraic space, which is a `RingedSite.{u + 1, u, u}`. This file removes the restriction for a
ringed site whose underlying category is essentially small at the universe of the sections of
its structure sheaf, which is the case for the small étale site.

## Main results

* `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupOfEssentiallySmall`: Tag 040E
  on an essentially small locally ringed site.

## Implementation notes

The route is the repo's standard one for this situation, the same as in
`AlgebraicGeometry.RingedSite.isInvertible_of_isFiniteLocallyFreeOfRank_one_of_essentiallySmall`:
restrict to a small model of the site, where the existing statement applies, and carry both
sides back. The small model and its topology are that file's
`AlgebraicGeometry.RingedSite.smallFunctor` and `AlgebraicGeometry.RingedSite.smallTopology`,
reused here rather than restated; that restriction of abelian sheaves along the comparison
functor is an equivalence with no size hypothesis, because that functor is the functor of
`CategoryTheory.Equivalence.sheafCongr`, is its
`AlgebraicGeometry.RingedSite.isEquivalence_sheafPushforward_smallFunctor`.

The two transports are `Stacks.Cohomology.DenseSubsite.hAddEquiv` for the cohomology of the
units and `AlgebraicGeometry.RingedSite.picardGroupDenseRestrictAddEquiv` for the Picard group;
that the restricted ringed site has the restricted units sheaf as its sheaf of units is
`AlgebraicGeometry.RingedSite.unitsAddSheaf_denseRestrict`, which holds by `rfl`, and that it is
locally ringed is `AlgebraicGeometry.RingedSite.isLocallyRinged_denseRestrict`.

Instances about the small model's topology are bridged by assignment rather than by instance
search, because `AlgebraicGeometry.RingedSite.denseRestrict` is deliberately opaque.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe a w u₁ v₁

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u₁, v₁, w}) [EssentiallySmall.{w} X.C]

/-- The ringed site on a small model of the underlying site of `X`: all three of its universes
are the universe `w` of the sections of the structure sheaf, so the statements proved for a
ringed site with equal universes apply to it. -/
abbrev smallModelRingedSite : RingedSite.{w, w, w} :=
  RingedSite.denseRestrict (RingedSite.smallTopology X) X (RingedSite.smallFunctor X)

section

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasExt.{a} (Sheaf X.J AddCommGrpCat.{w})]
  [hE : HasExt.{a} (Sheaf (RingedSite.smallTopology X) AddCommGrpCat.{w})]

/-- **Stacks Project, Tag 040E on an essentially small ringed site.** Let `(C, O)` be a locally
ringed site whose underlying category is essentially small at the universe of the sections of
`O`. There is a canonical isomorphism of abelian groups `H^1(C, O^*) = Pic(O)`.

This is `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroup` with the three
universes of the ringed site independent. -/
@[stacks 040E "on an essentially small ringed site, with the universe of the sections of the \
structure sheaf independent of the universes of the site"]
def h1UnitsAddEquivPicardGroupOfEssentiallySmall
    (hX : AlgebraicGeometry.RingedSite.IsLocallyRinged X) :
    Sheaf.H.{a} (unitsAddSheaf X) 1 ≃+
      Stacks.SheafOfModules.Picard.PicardGroup X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 := by
  haveI := RingedSite.isEquivalence_sheafPushforward_smallFunctor X
  haveI : HasExt.{a} (Sheaf (smallModelRingedSite X).J AddCommGrpCat.{w}) := hE
  exact ((Stacks.Cohomology.DenseSubsite.hAddEquiv (RingedSite.smallTopology X) X.J
        (RingedSite.smallFunctor X) (unitsAddSheaf X) 1).trans
      (h1UnitsAddEquivPicardGroup (smallModelRingedSite X)
        (RingedSite.isLocallyRinged_denseRestrict (RingedSite.smallTopology X) X
          (RingedSite.smallFunctor X) hX))).trans
    (RingedSite.picardGroupDenseRestrictAddEquiv (RingedSite.smallTopology X) X
      (RingedSite.smallFunctor X)).symm

end

end Stacks.Cohomology.Torsors.Generators

end
