module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardShrink
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupEssentiallySmall

/-!
# The Picard group of an algebraic space is first cohomology of the units

For an algebraic space `Z` over `S`, the first cohomology of the sheaf of units of the structure
sheaf on the small étale site of `Z` is the Picard group `Pic(Z)`. This is Tag 040E at the small
étale ringed site, which is locally ringed by Tag 04KH.

## Main definitions

* `AlgebraicGeometry.Space.unitsAddSheafEtale`: the sheaf of units of `𝒪_Z` on the small étale
  site of `Z`, written additively.
* `AlgebraicGeometry.Space.h1UnitsAddEquivPicardGroup`: the canonical isomorphism
  `H^1(Z_étale, 𝒪_Z^*) ≅ Pic(Z)`.

## Implementation notes

The small étale ringed site is a `RingedSite.{u + 1, u, u}`, so the form of Tag 040E that
applies is `Stacks.Cohomology.Torsors.Generators.h1UnitsAddEquivPicardGroupOfEssentiallySmall`;
essential smallness at the projection spelling is
`AlgebraicGeometry.Space.smallEtaleRingedSite_essentiallySmall`, which that module documents as
something that must stay a theorem rather than an instance, so it is installed by `haveI`
here.

That statement produces `Stacks.SheafOfModules.Picard.PicardGroup`, the universe-shrunk Picard
group of Tag 040B, while `AlgebraicGeometry.Space.picardGroup` is
`Stacks.SheafOfModules.PicardGroup`, the unshrunk one; the two are identified by
`Stacks.SheafOfModules.picardGroupShrinkAddEquiv`, compatibly with the class of an invertible
module.

The `Ext` universe is `u + 1`, where the hypothesis is discharged by
`AlgebraicGeometry.Space.hasExt_sheaf_smallEtale` rather than carried, and the small model of
the site gets its own `HasExt` from `CategoryTheory.HasExt.standard`. Both are installed by
`haveI` at the projection spellings, which instance search does not reach on its own.

## References

* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
* [Stacks Project, Tag 04KH](https://stacks.math.columbia.edu/tag/04KH)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.Torsors.Generators

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Z : AlgebraicSpaces B S hS)

/-- **The sheaf of units of an algebraic space**, on its small étale site, written additively so
that it can be used as a coefficient sheaf for cohomology. -/
abbrev unitsAddSheafEtale : Sheaf (SmallEtale.topology B S hS Z.1) AddCommGrpCat.{u} :=
  unitsAddSheaf (smallEtaleRingedSite B S hS Z.1 Z.2)

/-- **Stacks 040E for an algebraic space.** The first cohomology of the sheaf of units on the
small étale site of an algebraic space `Z` is the Picard group of `Z`. -/
@[stacks 040E "for the small étale site of an algebraic space"]
def h1UnitsAddEquivPicardGroup :
    Sheaf.H.{u + 1} (unitsAddSheafEtale B S hS Z) 1 ≃+ picardGroup Z := by
  haveI := smallEtaleRingedSite_essentiallySmall B S hS Z.1 Z.2
  haveI : HasExt.{u + 1} (Sheaf (smallEtaleRingedSite B S hS Z.1 Z.2).J AddCommGrpCat.{u}) :=
    hasExt_sheaf_smallEtale B S hS Z.1
  haveI : HasExt.{u + 1} (Sheaf (AlgebraicGeometry.RingedSite.smallTopology
      (smallEtaleRingedSite B S hS Z.1 Z.2)) AddCommGrpCat.{u}) := HasExt.standard _
  exact (h1UnitsAddEquivPicardGroupOfEssentiallySmall (smallEtaleRingedSite B S hS Z.1 Z.2)
    (smallEtaleRingedSite_isLocallyRinged B S hS Z.1 Z.2)).trans
      (Stacks.SheafOfModules.picardGroupShrinkAddEquiv
        (structureSheaf B S hS Z.1 Z.2).obj
        (structureRingPresheaf_isSheaf B S hS Z.1 Z.2)).symm

end AlgebraicGeometry.Space

end
