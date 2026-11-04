module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
import StacksCore.Tactic.StacksAttribute

/-!
# `𝐆_m`-torsors on the small étale site and first cohomology

Tag 03AJ classifies the torsors under an abelian sheaf on an arbitrary site by the first
cohomology of that sheaf. Read at `𝐆_m` on the small étale site of a scheme, it identifies
`H¹_ét(X, 𝐆_m)` with the isomorphism classes of `𝐆_m`-torsors there.

## Main definitions

* `Stacks.Kummer.multiplicativeTorsorIsoClasses`: the isomorphism classes of `𝐆_m`-torsors on
  the small étale site of a scheme.
* `Stacks.Kummer.multiplicativeTorsorIsoClassesEquivH1`: the bijection of Tag 03AJ, read at
  `𝐆_m` on the small étale site.

## Implementation notes

The classification of Tag 03AJ, `Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`, is
universe polymorphic in the objects and the morphisms of the site and in the universe of the
coefficient sheaf, so it applies to the small étale site — whose objects are one universe above
its morphisms — with no restriction. Only the two size side-conditions `HasSheafify` and
`HasExt` have to be carried as instance arguments, exactly as elsewhere on this site: the
universe in which the `Ext`-groups live is a parameter of `HasExt` and is not determined by the
site.

Nothing here carries a `stacks` attribute. Tag 03AJ is registered where it is proved, on
`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1`, and these are that theorem read at one
sheaf; restating the tag on an instantiation would register it twice.

This is only the torsor side. It says nothing about invertible modules, and so is not any part
of Tag 03P8: identifying these torsor classes with a Picard group is Tag 040E, whose
development is available on a ringed site whose objects and morphisms share a universe and so
not on the small étale site. See
`StacksFrontier.AlgebraicGeometry.Picard.ZariskiSiteFirstCohomology` for where that stands.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.Torsors

universe w v u

namespace Stacks.Kummer

variable (X : Scheme.{u})
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]

/-- The isomorphism classes of `𝐆_m`-torsors on the small étale site of a scheme. -/
abbrev multiplicativeTorsorIsoClasses := torsorIsoClasses (multiplicativeSheaf.{u, v} X)

variable [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]

/-- **Tag 03AJ at `𝐆_m` on the small étale site.** The isomorphism classes of `𝐆_m`-torsors on
the small étale site of a scheme are canonically in bijection with `H¹_ét(X, 𝐆_m)`. -/
def multiplicativeTorsorIsoClassesEquivH1 :
    torsorIsoClasses (multiplicativeSheaf.{u, v} X) ≃
      Sheaf.H.{w} (multiplicativeSheaf.{u, v} X) 1 :=
  torsorIsoClassesEquivH1 (multiplicativeSheaf.{u, v} X)

end Stacks.Kummer

end
