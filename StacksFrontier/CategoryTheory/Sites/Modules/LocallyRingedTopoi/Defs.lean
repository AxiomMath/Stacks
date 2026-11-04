module

public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.Morphisms
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedTopoi.InverseImage
import StacksCore.Tactic.StacksAttribute

/-!
# Locally ringed topoi

A ringed topos is *locally ringed* when the ringed site presenting it is a locally ringed site
in the sense of `AlgebraicGeometry.RingedSite.IsLocallyRinged`: the sections `0` and `1` of the
structure sheaf are nowhere equal, and every section is, on some covering, either a unit or has
unit complement.

The notion is well posed, in that it is a property of the ringed topos rather than of a chosen
presentation, because local ringedness of the presenting ringed site is invariant under an
equivalence of ringed topoi.

## Main definitions

* `AlgebraicGeometry.RingedTopos.IsLocallyRinged`: a locally ringed topos.

## Main results

* `AlgebraicGeometry.RingedTopos.isLocallyRinged_iff_of_equivalence`: an equivalence of ringed
  topoi preserves and reflects local ringedness.
* `AlgebraicGeometry.RingedSite.isLocallyRinged_toRingedTopos`: the ringed topos presented by a
  ringed site is locally ringed exactly when that ringed site is.

## Implementation notes

`AlgebraicGeometry.RingedTopos` and `AlgebraicGeometry.RingedSite` carry the same data, so the
definition is the site-level predicate read along `AlgebraicGeometry.RingedTopos.toRingedSite`,
and `isLocallyRinged_toRingedTopos` is a reassociation of fields. What has content is
`isLocallyRinged_iff_of_equivalence`, which is Stacks 04H7 part (2) restated for the predicate
and is the statement that makes the definition legitimate.

The definition has the three independent universes of `AlgebraicGeometry.RingedTopos`: the
morphisms of the site, its objects, and the sections of the structure sheaf. The invariance
statement inherits from Stacks 04H7 part (2) the restriction that the three universes of each
of the two ringed topoi agree.

## References

* [Stacks Project, Tag 04H8](https://stacks.math.columbia.edu/tag/04H8)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 04H7](https://stacks.math.columbia.edu/tag/04H7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

universe v u w

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 04H8.** A ringed topos is locally ringed when the ringed site
presenting it is a locally ringed site. -/
@[stacks 04H8]
abbrev RingedTopos.IsLocallyRinged (X : RingedTopos.{v, u, w}) : Prop :=
  RingedSite.IsLocallyRinged X.toRingedSite

/-- The ringed topos presented by a ringed site is locally ringed exactly when the ringed site
is locally ringed. -/
theorem RingedSite.isLocallyRinged_toRingedTopos (X : RingedSite.{u, u, u}) :
    X.toRingedTopos.IsLocallyRinged ↔ X.IsLocallyRinged :=
  Iff.rfl

/-- **Stacks Project, Tag 04H8**, well-posedness. Being locally ringed is a property of a ringed
topos and not of a site presenting it: by Stacks 04H7 part (2) an equivalence of ringed topoi
preserves and reflects it. -/
@[stacks 04H8 "well-posedness: invariance under an equivalence of ringed topoi"]
theorem RingedTopos.isLocallyRinged_iff_of_equivalence {X : RingedTopos.{u, u, u}}
    {Y : RingedTopos.{v, v, v}} (f : RingedToposHom X Y)
    [f.toToposHom.inverseImage.IsEquivalence] [IsIso f.fSharp] :
    Y.IsLocallyRinged ↔ X.IsLocallyRinged :=
  RingedToposHom.isLocallyRinged_iff_of_ringedToposEquivalence X Y f

end AlgebraicGeometry

end
