module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatRimSchlessingerStar
public import StacksFrontier.AlgebraicGeometry.Quot.ProperPushoutGluingUnconditional

/-!
# (RS\*) for `Spaces'_{fp, flat, proper}`, unconditionally

`AlgebraicGeometry.satisfiesRSStar_cartesianProperFlat` derives condition (RS\*) of Stacks 07Y8
for the stack `Spaces'_{fp, flat, proper}` (`AlgebraicGeometry.cartesianProperFlatProjection`)
from the statement of Stacks 0D1J, `AlgebraicGeometry.Space.ProperPushoutRS`, and
`AlgebraicGeometry.Space.properPushoutRS` proves that statement. This file composes the two: it
is the use the source makes of Stacks 0D1J in the proof of Stacks 0D3X ("has (RS\*) ... see
Lemma 0D1J").

No declaration here carries a Stacks tag.

## Main results

* `AlgebraicGeometry.satisfiesRSStar_cartesianProperFlat_unconditional`: (RS\*) for
  `Spaces'_{fp, flat, proper}` over any base scheme of the site.

## References

* [Stacks Project, Tag 0D1J](https://stacks.math.columbia.edu/tag/0D1J)
* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public section

open CategoryTheory Deformation.Artin

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **(RS\*) for the stack of finitely presented, flat and proper algebraic spaces.** Over any
base scheme `S` of the big fppf site, the stack `Spaces'_{fp, flat, proper}` satisfies condition
(RS\*) of Stacks 07Y8: this is Stacks 0D1J (`AlgebraicGeometry.Space.properPushoutRS`) read on the
fibres of the stack (`AlgebraicGeometry.satisfiesRSStar_cartesianProperFlat`). -/
theorem satisfiesRSStar_cartesianProperFlat_unconditional :
    SatisfiesRSStar B S hS (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) :=
  satisfiesRSStar_cartesianProperFlat B S hS (Space.properPushoutRS B S hS)

end AlgebraicGeometry

end
