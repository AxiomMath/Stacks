module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.AffineDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.AffineDenseSubsite

/-!
# The affine dense subsite for the étale and smooth topologies (Stacks 0H0B)

`AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous` proves Stacks 0H0B
from the corresponding fact one level down, that the inclusion of the big affine category over
`S` into the big category over `S` is a dense subsite. This file records the two instances of
it whose downstairs input is available: the big étale topology (Stacks 021E) and the big smooth
topology (Stacks 06VC).

The big étale and big smooth sites carried by a chosen big fppf site (Stacks 03FF) have the
same underlying categories as the fppf one — `AlgebraicGeometry.BigFppfSite.toBigEtaleSite` and
`.toBigSmoothSite` change only the selected covering families — so no transport is needed: the
affine category, the ambient category and the inclusion of the one are those of the other.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous_etale` and
  `.inclusion_isSpecialCocontinuous_smooth`: **Stacks 0H0B** for the étale and smooth
  topologies.

## Implementation notes

The Zariski and syntomic instances are
`AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous_zariski` and
`.inclusion_isSpecialCocontinuous_syntomic` of
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/AffineSiteZariskiSyntomic.lean`, which reads the
same general statement against the dense-subsite property of the big affine Zariski and big
affine syntomic inclusions (Stacks 020W and 06VD).

## References

* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
* [Stacks Project, Tag 06VC](https://stacks.math.columbia.edu/tag/06VC)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AffineCategory

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Stacks 0H0B** for the étale topology: the inclusion of the affine subcategory into a
category fibred in groupoids is special cocontinuous from the associated affine étale site to
the associated étale site, and so induces an equivalence of the sheaf topoi. -/
@[stacks 0H0B "the étale topology"]
theorem inclusion_isSpecialCocontinuous_etale (hp : p.IsFiberedInGroupoids) :
    IsSpecialCocontinuous
      (associatedAffineTopology B S hS p (BigAffineEtale.topology B.toBigEtaleSite S hS))
      (p.inheritedTopology (BigEtaleOver.topology B.toBigEtaleSite S hS))
      (inclusion B S hS p) :=
  inclusion_isSpecialCocontinuous B S hS p hp _ _
    (BigAffineEtale.inclusion_isSpecialCocontinuous B.toBigEtaleSite S hS).2

/-- **Stacks 0H0B** for the smooth topology: the inclusion of the affine subcategory into a
category fibred in groupoids is special cocontinuous from the associated affine smooth site to
the associated smooth site, and so induces an equivalence of the sheaf topoi. -/
@[stacks 0H0B "the smooth topology"]
theorem inclusion_isSpecialCocontinuous_smooth (hp : p.IsFiberedInGroupoids) :
    IsSpecialCocontinuous
      (associatedAffineTopology B S hS p (BigAffineSmooth.topology B.toBigSmoothSite S hS))
      (p.inheritedTopology (BigSmoothOver.topology B.toBigSmoothSite S hS))
      (inclusion B S hS p) :=
  inclusion_isSpecialCocontinuous B S hS p hp _ _
    (BigAffineSmooth.inclusion_isSpecialCocontinuous B.toBigSmoothSite S hS).2

end AlgebraicGeometry.Stack.AffineCategory

end
