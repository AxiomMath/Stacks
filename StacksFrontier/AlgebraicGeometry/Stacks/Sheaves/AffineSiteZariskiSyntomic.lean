module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineSyntomicDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.AffineZariskiDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenCoarserSites

/-!
# The affine dense subsite for the Zariski and syntomic topologies (Stacks 0H0B)

`AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous` proves Stacks 0H0B
from the corresponding fact one level down, that the inclusion of the big affine category over
`S` into the big category over `S` is a dense subsite. This file records the two instances of
it left over by
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/AffineSiteEtaleSmooth.lean`: the big Zariski
topology (Stacks 020W) and the big syntomic topology (Stacks 06VD).

The big Zariski and big syntomic sites carried by a chosen big fppf site (Stacks 03FF) have the
same underlying categories as the fppf one — `AlgebraicGeometry.BigFppfSite.toBigZariskiSite`
and `.toBigSyntomicSite` change only the selected covering families — so no transport is
needed: the affine category, the ambient category and the inclusion of the one are those of the
other.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.inclusion_isSpecialCocontinuous_zariski` and
  `.inclusion_isSpecialCocontinuous_syntomic`: **Stacks 0H0B** for the Zariski and syntomic
  topologies.

Together with `.inclusion_isSpecialCocontinuous_etale`, `.inclusion_isSpecialCocontinuous_smooth`
and `.inclusion_isSpecialCocontinuous_fppf` these are all five topologies of the source.

## References

* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
* [Stacks Project, Tag 06VD](https://stacks.math.columbia.edu/tag/06VD)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AffineCategory

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Stacks 0H0B** for the Zariski topology: the inclusion of the affine subcategory into a
category fibred in groupoids is special cocontinuous from the associated affine Zariski site to
the associated Zariski site, and so induces an equivalence of the sheaf topoi. -/
@[stacks 0H0B "the Zariski topology"]
theorem inclusion_isSpecialCocontinuous_zariski (hp : p.IsFiberedInGroupoids) :
    IsSpecialCocontinuous
      (associatedAffineTopology B S hS p (BigAffineZariski.topology B.toBigZariskiSite S hS))
      (p.inheritedTopology (BigZariskiOver.topology B.toBigZariskiSite S hS))
      (inclusion B S hS p) :=
  inclusion_isSpecialCocontinuous B S hS p hp _ _
    (BigAffineZariski.inclusion_isSpecialCocontinuous B.toBigZariskiSite S hS).2

/-- **Stacks 0H0B** for the syntomic topology: the inclusion of the affine subcategory into a
category fibred in groupoids is special cocontinuous from the associated affine syntomic site to
the associated syntomic site, and so induces an equivalence of the sheaf topoi. -/
@[stacks 0H0B "the syntomic topology"]
theorem inclusion_isSpecialCocontinuous_syntomic (hp : p.IsFiberedInGroupoids) :
    IsSpecialCocontinuous
      (associatedAffineTopology B S hS p (BigAffineSyntomic.topology B.toBigSyntomicSite S hS))
      (p.inheritedTopology (BigSyntomicOver.topology B.toBigSyntomicSite S hS))
      (inclusion B S hS p) :=
  inclusion_isSpecialCocontinuous B S hS p hp _ _
    (BigAffineSyntomic.inclusion_isSpecialCocontinuous B.toBigSyntomicSite S hS).2

end AlgebraicGeometry.Stack.AffineCategory

end
