module

public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSitePrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products in big ph sites

For a big ph site `B` containing a scheme `S`, the underlying category of `B`, the big ph
category over `S`, and its affine full subcategory all admit fibre products, and their
canonical functors to the category of all schemes preserve them.  The object `S / S` is final
in the big ph category over `S`.

## Main results

* `AlgebraicGeometry.BigPHSite.hasPullbacks_schemes` (tagged here): the underlying category
  of a big ph site admits fibre products.
* `AlgebraicGeometry.BigPHSite.preservesPullbacks_inclusion` (tagged here): its inclusion
  into schemes preserves fibre products.
* `AlgebraicGeometry.hasPullbacks_bigPHOver`: the big ph category over `S` admits fibre
  products.
* `AlgebraicGeometry.preservesPullbacks_bigPHOverToScheme`: its canonical functor to schemes
  preserves fibre products.
* `AlgebraicGeometry.isTerminal_mkId_bigPHOver`: `S / S` is a final object of the big ph
  category over `S`.
* `AlgebraicGeometry.hasPullbacks_bigAffinePH`: the big affine ph category over `S` admits
  fibre products.
* `AlgebraicGeometry.preservesPullbacks_bigAffinePHToScheme`: its canonical functor to
  schemes preserves fibre products.

## Implementation notes

The fibre products of the underlying category of a big ph site, and their preservation by
its inclusion into schemes, are instances declared in
`StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSitePrecoverage` and registered here.
The big ph category over `S` is a slice, whose fibre products are preserved by the forgetful
functor.
The affine subcategory is closed under fibre products because a fibre product of affine
schemes over an affine scheme is affine.

## References

* [Stacks Project, Tag 0DBN](https://stacks.math.columbia.edu/tag/0DBN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

add_to_stacks 0DBN "fibre products in the big ph site"
  AlgebraicGeometry.BigPHSite.hasPullbacks_schemes

add_to_stacks 0DBN "preservation by the big ph site inclusion"
  AlgebraicGeometry.BigPHSite.preservesPullbacks_inclusion

variable (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0DBN, second part.** The big ph category over `S` admits fibre products. -/
@[stacks 0DBN "fibre products in the big ph slice"]
public theorem hasPullbacks_bigPHOver : HasPullbacks (BigPHOver B S hS) := inferInstance

/-- **Stacks 0DBN, second part.** The canonical functor from the big ph category over `S` to
the category of all schemes preserves fibre products. -/
@[stacks 0DBN "preservation by the big ph slice functor to schemes"]
public theorem preservesPullbacks_bigPHOverToScheme :
    PreservesLimitsOfShape WalkingCospan (BigPHOver.toScheme B S hS) := inferInstance

/-- **Stacks 0DBN, last part.** The final object of the big ph category over `S` is `S / S`,
the identity of `S` viewed as an object over `S`. -/
@[stacks 0DBN "the final object of the big ph slice is S / S"]
public noncomputable def isTerminal_mkId_bigPHOver :
    IsTerminal (C := BigPHOver B S hS) (Over.mk (𝟙 (B.obj S hS))) :=
  Over.mkIdTerminal

/-- The inclusion of the big affine ph category into the big ph category over `S` creates
fibre products, because a fibre product of affine schemes over an affine base is affine. -/
private noncomputable instance createsPullbacks_bigAffinePHInclusion :
    CreatesLimitsOfShape WalkingCospan (BigAffinePH.inclusion B S hS) where
  CreatesLimit := fun {F} => by
    let G := BigPHOver.toScheme B S hS
    let D := F ⋙ BigAffinePH.inclusion B S hS
    letI (j : WalkingCospan) : IsAffine (G.obj (D.obj j)) := (F.obj j).property
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    exact createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _)) (by
      let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
        (D.map WalkingCospan.Hom.inr)
      exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance)

/-- **Stacks 0DBN, third part.** The big affine ph category over `S` admits fibre
products. -/
@[stacks 0DBN "fibre products in the big affine ph site"]
public instance hasPullbacks_bigAffinePH : HasPullbacks (BigAffinePH B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (BigAffinePH.inclusion B S hS)

/-- **Stacks 0DBN, third part.** The canonical functor from the big affine ph category over
`S` to the category of all schemes preserves fibre products. -/
@[stacks 0DBN "preservation by the big affine ph functor to schemes"]
public instance preservesPullbacks_bigAffinePHToScheme :
    PreservesLimitsOfShape WalkingCospan (BigAffinePH.toScheme B S hS) :=
  comp_preservesLimitsOfShape _ _

end AlgebraicGeometry
