module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of quasi-coherent modules on the small étale site

The small étale site of a scheme is essentially small, so abelian presheaves on it have a
sheafification which is exact and whose unit is a weak equivalence exactly on the locally
bijective maps. With those two facts in place the category of quasi-coherent modules on the
small étale site is closed under the operations of a tensor category, and in particular the
tensor product of two quasi-coherent modules is quasi-coherent.

## Main results

* `AlgebraicGeometry.smallEtale_hasSheafify` — abelian presheaves on the small étale site
  sheafify.
* `AlgebraicGeometry.smallEtale_wEqualsLocallyBijective` — on the small étale site the weak
  equivalences for abelian sheafification are the locally bijective maps.
* `AlgebraicGeometry.tensorSheaf_isQuasicoherent` (elsewhere) is the tensor-product clause of
  Tag 0GNB; it is stated for an arbitrary ringed space, hence applies to the small étale site
  of a scheme without a second, site-specific tensor construction.

## Implementation notes

Both instances come from essential smallness of the site
(`AlgebraicGeometry.SmallEtale.essentiallySmall`) through
`CategoryTheory.hasSheafifyEssentiallySmallSite` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`, so neither
needs the étale topology beyond the size of its index category, and neither has to be
transported from an over-site.

`AlgebraicGeometry.smallEtale_hasSheafify` gives `CategoryTheory.HasWeakSheafify` by instance
search, so it is stated in the stronger form which also carries exactness of sheafification.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Abelian presheaves on the small étale site of a scheme have an exact sheafification. -/
@[instance] public theorem smallEtale_hasSheafify :
    HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- On the small étale site of a scheme, the maps of abelian presheaves inverted by
sheafification are exactly the locally bijective ones. -/
@[instance] public theorem smallEtale_wEqualsLocallyBijective :
    (SmallEtale.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  .ofEssentiallySmall (SmallEtale.topology B S hS)

add_to_stacks 0GNB "tensor_products" AlgebraicGeometry.tensorSheaf_isQuasicoherent

end AlgebraicGeometry

end
