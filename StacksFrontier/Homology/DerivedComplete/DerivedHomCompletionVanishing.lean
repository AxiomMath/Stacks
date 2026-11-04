module

public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.TelescopeHom
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.MappingCocone
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.DerivedLimitModel
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionVanishing.VanishingCriteria

/-!
# Vanishing criteria for derived Hom from an affine localization

This file collects the parts `TelescopeHom`, `MappingCocone`, `DerivedLimitModel` and
`VanishingCriteria`.

Let `A` be a commutative ring, `f : A`, and `K` an object of `D(A)`. These files state the
equivalence between vanishing of the Ext groups from `A_f`, right orthogonality to `D(A_f)`,
vanishing of the derived limits `T(K, f)` and `T(H^p(K), f)`, the corresponding degree-zero and
degree-one conditions on cohomology, vanishing of derived Hom, and invertibility of the product
difference map.

## Main definitions

* `DerivedHomAway.derivedHomFromAway`: the value `RHom_A(A_f, K)` of the derived-Hom bifunctor.

## Main results

* `DerivedHomAway.tfae_ext_localization_vanishing`: the seven equivalent vanishing criteria,
  together with the derived-limit and cohomology descriptions of `RHom_A(A_f, K)`.
* `DerivedHomAway.derivedHomFromAwayIsDerivedLimit`: the derived-limit model for
  `RHom_A(A_f, K)`.
* `DerivedHomAway.derivedHomFromAwayHomologyIsoExt`: the resulting homology--Ext equivalence.

## Implementation notes

The derived-Hom object is the value of the derived-Hom bifunctor of
`StacksDraft.DerivedHom.derivedHomAdjunction`. The ring, its localization, and all module
categories use one universe level. The homology--Ext comparison is an additive equivalence
between the underlying homology group and the group of derived morphisms.

## References

* [The Stacks Project, Tag 091P](https://stacks.math.columbia.edu/tag/091P)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/
