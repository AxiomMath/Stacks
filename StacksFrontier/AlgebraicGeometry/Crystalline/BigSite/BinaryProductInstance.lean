module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductDescent
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.FibreProduct
public import StacksFrontier.CategoryTheory.Limits.Finite.Nonempty

/-!
# Nonempty finite limits in the big crystalline category

Fix a global crystalline situation `(p, (S, I, γ), X)`. The big crystalline category `CRIS(X/S)`
has products of pairs and all nonempty finite limits.

## Main results

* `Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening` — `CRIS(X/S)` has
  products of pairs.
* `Crystalline.GlobalCrystallineSituation.hasNonemptyFiniteLimits_thickening` — `CRIS(X/S)` has
  all nonempty finite limits.
* `Crystalline.GlobalCrystallineSituation.zariskiGluing` — Zariski descent for morphisms out of
  an object of `CRIS(X/S)`.
* `Crystalline.GlobalCrystallineSituation.instAffineBinaryProducts` — binary products in the
  affine case.

## References

* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 04AU](https://stacks.math.columbia.edu/tag/04AU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Crystalline

namespace GlobalCrystallineSituation

/-- Zariski descent for morphisms out of an object of `CRIS(X/S)`: a family of morphisms out of
the restrictions of `T` to the members of an open cover of its ambient scheme, agreeing on the
pairwise intersections, is the family of restrictions of a morphism out of `T`. -/
theorem zariskiGluing (S : GlobalCrystallineSituation.{u}) : ZariskiGluing S :=
  fun {T _ _} U hU g hg =>
    ⟨Thickening.glueHom U hU g fun i j =>
      hg i j _ _ (T.restrictOpenLE_restrictOpenHom _) (T.restrictOpenLE_restrictOpenHom _),
      fun i => Thickening.glueHom_restrictOpenHom U hU g _ i⟩

/-- Binary products in the affine case: two objects of `CRIS(X'/S')` whose thickened and ambient
schemes are affine, over a situation whose base and thickened space are affine and on which the
fixed prime is nilpotent on global sections, have a binary product. -/
instance instAffineBinaryProducts : AffineBinaryProducts.{u} where
  out _ hX hS hp A' B' hA _ hB _ :=
    haveI := hX
    haveI := hS
    haveI := hA
    haveI := hB
    hasBinaryProduct_of_isAffine hp A' B'

/-- The big crystalline category `CRIS(X/S)` has products of pairs. -/
instance instHasBinaryProductsThickening (S : GlobalCrystallineSituation.{u}) :
    HasBinaryProducts (Thickening S) :=
  hasBinaryProducts_thickening_of_glue instAffineBinaryProducts (zariskiGluing S)

/-- The big crystalline category `CRIS(X/S)` has all nonempty finite limits, in particular
products of pairs and fibre products. -/
@[stacks 07I9 "clause (1): CRIS(X/S) has all nonempty finite limits, in particular products of \
pairs and fibre products"]
theorem hasNonemptyFiniteLimits_thickening (S : GlobalCrystallineSituation.{u}) :
    HasNonemptyFiniteLimits (Thickening S) :=
  have : HasEqualizers (Thickening S) := hasEqualizers_of_hasPullbacks_and_binary_products
  hasNonemptyFiniteLimits_of_hasBinaryProducts_and_hasEqualizers _

end GlobalCrystallineSituation

end Crystalline

end
