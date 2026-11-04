module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupEssentiallySmall
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# The derived dual on an essentially small ringed site

Let `(C, O)` be a ringed site whose underlying category is essentially small at the universe of
the sections of `O` — the small étale site of an algebraic space is one. The derived internal Hom
`RSheafHom(-, -)` of Stacks 0A97, and with it the dual `K^∨ = RSheafHom(K, O)` of Stacks 08JD, are
constructed in this library on a ringed site all three of whose universes agree. Restricting
sheaves of modules to a small model of `C` is an equivalence of categories (the Comparison
Lemma, Stacks 00XU), hence induces an equivalence of derived categories, and the dual of an object
of `D(O)` is defined here as the object corresponding to the dual of its restriction.

## Main definitions

* `AlgebraicGeometry.RingedSite.smallModelModulesEquivalence`: restriction of sheaves of modules
  to the small model, as an equivalence.
* `AlgebraicGeometry.RingedSite.smallModelDerivedEquivalence`: the induced equivalence of derived
  categories.
* `AlgebraicGeometry.RingedSite.essentiallySmallDerivedDual`: **the derived dual** `K^∨` of an
  object of `D(O)`.

## Main results

* `AlgebraicGeometry.RingedSite.smallModelDerivedEquivalence_essentiallySmallDerivedDual`: the
  restriction of `K^∨` to the small model is the dual `RSheafHom(K|, O|)` of the restriction.

## Implementation notes

The small model and its ringed site are
`Stacks.Cohomology.Torsors.Generators.smallModelRingedSite`, and restriction of sheaves of modules
to it is `AlgebraicGeometry.RingedSite.denseRestrictModules`, which is fully faithful and, since
restriction of abelian sheaves along the comparison with the small model is an equivalence
(`AlgebraicGeometry.RingedSite.isEquivalence_sheafPushforward_smallFunctor`), essentially
surjective.

## References

* [Stacks Project, Tag 08JD](https://stacks.math.columbia.edu/tag/08JD)
* [Stacks Project, Tag 0A97](https://stacks.math.columbia.edu/tag/0A97)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{c, u, u}) [EssentiallySmall.{u} X.C]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Restriction of sheaves of modules to a small model of the site, as an equivalence.** -/
def smallModelModulesEquivalence :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ≌
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O) :=
  haveI := isEquivalence_sheafPushforward_smallFunctor X
  haveI : (denseRestrictModules (smallTopology X) X (smallFunctor X)).IsEquivalence := {}
  (denseRestrictModules (smallTopology X) X (smallFunctor X)).asEquivalence

/-- Restriction of sheaves of modules to the small model is an additive functor. -/
instance : (smallModelModulesEquivalence X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The inverse of restriction of sheaves of modules to the small model is an additive functor. -/
instance : (smallModelModulesEquivalence X).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The derived categories of a ringed site and of its small model are equivalent**, by the
equivalence induced by restriction of sheaves of modules. -/
def smallModelDerivedEquivalence :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≌
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
        (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X).O)) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (smallModelModulesEquivalence X)

/-- **The derived dual** `K^∨ = RSheafHom(K, O)` of an object of `D(O)` on a ringed site whose
underlying category is essentially small: the object corresponding, under the equivalence with
the derived category of a small model, to the derived dual there. -/
def essentiallySmallDerivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (smallModelDerivedEquivalence X).inverse.obj
    (derivedDual (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)
      ((smallModelDerivedEquivalence X).functor.obj K))

/-- The restriction to the small model of the derived dual `K^∨` is the derived dual of the
restriction of `K`. -/
def smallModelDerivedEquivalence_essentiallySmallDerivedDual
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (smallModelDerivedEquivalence X).functor.obj (essentiallySmallDerivedDual X K) ≅
      derivedDual (Stacks.Cohomology.Torsors.Generators.smallModelRingedSite X)
        ((smallModelDerivedEquivalence X).functor.obj K) :=
  (smallModelDerivedEquivalence X).counitIso.app _

end AlgebraicGeometry.RingedSite

end
