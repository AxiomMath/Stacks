module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeVersusCompositeComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomologySupplement

/-!
# The `Ext`-side transport along an exact functor is the Leray edge morphism

Two comparisons between `Ext_A^n(X, -)` and `L ⋙ Ext_B^n(Y, -)` meet in this library, and until
now nothing related them.

* The **resolution side**: `Stacks.Cohomology.RightDerivedEdge.edge`, the edge morphism of the
  Grothendieck spectral sequence of a pair of composable functors, which is pinned on an arbitrary
  injective resolution by `Stacks.Cohomology.RightDerivedEdge.edge_app_eq`. The transition maps of
  the cohomology diagram of Stacks 09YQ are edge morphisms, by
  `Stacks.WeakSites.ColimitSiteCohomology.CohomologyCocone.diagram_map_eq_edge_app`.
* The **`Ext` side**: `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp`, which is Stacks 015Z
  — `Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` — conjugated by the
  `Ext`-to-derived-`Hom` bridge `extFunctorObjIsoRightDerivedCoyoneda`. Every "cohomology over `X`
  is cohomology on a localized site" comparison of this library is of that shape.

This file identifies the second with the first: componentwise, the inverse of
`extFunctorObjIsoComp` *is* the edge morphism, conjugated by the two `Ext`-to-derived-`Hom`
bridges and by the derived comparison of the two `Hom` functors.

## Main results

* `Stacks.Cohomology.ExtComparison.extFunctorObjIsoComp_inv_app_eq_edge_app` — **the component of
  the inverse of the `Ext`-side transport is the component of the Leray edge morphism**, so the
  `Ext`-side comparison and the edge comparison agree.
* `Stacks.Cohomology.ExtComparison.edge_app_eq_extFunctorObjIsoComp_inv_app` — the same equation
  solved for the edge morphism, which is the direction a consumer holding an edge morphism needs.

## Implementation notes

The proof is the composition of two facts and no new homological algebra:
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app`, which says the
edge morphism of an exact functor preserving injectives is the inverse of
`compRightDerivedNatIso`, and the definition of `extFunctorObjIsoComp` as a composite of
isomorphisms with that one in the middle.

The hypotheses are exactly those of `extFunctorObjIsoComp`: no exactness of `L` beyond what that
definition already asks, and no acyclicity. In particular this says nothing about
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIsoOfAcyclic`, whose engine is
`ModuleSheafCohomology.extComparisonIso` — the universality of δ-functors of Stacks 010T and 010U
— for which the library has no computation on a resolution. A consumer that needs to relate its
comparison to an edge morphism must take the `PreservesInjectiveObjects` route, which is what
`Stacks.Cohomology.BiggerSiteGlobal.sheafCohomologyIsoOfConstantSheafIso`,
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence'` and
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCohomologyFunctorIsoEtaleCohomology'` provide.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits CategoryTheory.Abelian

namespace Stacks.Cohomology.ExtComparison

universe v u u'

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A] [HasInjectiveResolutions A]
  {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B] [HasInjectiveResolutions B]
  (L : A ⥤ B) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L.PreservesInjectiveObjects] {X : A} {Y : B}
  (α : L ⋙ preadditiveCoyoneda.obj (op Y) ≅ preadditiveCoyoneda.obj (op X))

/-- **The `Ext`-side transport along an exact functor is the Leray edge morphism.** The component
at `Z` of the inverse of `extFunctorObjIsoComp L α n` is the component at `Z` of the edge morphism
`Stacks.Cohomology.RightDerivedEdge.edge L (Hom(Y, -)) n`, conjugated by the two
`Ext`-to-derived-`Hom` bridges `extFunctorObjIsoRightDerivedCoyoneda` and by the derived
comparison of `Hom(X, -)` with `L ⋙ Hom(Y, -)`.

This is the compatibility between the two ways this library computes such a comparison. The
`Ext` side is `compRightDerivedNatIso`, Stacks 015Z, by the definition of `extFunctorObjIsoComp`;
the resolution side is `edge`; and the two are inverse to one another by
`Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app`. -/
theorem extFunctorObjIsoComp_inv_app_eq_edge_app (n : ℕ) (Z : A) :
    (extFunctorObjIsoComp L α n).inv.app Z =
      (extFunctorObjIsoRightDerivedCoyoneda Y n).hom.app (L.obj Z) ≫
        (Stacks.Cohomology.RightDerivedEdge.edge L (preadditiveCoyoneda.obj (op Y)) n).app Z ≫
          (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso α.symm n).inv.app Z ≫
            (extFunctorObjIsoRightDerivedCoyoneda X n).inv.app Z := by
  rw [Stacks.Cohomology.RightDerivedEdge.edge_app_eq_compRightDerivedNatIso_inv_app]
  simp [extFunctorObjIsoComp]

/-- **The Leray edge morphism is the `Ext`-side transport along an exact functor.**
`extFunctorObjIsoComp_inv_app_eq_edge_app` solved for the edge morphism: this is the direction a
consumer holding an edge morphism — a transition map of the cohomology diagram of Stacks 09YQ, say
— needs in order to rewrite it as the `Ext`-side comparison. -/
theorem edge_app_eq_extFunctorObjIsoComp_inv_app (n : ℕ) (Z : A) :
    (Stacks.Cohomology.RightDerivedEdge.edge L (preadditiveCoyoneda.obj (op Y)) n).app Z =
      (extFunctorObjIsoRightDerivedCoyoneda Y n).inv.app (L.obj Z) ≫
        (extFunctorObjIsoComp L α n).inv.app Z ≫
          (extFunctorObjIsoRightDerivedCoyoneda X n).hom.app Z ≫
            (Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso α.symm n).hom.app Z := by
  rw [extFunctorObjIsoComp_inv_app_eq_edge_app L α n Z]
  simp

end Stacks.Cohomology.ExtComparison

end
