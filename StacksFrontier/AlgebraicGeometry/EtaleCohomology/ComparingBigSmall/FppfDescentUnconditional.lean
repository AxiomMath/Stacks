module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeCommutation
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SheafDescentProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.UnibranchLocallyIrreducible
public import StacksFrontier.AlgebraicGeometry.Morphisms.Integral.Fiber
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.CategoryTheory.Triangulated.ConnectingMorphismNatTrans
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FppfDescent
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FppfDescent
import StacksCore.Tactic.StacksAttribute

public import Mathlib.CategoryTheory.Monad.Comonadicity
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ChangeOfTopologyDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfToEtaleSquares
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.LocallyQuasiFiniteRefinement
public import StacksFrontier.CategoryTheory.Adjunction.CategoricalPullbackFullyFaithful
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Stacks Tag 0DEU: fppf descent of étale sheaves

Let `f : X ⟶ Y` be a morphism of the big fppf site which is flat, locally of finite presentation
and surjective. Then the functor from `Sh(Y_étale)` to the category of triples `(G, H, α)` with
`G ∈ Sh(X_étale)`, `H ∈ Sh((Sch/Y)_fppf)` and `α : a_X⁻¹G ≅ f_{big,fppf}⁻¹H` an isomorphism,
`F ↦ (f_small⁻¹F, a_Y⁻¹F, can)`, is an equivalence of categories. This is
`AlgebraicGeometry.isEquivalence_fppfSmallEtaleTripleFunctor`, proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.FppfDescent`; this file
registers it as Stacks Tag 0DEU and contains no declarations of its own.

## Main results

* `AlgebraicGeometry.isEquivalence_fppfSmallEtaleTripleFunctor` — **Stacks 0DEU**.

## References

* [Stacks, Tag 0DEU](https://stacks.math.columbia.edu/tag/0DEU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u})

end AlgebraicGeometry

add_to_stacks 0DEU AlgebraicGeometry.isEquivalence_fppfSmallEtaleTripleFunctor
