module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaRight

/-!
# The right-handed projection-formula map is compatible with a commutative square

Let `g' ≫ f = f' ≫ g` be a commutative square of ringed spaces, with `f : X ⟶ Y`,
`f' : X' ⟶ Y'`, `g : Y' ⟶ Y` and `g' : X' ⟶ X`, and let `E ∈ D(𝒪_X)`, `K ∈ D(𝒪_Y)`.
[Stacks, Tag 0B6B] asserts that the projection-formula map
`Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` is compatible with derived base change along the square.
This file proves the same compatibility for the projection-formula map with the pushforward in
the *right* tensor factor, `K ⊗^L Rf_*E ⟶ Rf_*(Lf^*K ⊗^L E)`: the comparison of
[Stacks, Tag 079U] for `g`, followed by the base change map of [Stacks, Tag 08HY] in the second
tensor factor and by the right-handed projection-formula map for `f'`, equals the derived
pullback along `g` of the right-handed projection-formula map for `f`, followed by base change
and by `Rf'_*` of the comparison for `g'` and of the identification of the two iterated derived
pullbacks in the first tensor factor.

## Main results

* `Stacks.AffineProjectionFormula.tensorComparisonCompatible_swap`: the compatibility of four
  tensor comparisons around a square, for the bifunctors with their arguments interchanged, is
  the compatibility of the original comparisons at the interchanged pair.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight_derivedBaseChangeMap`:
  the diagram `ProjectionFormulaBaseChangeSquare` at the right-handed projection-formula map,
  for arbitrary `E` and `K`.
* `Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMapRight_derivedBaseChangeMap_eq`:
  the same, with the equation of the diagram written out.

## Implementation notes

The right-handed projection-formula map is the abstract adjunction-tensor map at the derived
tensor products precomposed with the interchange of factors, and the comparisons of
[Stacks, Tag 079U] read with their arguments interchanged.  The abstract diagram chase
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square` holds for arbitrary
bifunctors, so it applies verbatim; its one hypothesis, the coherence of the four comparisons
around the square, holds for the interchanged comparisons at `(M, N)` because it is, by
definition, the coherence of the original comparisons at `(N, M)`.

## References

* [Stacks Project, Tag 0B6B](https://stacks.math.columbia.edu/tag/0B6B)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped CategoryTheory.Prod
open Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.DerivedTensor.RingedSite

namespace Stacks.AffineProjectionFormula

variable {S T S' T' : Type*} [Category S] [Category T] [Category S'] [Category T']
  {Lf : S ⥤ T} {Lf' : S' ⥤ T'} {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lc : S ⥤ T'}
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
  (A : S × S ⥤ S) (A' : S' × S' ⥤ S') (B : T × T ⥤ T) (B' : T' × T' ⥤ T')
  (αf : A ⋙ Lf ⟶ Lf.prod Lf ⋙ B) (αf' : A' ⋙ Lf' ⟶ Lf'.prod Lf' ⋙ B')
  (αg : A ⋙ Lg ⟶ Lg.prod Lg ⋙ A') (αg' : B ⋙ Lg' ⟶ Lg'.prod Lg' ⋙ B')

open Stacks.Cohomology.DerivedProjectionFormula in
/-- The compatibility of four tensor comparisons around a square, for the bifunctors with their
arguments interchanged and the comparisons read accordingly, holds at `(M, N)` as soon as the
compatibility of the original comparisons holds at `(N, M)`. -/
lemma tensorComparisonCompatible_swap {M N : S}
    (h : TensorComparisonCompatible eg ef A A' B B' αf αf' αg αg' N M) :
    TensorComparisonCompatible eg ef
      (CategoryTheory.Prod.swap S S ⋙ A) (CategoryTheory.Prod.swap S' S' ⋙ A')
      (CategoryTheory.Prod.swap T T ⋙ B) (CategoryTheory.Prod.swap T' T' ⋙ B')
      (comparisonSwap A B αf) (comparisonSwap A' B' αf')
      (comparisonSwap A A' αg) (comparisonSwap B B' αg') M N :=
  h

end Stacks.AffineProjectionFormula

namespace Stacks.Cohomology.DerivedProjectionFormula

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X' X Y' Y : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y) (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The right-handed projection-formula map is compatible with a commutative square of ringed
spaces.**

For a commutative square `g' ≫ f = f' ≫ g` of ringed spaces and arbitrary `E ∈ D(𝒪_X)`,
`K ∈ D(𝒪_Y)`, the diagram `ProjectionFormulaBaseChangeSquare` commutes at the right-handed
projection-formula map `projectionFormulaMapRight` for `f` and for `f'`, the derived base change
map of Stacks 08HY and the identification `derivedPullbackSquareIso`, with the derived tensor
products read with their arguments interchanged.  This is
`projectionFormulaMap_derivedBaseChangeMap` with the pushforward in the right tensor factor. -/
@[stacks 0B6B "the right-handed form: the pushforward in the right tensor factor"]
theorem projectionFormulaMapRight_derivedBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ProjectionFormulaBaseChangeSquare (derivedPushforward f) (derivedPushforward f')
      (derivedPullback f) (derivedPullback f') (derivedPullback g) (derivedPullback g')
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y'.sheaf))
      (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X'.sheaf))
      (pullbackTensorComparisonSwap g) (pullbackTensorComparisonSwap g') E K
      (projectionFormulaMapRight f K E)
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
        ((CategoryTheory.Prod.swap _ _ ⋙
          Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
            (E, (derivedPullback f).obj K)))
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E)
      ((derivedPullbackSquareIso g' f' f g sq).inv.app K)
      (projectionFormulaMapRight f' ((derivedPullback g).obj K) ((derivedPullback g').obj E)) :=
  adjunctionTensorMap_derivedBaseChangeMap (derivedAdjunction f) (derivedAdjunction f')
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor Y'.sheaf))
    (CategoryTheory.Prod.swap _ _ ⋙ Functor.uncurry.obj (derivedTensorProductFunctor X'.sheaf))
    (pullbackTensorComparisonSwap f) (pullbackTensorComparisonSwap f')
    (pullbackTensorComparisonSwap g) (pullbackTensorComparisonSwap g')
    (Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft g' f' f g sq)
    (derivedPullbackCompIsoCanonical g' f) E K
    (Stacks.AffineProjectionFormula.tensorComparisonCompatible_swap _ _ _ _ _ _ _ _ _ _
      (tensorComparisonCompatible_of_comparisonSquare _ _ _ _ _ _ _ _
        (Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square
          g' f' f g sq) _ _))

/-- **The right-handed projection-formula map is compatible with a commutative square of ringed
spaces**, with the equation written out: the comparison of Stacks 079U for `g` at
`(K, Rf_*E)`, followed by the derived base change map of Stacks 08HY in the second tensor factor
and by the right-handed projection-formula map for `f'`, equals `Lg^*` of the right-handed
projection-formula map for `f`, followed by the base change map at `Lf^*K ⊗^L E` and by `Rf'_*`
of the comparison for `g'` and of the identification `derivedPullbackSquareIso` in the first
tensor factor. -/
theorem projectionFormulaMapRight_derivedBaseChangeMap_eq
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (pullbackTensorComparison g).app (K, (derivedPushforward f).obj E) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y'.sheaf)).map
          (𝟙 ((derivedPullback g).obj K) ×ₘ
            Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq E) ≫
        projectionFormulaMapRight f' ((derivedPullback g).obj K) ((derivedPullback g').obj E) =
      (derivedPullback g).map (projectionFormulaMapRight f K E) ≫
        Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap g' f' f g sq
          ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).obj
            ((derivedPullback f).obj K, E)) ≫
        (derivedPushforward f').map
          ((pullbackTensorComparison g').app ((derivedPullback f).obj K, E) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor X'.sheaf)).map
              ((derivedPullbackSquareIso g' f' f g sq).inv.app K ×ₘ
                𝟙 ((derivedPullback g').obj E))) :=
  projectionFormulaMapRight_derivedBaseChangeMap g' f' f g sq E K

end Stacks.Cohomology.DerivedProjectionFormula

end
