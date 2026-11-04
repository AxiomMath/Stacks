module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquareOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
import StacksCore.Tactic.StacksAttribute

/-!
# The projection formula map and a base change square of ringed topoi

For a commutative square of morphisms of ringed topoi

```
             g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
      |  f'                |  f
      v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
             g
```

the map `Rf_*E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^*K)` of Equation 21.50.0.1 is compatible with the base
change map of [Stacks, Tag 07A7]; this is [Stacks, Tag 0E48].

The four arrows are morphisms of ringed topoi in the two-field sense of [Stacks, Tag 01D3],
part (2): a morphism of the underlying topoi together with the map of structure sheaves.

## Main results

* `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square`:
  **[Stacks, Tag 0E48]**, the projection formula map is compatible with the base change map
  around a commutative square of morphisms of ringed topoi.

## Implementation notes

The map of Equation 21.50.0.1 along `f` is `CategoryTheory.adjunctionTensorMap` at the derived
adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6] and the forward map of [Stacks, Tag 07A4], as in
`Stacks.Cohomology.ProjectionFormulaOnRingedTopoi.projectionFormulaMap`; it is written out in
the statement.  The hexagon is
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, whose one input, the
compatibility of the four comparisons of [Stacks, Tag 07A4] around the square, follows from the
composition law of [Stacks, Tag 07A4]: it is
`Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`.

## References

* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPushforward Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)
open Stacks.Sheaves.DerivedPullback.OfToposHom (derivedPullbackTensorIso)

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X)
  (f' : RingedToposHom X' Y') (g : RingedToposHom Y' Y)

/-- **[Stacks, Tag 0E48].**  For a commutative square of morphisms of ringed topoi

```
             g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
      |  f'                |  f
      v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
             g
```

and `E` in `D(𝒪_C)`, `K` in `D(𝒪_D)`, the map `p` of Equation 21.50.0.1 is compatible with the
base change map `b` of [Stacks, Tag 07A7]: going down the left (`t`, the comparison of
[Stacks, Tag 07A4] for `g`, then `b ⊗ 1`, then `p` for `f'`) equals going down the right (`Lg^*`
of `p` for `f`, then `b`, then `R(f')_*` of `t` for `g'` followed by `1 ⊗ c`, where
`c : L(g')^*Lf^*K ⟶ L(f')^*Lg^*K` identifies the two iterated pullbacks around the square), as
maps `Lg^*(Rf_*E ⊗^L K) ⟶ R(f')_*(L(g')^*E ⊗^L L(f')^*Lg^*K)` in `D(𝒪_{D'})`. -/
@[stacks 0E48]
theorem projectionFormulaMap_baseChange_square (h : g.comp f' = f.comp g')
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackTensorIso g).hom.app ((derivedPushforward f).obj E, K) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
            (derivedBaseChangeMap f g' f' g h E ×ₘ 𝟙 ((derivedPullback g).obj K)) ≫
          adjunctionTensorMap (derivedAdjunction f')
            (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
            (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
            (derivedPullbackTensorIso f').hom
            ((derivedPullback g').obj E) ((derivedPullback g).obj K) =
      (derivedPullback g).map
          (adjunctionTensorMap (derivedAdjunction f)
            (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
            (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
            (derivedPullbackTensorIso f).hom E K) ≫
        derivedBaseChangeMap f g' f' g h
            (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K)) ≫
          (derivedPushforward f').map
            ((derivedPullbackTensorIso g').hom.app (E, (derivedPullback f).obj K) ≫
              (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
                (𝟙 ((derivedPullback g').obj E) ×ₘ
                  (Stacks.AffineProjectionFormula.squareCompositeIso
                    (derivedPullbackCompIsoLeft f' g)
                    (derivedPullbackCompIsoRight f g' f' g h)).inv.app K)) :=
  Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
    (derivedAdjunction f) (derivedAdjunction f')
    (derivedPullbackCompIsoLeft f' g) (derivedPullbackCompIsoRight f g' f' g h)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
    (derivedPullbackTensorIso f).hom (derivedPullbackTensorIso f').hom
    (derivedPullbackTensorIso g).hom (derivedPullbackTensorIso g').hom
    E K
      (Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso
        f g' f' g h _ _)

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
