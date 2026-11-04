module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquareOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Compatibility of the relative cup product with a base change square of ringed topoi

For a commutative square `g ∘ f' = f ∘ g'` of morphisms of ringed topoi and arbitrary `K`, `L`
in `D(𝒪_C)`, the relative cup product of [Stacks, Tag 0B6C] is compatible with the base change
map of [Stacks, Tag 07A7] and the comparisons of [Stacks, Tag 07A4]; this is [Stacks, Tag 0H9A].

## Main results

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_baseChange_square`:
  **[Stacks, Tag 0H9A]**, with no hypothesis beyond the commutativity of the square.

## Implementation notes

The statement is `adjunctionCupProduct_baseChange_square` at the derived adjunctions of
[Stacks, Tag 07A6] and the comparisons of [Stacks, Tag 07A4]; its one input, the compatibility
of the four comparisons around the square, is
`Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`.

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AffineProjectionFormula
open Stacks.Cohomology.DerivedBaseChangeOnTopoi
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.Sheaves.DerivedPullback
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

/-! ### Tag 0H9A for a commutative square of morphisms of ringed topoi -/

section ToposSquare

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
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : RingedToposHom X Y) (g' : RingedToposHom X' X) (f' : RingedToposHom X' Y')
  (g : RingedToposHom Y' Y) (h : g.comp f' = f.comp g')

/-- **[Stacks, Tag 0H9A].**  For a commutative square of morphisms of ringed topoi

```
                g'
  (Sh(C'), 𝒪_{C'}) --→ (Sh(C), 𝒪_C)
        |  f'                |  f
        v                    v
  (Sh(D'), 𝒪_{D'}) --→ (Sh(D), 𝒪_D)
                g
```

and arbitrary `K`, `L` in `D(𝒪_C)`, the relative cup product of [Stacks, Tag 0B6C] is compatible
with the square: the composite down the left (the comparison of [Stacks, Tag 07A4] for `g`, then
the base change map of [Stacks, Tag 07A7] in each tensor factor) and along the bottom (the
relative cup product for `f'`) equals the composite along the top (`Lg^*` of the relative cup
product for `f`) and down the right (the base change map, then `R(f')_*` of the comparison of
[Stacks, Tag 07A4] for `g'`), as maps
`Lg^*(Rf_*K ⊗^L Rf_*L) ⟶ R(f')_*(L(g')^*K ⊗^L L(g')^*L)` in `D(𝒪_{D'})`.

The four morphisms are morphisms of ringed topoi in the sense of Tag 01D3, part (2), and the
only hypothesis on them is the commutativity `h` of the square.  The relative cup product of
Tag 0B6C is written out as `adjunctionCupProduct` of the derived adjunction of Tag 07A6 and the
comparison of Tag 07A4. -/
@[stacks 0H9A]
theorem relativeCupProduct_baseChange_square
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
          ((Stacks.Cohomology.DerivedPushforward.derivedPushforward f).obj K,
            (Stacks.Cohomology.DerivedPushforward.derivedPushforward f).obj L) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
            (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMap f g' f' g h K ×ₘ
              Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMap f g' f' g h L) ≫
          adjunctionCupProduct (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction f')
            (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
            (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
            (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f').hom
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback g').obj K)
            ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback g').obj L) =
      (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback g).map
          (adjunctionCupProduct (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction f)
            (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
            (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
            (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom K L) ≫
        Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedBaseChangeMap f g' f' g h
            (((derivedTensorProductFunctor X.O).obj K).obj L) ≫
          (Stacks.Cohomology.DerivedPushforward.derivedPushforward f').map
            ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom.app
              (K, L)) :=
  adjunctionCupProduct_baseChange_square
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction f)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction f')
    (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCompIsoLeft f' g)
    (Stacks.Cohomology.DerivedBaseChangeOfToposHom.derivedPullbackCompIsoRight f g' f' g h)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f').hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom K L
    (Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso
      f g' f' g h _ _)

end ToposSquare

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
