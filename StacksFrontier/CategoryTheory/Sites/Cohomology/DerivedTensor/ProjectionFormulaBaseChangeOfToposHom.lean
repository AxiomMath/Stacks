module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorSquareCompatible

/-!
# The projection formula map and base change, for a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`,
and let `Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` be the isomorphism of the two derived pullbacks
around it. The base change map `b : Lg^* Rf_* ⟶ Rf'_* L(g')^*` of the square is the mate of `Σ`
under the two derived adjunctions `Lf^* ⊣ Rf_*` and `L(f')^* ⊣ Rf'_*` of [Stacks, Tag 07A6].

[Stacks, Tag 0E48] says that Equation 21.50.0.1 is compatible with `b`: for `E ∈ D(𝒪_𝒞)` and
`K ∈ D(𝒪_𝒟)` the two routes from `Lg^*(Rf_*E ⊗^𝐋 K)` to `Rf'_*(L(g')^*E ⊗^𝐋 L(f')^*Lg^*K)`
agree. Over abstract adjunctions this is
`Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, whose one input is the
compatibility of the four comparisons of [Stacks, Tag 07A4] around the square; for a square of
ringed topoi that input is `AlgebraicGeometry.RingedToposHom.TwoIso.tensorComparisonCompatible`.
So the remark holds here with no hypothesis.

As a consequence, if the base change map is invertible then the projection formula map along `f`
is invertible after `Lg^*` as soon as the projection formula map along `f'` is invertible at the
pulled back objects. This is how invertibility of Equation 21.50.0.1 is checked locally on the
target.

## Main definitions

* `Stacks.Cohomology.ProjectionFormulaOfToposHom.squareBaseChangeMap`: the base change map of the
  square, `Lg^* Rf_* E ⟶ Rf'_* L(g')^* E`.

## Main results

* `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square_of_twoIso`:
  **[Stacks, Tag 0E48]** for a 2-commutative square of ringed topoi. For a strictly commutative
  square this is
  `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square`.
* `Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_derivedPullback_map_projectionFormulaMap`:
  invertibility of the projection formula map along `f'` gives its invertibility along `f` after
  `Lg^*`, when the base change map is invertible.

## References

* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

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
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))

/-- **The base change map of a 2-commutative square of ringed topoi**,
`Lg^* Rf_* E ⟶ Rf'_* L(g')^* E`: the mate, under the derived adjunctions `Lf^* ⊣ Rf_*` and
`L(f')^* ⊣ Rf'_*`, of the isomorphism `Σ : L(f')^* ∘ Lg^* ≅ L(g')^* ∘ Lf^*` of the two derived
pullbacks around the square. -/
def squareBaseChangeMap
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullback g).obj ((derivedPushforward (X := X) (Y := Y) f).obj E) ⟶
      (derivedPushforward (X := X') (Y := Y') f').obj ((derivedPullback g').obj E) :=
  Stacks.CategoryTheory.BaseChange.map (derivedAdjunction f) (derivedAdjunction f')
    (RingedToposHom.TwoIso.derivedPullbackSquareIso s) (Iso.refl _) E

/-- **[Stacks, Tag 0E48] for a 2-commutative square of ringed topoi.** For `E ∈ D(𝒪_𝒞)` and
`K ∈ D(𝒪_𝒟)`, the comparison of [Stacks, Tag 07A4] along `g`, followed by the base change map in
the first factor and by Equation 21.50.0.1 along `f'`, is `Lg^*` of Equation 21.50.0.1 along `f`,
followed by the base change map and by `Rf'_*` of the comparison along `g'` and of `Σ⁻¹` in the
second factor. -/
theorem projectionFormulaMap_baseChange_square_of_twoIso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
        ((derivedPushforward (X := X) (Y := Y) f).obj E, K) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
        (squareBaseChangeMap s E ×ₘ 𝟙 ((derivedPullback g).obj K)) ≫
      projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K) =
    (derivedPullback g).map (projectionFormulaMap f E K) ≫
      squareBaseChangeMap s
        (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K)) ≫
      (derivedPushforward (X := X') (Y := Y') f').map
        ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom.app
            (E, (derivedPullback f).obj K) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
            (𝟙 ((derivedPullback g').obj E) ×ₘ
              (RingedToposHom.TwoIso.derivedPullbackSquareIso s).inv.app K)) := by
  have h := Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square
    (derivedAdjunction f) (derivedAdjunction f')
    (RingedToposHom.TwoIso.derivedPullbackSquareIso s) (Iso.refl _)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f').hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom E K
    (RingedToposHom.TwoIso.tensorComparisonCompatible s _ _)
  exact h.trans (by
    simp only [Stacks.AffineProjectionFormula.squareCompositeIso_inv_app, Iso.refl_hom,
      NatTrans.id_app, Category.id_comp]
    rfl)

/-- A functor on `C × C` sends a product of two isomorphisms to an isomorphism. -/
private theorem isIso_map_prod {C D : Type*} [Category C] [Category D] (F : C × C ⥤ D)
    {A B A' B' : C} (a : A ⟶ A') (b : B ⟶ B') [IsIso a] [IsIso b] : IsIso (F.map (a ×ₘ b)) := by
  have : IsIso (a ×ₘ b) := (isIso_prod_iff (C := _) (D := _)).2 ⟨inferInstance, inferInstance⟩
  exact Functor.map_isIso _ _

/-- **Invertibility of the projection formula map along `f` after `Lg^*`, from invertibility
along `f'`.** If the base change map of the square is invertible, then `Lg^*` of Equation
21.50.0.1 along `f` at `(E, K)` is invertible as soon as Equation 21.50.0.1 along `f'` is
invertible at `(L(g')^*E, Lg^*K)`: by [Stacks, Tag 0E48] the two are identified up to
invertible maps. -/
theorem isIso_derivedPullback_map_projectionFormulaMap
    (hb : ∀ E, IsIso (squareBaseChangeMap s E))
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (h : IsIso (projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback g).map (projectionFormulaMap f E K)) := by
  have heq := projectionFormulaMap_baseChange_square_of_twoIso s E K
  have := hb E
  have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (squareBaseChangeMap s E) (𝟙 ((derivedPullback g).obj K))
  have hL : IsIso ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
        ((derivedPushforward (X := X) (Y := Y) f).obj E, K) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
        (squareBaseChangeMap s E ×ₘ 𝟙 ((derivedPullback g).obj K)) ≫
      projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K)) := by
    infer_instance
  rw [heq] at hL
  have := hb (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K))
  have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
    (𝟙 ((derivedPullback g').obj E))
    ((RingedToposHom.TwoIso.derivedPullbackSquareIso s).inv.app K)
  have : IsIso ((derivedPushforward (X := X') (Y := Y') f').map
        ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom.app
            (E, (derivedPullback f).obj K) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
            (𝟙 ((derivedPullback g').obj E) ×ₘ
              (RingedToposHom.TwoIso.derivedPullbackSquareIso s).inv.app K))) :=
    Functor.map_isIso _ _
  exact (isIso_comp_right_iff _ _).1 hL

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
