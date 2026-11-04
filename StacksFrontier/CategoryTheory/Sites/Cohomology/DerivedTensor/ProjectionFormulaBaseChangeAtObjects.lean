module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaBaseChangeOfToposHom

/-!
# Invertibility of the projection formula map after `Lg^*`, from base change at two objects

For a 2-commutative square of ringed topoi `s : g ∘ f' ≅ f ∘ g'`,
`Stacks.Cohomology.ProjectionFormulaOfToposHom.isIso_derivedPullback_map_projectionFormulaMap`
deduces that `Lg^*` of the projection formula map along `f` at `(E, K)` is invertible from the
projection formula along `f'` and the invertibility of the base change map of the square at every
object. Its proof, through [Stacks, Tag 0E48], uses the base change map only at `E` and at
`E ⊗^L Lf^* K`. This file records that sharper form, which applies when base change is known
only on a subcategory, such as bounded below objects with torsion cohomology.

## Main results

All in the namespace `Stacks.Cohomology.ProjectionFormulaOfToposHom`:

* `isIso_derivedPullback_map_projectionFormulaMap_of_isIso`.
* `isIso_projectionFormulaMap_iff_of_iso`.

## References

* [Stacks Project, Tag 0E48](https://stacks.math.columbia.edu/tag/0E48)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.ProjectionFormulaOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

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

/-- A bifunctor, viewed on the product category, sends a product of isomorphisms to one. -/
private theorem isIso_map_prod {C C' D : Type*} [Category C] [Category C'] [Category D]
    (F : C × C' ⥤ D) {A B : C} {A' B' : C'} (a : A ⟶ B) (b : A' ⟶ B') [IsIso a] [IsIso b] :
    IsIso (F.map (a ×ₘ b)) :=
  have : IsIso (a ×ₘ b) := (isIso_prod_iff (C := _) (D := _)).2 ⟨inferInstance, inferInstance⟩
  Functor.map_isIso _ _

/-- **Invertibility of the projection formula map along `f` after `Lg^*`, from base change at
`E` and at `E ⊗^L Lf^* K`.** If the base change map of the square is invertible at `E` and at
`E ⊗^L Lf^* K`, then `Lg^*` of the projection formula map along `f` at `(E, K)` is invertible as
soon as the projection formula map along `f'` is invertible at `(L(g')^*E, Lg^*K)`. -/
theorem isIso_derivedPullback_map_projectionFormulaMap_of_isIso
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : IsIso (squareBaseChangeMap s E))
    (hEK : IsIso (squareBaseChangeMap s
      (((derivedTensorProductFunctor X.O).obj E).obj ((derivedPullback f).obj K))))
    (h : IsIso (projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K))) :
    IsIso ((derivedPullback g).map (projectionFormulaMap f E K)) := by
  have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (squareBaseChangeMap s E) (𝟙 ((derivedPullback g).obj K))
  have hL : IsIso ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
        ((derivedPushforward (X := X) (Y := Y) f).obj E, K) ≫
      (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
        (squareBaseChangeMap s E ×ₘ 𝟙 ((derivedPullback g).obj K)) ≫
      projectionFormulaMap f' ((derivedPullback g').obj E) ((derivedPullback g).obj K)) := by
    infer_instance
  rw [projectionFormulaMap_baseChange_square_of_twoIso s E K] at hL
  have : IsIso ((derivedPushforward (X := X') (Y := Y') f').map
        ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom.app
            (E, (derivedPullback f).obj K) ≫
          (Functor.uncurry.obj (derivedTensorProductFunctor X'.O)).map
            (𝟙 ((derivedPullback g').obj E) ×ₘ
              (RingedToposHom.TwoIso.derivedPullbackSquareIso s).inv.app K))) := by
    have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
      (𝟙 ((derivedPullback g').obj E))
      ((RingedToposHom.TwoIso.derivedPullbackSquareIso s).inv.app K)
    exact Functor.map_isIso _ _
  exact (isIso_comp_right_iff _ _).1 hL

/-- Invertibility of the projection formula map only depends on the isomorphism classes of its
two arguments: the map is natural in both. -/
theorem isIso_projectionFormulaMap_iff_of_iso
    {E E' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))}
    (eE : E ≅ E') (eK : K ≅ K') :
    IsIso (projectionFormulaMap f E K) ↔ IsIso (projectionFormulaMap f E' K') := by
  have h := CategoryTheory.adjunctionTensorMap_natural (derivedAdjunction f)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom eE.hom eK.hom
  have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    ((derivedPushforward (X := X) (Y := Y) f).map eE.hom) eK.hom
  have : IsIso ((derivedPushforward (X := X) (Y := Y) f).map
      ((Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
        (eE.hom ×ₘ (derivedPullback f).map eK.hom))) :=
    have := isIso_map_prod (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
      eE.hom ((derivedPullback f).map eK.hom)
    Functor.map_isIso _ _
  unfold projectionFormulaMap
  rw [← isIso_comp_right_iff _ ((derivedPushforward (X := X) (Y := Y) f).map
      ((Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
        (eE.hom ×ₘ (derivedPullback f).map eK.hom))), ← h]
  exact isIso_comp_left_iff _ _

end Stacks.Cohomology.ProjectionFormulaOfToposHom

end
