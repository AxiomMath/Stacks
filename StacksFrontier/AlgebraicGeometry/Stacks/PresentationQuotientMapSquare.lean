module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.SmoothQuotientStackModel
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaPresentationSquareAlgebraicStacks
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothQuotientStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverMapCorners

/-!
# Stacks 04ZN over a presentation, in the 2-category of algebraic stacks

Let `𝒳` be an algebraic stack over `S` with a presentation `[U/R] ≃ 𝒳` by a smooth groupoid
`(U, R, s, t, c)` in algebraic spaces (Stacks 04TI), and let `φ : (U', R', s', t', c') ⟶ (U, R,
s, t, c)` be a morphism of groupoids in algebraic spaces with `(U', R')` smooth. Then
`[U'/R']` is an algebraic stack (Stacks 04TK), represented in the 2-category
`AlgebraicGeometry.Stack.AlgebraicStacks` by its hom-shrunk model
`AlgebraicGeometry.Stack.smoothQuotientAlgebraicStack`, and `φ` induces a 1-morphism
`[U'/R'] ⟶ [U/R] ≃ 𝒳` of algebraic stacks (Stacks 046Q). Stacks 04ZN says that when the square
`R' ⟶ R` over `s' , s` and `U' ⟶ U` is cartesian, the square

```
𝒮_{U'} ------> [U'/R']
  |               |
  v               v
𝒮_U   ------>     𝒳
```

is a 2-fibre product. This file proves it in the 2-category of algebraic stacks over `S`.

## Main definitions

* `AlgebraicGeometry.Stack.presentationQuotientMap`: the 1-morphism `[U'/R'] ⟶ 𝒳` of algebraic
  stacks induced by `φ`.
* `AlgebraicGeometry.Stack.presentationQuotientMapSquare`: the square above.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_presentationQuotientMapSquare`: **Stacks 04ZN** in
  the 2-category of algebraic stacks over `S`, for the 1-morphism of a morphism of groupoids into
  a presenting groupoid.

## References

* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 04TK](https://stacks.math.columbia.edu/tag/04TK)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)
  {G' : GroupoidInAlgebraicSpaces B S hS (baseSpace B S hS)}
  (hG' : GroupoidInAlgebraicSpaces.IsSmooth B S hS G') (φ : Hom G' P.groupoid)

/-- **The 1-morphism `[U'/R'] ⟶ 𝒳` induced by a morphism of groupoids into a presenting
groupoid.** It is the 1-morphism `[U'/R'] ⟶ [U/R]` of Stacks 046Q followed by the presentation
`[U/R] ≃ 𝒳`, read out of the hom-shrunk model of `[U'/R']`. -/
noncomputable def presentationQuotientMap :
    smoothQuotientAlgebraicStack.{u, w} hG' ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').inv.functor ⋙
        (quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor
      w := by
        rw [Functor.assoc, Functor.assoc, P.basedFunctor.w, (quotientStackMap φ).w,
          (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').inv.w] })

/-- The underlying functor of `AlgebraicGeometry.Stack.presentationQuotientMap`. -/
theorem presentationQuotientMap_toFunctor :
    (presentationQuotientMap B S hS P hG' φ).hom.hom.toFunctor =
      (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').inv.functor ⋙
        (quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor :=
  rfl

/-- The 2-isomorphism filling `AlgebraicGeometry.Stack.presentationQuotientMapSquare`: the unit
of the hom-shrunk model, followed by the filler of the square of Stacks 04ZN, read through the
presentation. -/
noncomputable def presentationQuotientMapSquareIso :
    (quotientStackProjection G').toFunctor ⋙
        (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').hom.functor ⋙
          (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').inv.functor ⋙
            (quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor ≅
      (objectSpaceMap φ).toFunctor ⋙ (quotientStackProjection P.groupoid).toFunctor ⋙
        P.basedFunctor.toFunctor :=
  Functor.isoWhiskerLeft (quotientStackProjection G').toFunctor
      (Functor.isoWhiskerRight
        (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.symm
        ((quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor)) ≪≫
    (Functor.isoWhiskerRight (functorialityProjectionCellUnlifted φ) P.basedFunctor.toFunctor ≪≫
      Iso.refl _)

/-- The component of `AlgebraicGeometry.Stack.presentationQuotientMapSquareIso` at `x`: the image
of the inverse unit of the hom-shrunk model, followed by the image of the filler of the square of
Stacks 04ZN. -/
theorem presentationQuotientMapSquareIso_hom_app
    (x : (fibredCategory B S hS G'.objects.obj).val.obj) :
    (presentationQuotientMapSquareIso B S hS P hG' φ).hom.app x =
      P.basedFunctor.toFunctor.map ((quotientStackMap φ).toFunctor.map
          ((smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.inv.app
            ((quotientStackProjection G').toFunctor.obj x))) ≫
        P.basedFunctor.toFunctor.map ((functorialityProjectionCellUnlifted φ).hom.app x) := by
  simp [presentationQuotientMapSquareIso]

/-- Each component of `AlgebraicGeometry.Stack.presentationQuotientMapSquareIso` lies over an
identity morphism of the site. -/
theorem presentationQuotientMapSquareIso_isHomLift
    (x : (fibredCategory B S hS G'.objects.obj).val.obj) :
    𝒳.val.val.p.IsHomLift (𝟙 ((fibredCategory B S hS G'.objects.obj).val.p.obj x))
      ((presentationQuotientMapSquareIso B S hS P hG' φ).hom.app x) := by
  rw [presentationQuotientMapSquareIso_hom_app]
  have h₁ : (quotientStack G').p.IsHomLift
      (𝟙 ((fibredCategory B S hS G'.objects.obj).val.p.obj x))
      ((smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.inv.app
        ((quotientStackProjection G').toFunctor.obj x)) := by
    have h := (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').isHomLift_unitIso_inv_app
      ((quotientStackProjection G').toFunctor.obj x)
    rwa [BasedFunctor.w_obj (quotientStackProjection G') x] at h
  have h₃ : (quotientStack P.groupoid).p.IsHomLift
      (𝟙 ((fibredCategory B S hS G'.objects.obj).val.p.obj x))
      ((functorialityProjectionCellUnlifted φ).hom.app x) :=
    functorialityProjectionCellUnlifted_isHomLift φ x
  have h₄ : 𝒳.val.val.p.IsHomLift (𝟙 ((fibredCategory B S hS G'.objects.obj).val.p.obj x))
      (P.basedFunctor.toFunctor.map ((quotientStackMap φ).toFunctor.map
        ((smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.inv.app
          ((quotientStackProjection G').toFunctor.obj x)))) :=
    Functor.isHomLift_map_of_comp_eq
      (G := (quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor)
      (by rw [Functor.assoc, P.basedFunctor.w, (quotientStackMap φ).w]) _ _
  have h₅ : 𝒳.val.val.p.IsHomLift (𝟙 ((fibredCategory B S hS G'.objects.obj).val.p.obj x))
      (P.basedFunctor.toFunctor.map ((functorialityProjectionCellUnlifted φ).hom.app x)) :=
    Functor.isHomLift_map_of_comp_eq P.basedFunctor.w _ _
  infer_instance

/-- **The square of Stacks 04ZN over a presentation**, in the 2-category of algebraic stacks over
`S`:

```
𝒮_{U'} ------> [U'/R']
  |               |
  v               v
𝒮_U   ------>     𝒳
```

with the projection of Stacks 044R read on the hom-shrunk model on top, the 1-morphism of
Stacks 0458 induced by the map `U' ⟶ U` of object spaces on the left, the 1-morphism
`AlgebraicGeometry.Stack.presentationQuotientMap` on the right and the projection
`AlgebraicGeometry.Stack.presentationObjectMorphismAlgebraicStacks` of the presentation at the
bottom. -/
noncomputable def presentationQuotientMapSquare :
    Bicategory.TwoCommSq (presentationQuotientMap B S hS P hG' φ)
      (presentationObjectMorphismAlgebraicStacks B S hS P) where
  pt := algebraicSpaceStack.{u, w} B S hS G'.objects.obj G'.objects.property
  fst := quotientStackModelProjection.{u, w} B S hS (baseSpace B S hS) G'
    (smoothQuotientAlgebraicStack.{u, w} hG')
    (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG')
  snd := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom (objectSpaceMap φ))
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (presentationQuotientMapSquareIso B S hS P hG' φ)
      (presentationQuotientMapSquareIso_isHomLift B S hS P hG' φ)))

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ in
/-- A composite of three equivalences is an equivalence. -/
theorem isEquivalence_comp₃ {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
    {A₃ : Type u₃} [Category.{v₃} A₃] {A₄ : Type u₄} [Category.{v₄} A₄]
    (F : A₁ ⥤ A₂) (G : A₂ ⥤ A₃) (H : A₃ ⥤ A₄) (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    (hH : H.IsEquivalence) : (F ⋙ G ⋙ H).IsEquivalence := by
  have := hF
  have := hG
  have := hH
  infer_instance

/-- The universe lowering of the category of elements of the object space, as an equivalence over
the site. -/
noncomputable def liftedFibredCategoryDownEquivalenceOver (X : AlgebraicSpaces B S hS) :
    StacksRepresentableCFG.EquivalenceOver (liftedSpaceStack X).val.p
      (fibredCategory B S hS X.obj).val.p :=
  StacksRepresentableCFG.equivalenceOverOfIsEquivalence (liftedSpaceStack X).isFiberedInGroupoids
    (fibredCategory B S hS X.obj).isFiberedInGroupoids (liftedFibredCategoryDown X).toFunctor
    (liftedFibredCategoryDown X).w inferInstance

/-- The change of corners from the cospan of the square of Stacks 04ZN, read in the 2-category of
categories fibred in groupoids with morphisms in universe `u + 1`, to the cospan of
`AlgebraicGeometry.Stack.presentationQuotientMapSquare`: the hom-shrunk model on the first
corner, the universe lowering on the second, the presentation on the base. -/
noncomputable def presentationQuotientMapCorners :
    TwoFibreProductOver (quotientStack G').p (liftedSpaceStack P.groupoid.objects).val.p
        (quotientStack P.groupoid).p (quotientStackMap φ).toFunctor
        (liftedQuotientStackProjection P.groupoid).toFunctor ⥤
      TwoFibreProductOver (smoothQuotientAlgebraicStack.{u, w} hG').val.val.p
        (fibredCategory B S hS P.groupoid.objects.obj).val.p 𝒳.val.val.p
        (presentationQuotientMap B S hS P hG' φ).hom.hom.toFunctor
        (presentationObjectMorphismAlgebraicStacks B S hS P).hom.hom.toFunctor :=
  TwoFibreProductOver.mapCorners (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').hom.w
    (liftedFibredCategoryDownEquivalenceOver B S hS P.groupoid.objects).hom.w
    P.equivalence.hom.w
    (Functor.isoWhiskerRight (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso
      ((quotientStackMap φ).toFunctor ⋙ P.basedFunctor.toFunctor))
    (Iso.refl _)
    (fun x => by
      have h := (smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').isHomLift_unitIso_hom_app x
      have h' : (quotientStack P.groupoid).p.IsHomLift (𝟙 ((quotientStack G').p.obj x))
          ((quotientStackMap φ).toFunctor.map
            ((smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.hom.app x)) :=
        Functor.isHomLift_map_of_comp_eq (quotientStackMap φ).w _ _
      have h'' : 𝒳.val.val.p.IsHomLift (𝟙 ((quotientStack G').p.obj x))
          (P.basedFunctor.toFunctor.map ((quotientStackMap φ).toFunctor.map
            ((smoothQuotientAlgebraicStackEquivalenceOver.{u, w} hG').unitIso.hom.app x))) :=
        Functor.isHomLift_map_of_comp_eq P.basedFunctor.w _ _
      have hx :
          𝒳.val.val.p.obj (P.equivalence.hom.functor.obj ((quotientStackMap φ).toFunctor.obj x)) =
            (quotientStack G').p.obj x := by
        rw [← Functor.comp_obj, P.equivalence.hom.w, ← Functor.comp_obj, (quotientStackMap φ).w]
      rw [hx]
      exact h'')
    (fun y => by
      simp only [Iso.refl_hom, NatTrans.id_app]
      exact IsHomLift.id rfl)

/-- The change of corners `AlgebraicGeometry.Stack.presentationQuotientMapCorners` is an
equivalence. -/
theorem isEquivalence_presentationQuotientMapCorners :
    (presentationQuotientMapCorners B S hS P hG' φ).IsEquivalence :=
  TwoFibreProductOver.isEquivalence_mapCorners _ _ _
    (presentationQuotientMap B S hS P hG' φ).hom.hom.w
    (presentationObjectMorphismAlgebraicStacks B S hS P).hom.hom.w _ _ _ _

/-- **The comparison functor of `AlgebraicGeometry.Stack.presentationQuotientMapSquare` with the
canonical 2-fibre product of its cospan is an equivalence.** -/
theorem isEquivalence_lift_presentationQuotientMapSquare
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G'.source.hom P.groupoid.source.hom
      φ.toGroupoidHom.mapObjects) :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
        (presentationQuotientMap B S hS P hG' φ).hom
        (presentationObjectMorphismAlgebraicStacks B S hS P).hom
        (presentationQuotientMapSquare B S hS P hG' φ).underlying).hom.toFunctor := by
  have hK : Functor.IsEquivalence
      (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
        (functorialitySquareFibred φ)).hom.toFunctor :=
    Bicategory.isEquivalence_of_isTwoFibreProduct
      (isTwoFibreProduct_functorialitySquareFibred φ hφ)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
        (functorialitySquareFibred φ))
  have hM := isEquivalence_presentationQuotientMapCorners B S hS P hG' φ
  exact @isEquivalence_comp₃ _ _ _ _ _ TwoFibreProductOver.instCategory _
    TwoFibreProductOver.instCategory (liftedFibredCategoryUp G'.objects).toFunctor
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
      (functorialitySquareFibred φ)).hom.toFunctor (presentationQuotientMapCorners B S hS P hG' φ)
    (isEquivalence_liftedFibredCategoryUp _) hK hM

/-- **The square of a morphism into a presenting groupoid is a 2-fibre product.** Let `𝒳` be an
algebraic stack over `S` presented by a smooth groupoid `(U, R, s, t, c)` (Stacks 04TI), and let
`φ : (U', R', s', t', c') ⟶ (U, R, s, t, c)` be a morphism from a smooth groupoid in algebraic
spaces whose square of source maps

```
R' --φ--> R
|s'       |s
v         v
U' --φ--> U
```

is cartesian. Then the square
`AlgebraicGeometry.Stack.presentationQuotientMapSquare`

```
𝒮_{U'} ------> [U'/R']
  |               |
  v               v
𝒮_U   ------>     𝒳
```

is a 2-fibre product in the 2-category of algebraic stacks over `S` (Stacks 03YP). -/
@[stacks 04ZN "in the 2-category of algebraic stacks, for a morphism into a presenting groupoid"]
noncomputable def isTwoFibreProduct_presentationQuotientMapSquare
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G'.source.hom P.groupoid.source.hom
      φ.toGroupoidHom.mapObjects) :
    Bicategory.IsTwoFibreProduct (presentationQuotientMapSquare B S hS P hG' φ) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
        (presentationQuotientMapSquare B S hS P hG' φ).underlying)
      (isEquivalence_lift_presentationQuotientMapSquare B S hS P hG' φ hφ))

end AlgebraicGeometry.Stack

end
