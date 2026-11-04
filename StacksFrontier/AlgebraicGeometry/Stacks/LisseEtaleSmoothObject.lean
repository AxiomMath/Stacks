module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothSourceLocalityTransfer
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.TwoYoneda.RepresentedPoint

/-!
# The smooth objects of the stack of a scheme are the smooth morphisms to it

Let `U` be a scheme over `S` in a big fppf site and let `𝒳 = schemeStack U` be the algebraic
stack it represents, so that an object of `𝒳` is a scheme over `U` in the site. Stacks 0787 calls
such an object *smooth* when the 1-morphism of algebraic stacks it names under the 2-Yoneda lemma
is smooth, and the lisse-étale site of `𝒳` is the full subcategory of the smooth objects. This
file identifies that condition with the elementary one: the object `x : V ⟶ U` is smooth exactly
when the morphism of schemes underneath `x.hom` is smooth.

## Main results

* `AlgebraicGeometry.Stack.representingMap_eq_yoneda_map_baseMap`: the morphism of representing
  presheaves induced by a based functor between slices is the Yoneda image of the morphism of the
  site underlying it.
* `AlgebraicGeometry.Stack.baseMapOfBasedFunctor_liftBased`: for the 2-Yoneda based functor of an
  object of a slice, that morphism is the object's structure morphism.
* `AlgebraicGeometry.Stack.smoothObject_schemeStack_iff`: **Stacks 0787** — an object of the
  stack of a scheme is a smooth object exactly when its structure morphism of schemes is smooth.

## Implementation notes

Both source and target are represented by representable presheaves, with the representing
equivalences `CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`. **Stacks 06FM**
for representable source and target,
`AlgebraicGeometry.Stack.hasPropertyOnSomeSmoothDiagram_iff_represented`, reduces smoothness of
the 1-morphism to smoothness of the induced morphism of presheaves, which
`AlgebraicGeometry.Stack.representingMap_eq_yoneda_map_baseMap` and
`AlgebraicGeometry.Stack.baseMapOfBasedFunctor_liftBased` identify with `yoneda.map x.hom`. Its
smoothness as a morphism of algebraic spaces is smoothness of the underlying morphism of schemes,
`AlgebraicGeometry.Space.isSmooth_yoneda_map_iff`.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 075U](https://stacks.math.columbia.edu/tag/075U)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The morphism of the big fppf category of `S` underlying a based functor between two slices:
the structure morphism of the image of the terminal object, transported along the equality of
underlying objects that being a based functor supplies. -/
def baseMapOfBasedFunctor {W U : BigFppfOver B S hS}
    (b : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor (Over.forget U)) :
    W ⟶ U :=
  eqToHom (Functor.congr_obj b.w (Over.mk (𝟙 W))).symm ≫ (b.obj (Over.mk (𝟙 W))).hom

/-- `AlgebraicGeometry.Stack.baseMapOfBasedFunctor` is the morphism `W ⟶ U` that the identity
equivalence of `CategoryTheory.Over.forget U` with itself reads off the 2-Yoneda evaluation of
the based functor. -/
theorem baseMapOfBasedFunctor_eq_sliceHomOfFiber {W U : BigFppfOver B S hS}
    (b : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor (Over.forget U)) :
    baseMapOfBasedFunctor B S hS b =
      StacksRepresentableCFG.sliceHomOfFiber
        (StacksRepresentableCFG.EquivalenceOver.refl (Over.forget U))
        ((Functor.twoYonedaEvaluation (Over.forget U) W).obj b) := rfl

/-- **The morphism of representing presheaves induced by a based functor between slices is the
Yoneda image of the morphism of the site underlying it.** -/
theorem representingMap_eq_yoneda_map_baseMap {W U : BigFppfOver B S hS}
    (b : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor (Over.forget U)) :
    representingMap B S hS
      (schemeFibredCategory B S hS W) (schemeFibredCategory B S hS U)
      (yoneda.obj W) (yoneda.obj U)
      (PresheafOfCategories.sliceElementsEquivalenceOver W)
      (PresheafOfCategories.sliceElementsEquivalenceOver U)
      (Bicategory.InducedBicategory.mkHom b) = yoneda.map (baseMapOfBasedFunctor B S hS b) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_yoneda_map]
  have h := morphismSpaceEquiv_map B S hS
    (schemeFibredCategory B S hS W) (schemeFibredCategory B S hS U)
    (yoneda.obj W) (yoneda.obj U)
    (PresheafOfCategories.sliceElementsEquivalenceOver W)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    ⟨CatFiberedInGroupoids.homFunctor (Bicategory.InducedBicategory.mkHom b),
      CatFiberedInGroupoids.homFunctor_comp_p _⟩ W (𝟙 W)
  have : ∀ V, (schemeFibredCategory B S hS V).val.p.IsFibered :=
    fun V => (schemeFibredCategory B S hS V).2.isFibered
  have he := congrArg (StacksRepresentableCFG.sliceHomOfIsoClass
    (StacksRepresentableCFG.EquivalenceOver.refl (Over.forget U))) h
  have hbridge : ∀ a : (schemeFibredCategory B S hS U).val.p.Fiber W,
      StacksRepresentableCFG.sliceHomOfIsoClass
          (StacksRepresentableCFG.EquivalenceOver.refl (Over.forget U))
          (Functor.isoClassMk (schemeFibredCategory B S hS U).val.p a)
        = StacksRepresentableCFG.sliceHomOfFiber
          (StacksRepresentableCFG.EquivalenceOver.refl (Over.forget U)) a :=
    fun _ => rfl
  rw [Functor.isoClassMap_app_isoClassMk, hbridge, hbridge] at he
  exact he.symm

/-- **The morphism of the site underlying the 2-Yoneda based functor of an object of a slice is
that object's structure morphism.** -/
theorem baseMapOfBasedFunctor_liftBased (U : BigFppfOver B S hS) (x : Over U) :
    baseMapOfBasedFunctor B S hS
      (Functor.TwoYoneda.liftBased (Over.forget U)
        (Functor.IsFiberedInGroupoids.over_forget U) x.left
        (Functor.Fiber.mk (a := x) rfl)) = x.hom := by
  rw [baseMapOfBasedFunctor_eq_sliceHomOfFiber,
    StacksRepresentableCFG.sliceHomOfFiber_eq_of_iso
      (StacksRepresentableCFG.EquivalenceOver.refl (Over.forget U))
      (Functor.TwoYoneda.liftBasedEvaluationIso (Over.forget U)
        (Functor.IsFiberedInGroupoids.over_forget U) x.left
        (Functor.Fiber.mk (a := x) rfl))]
  show eqToHom (rfl : x.left = x.left) ≫ x.hom = x.hom
  simp

/-- **Stacks 0787.** An object of the algebraic stack of a scheme `U` over `S` — that is, a scheme
`x` over `U` in the big fppf category — is a *smooth object* exactly when the morphism of schemes
underlying its structure morphism is smooth. -/
@[stacks 0787 "lisse_etale_site: smooth objects of the stack of a scheme"]
theorem smoothObject_schemeStack_iff (U : BigFppfOver B S hS) (x : Over U) :
    smoothObject.{u, w} B S hS (schemeStack.{u, w} B S hS U) x ↔
      Smooth ((BigFppfOver.toScheme B S hS).map x.hom) := by
  have heq := representingMap_eq_yoneda_map_baseMap B S hS
    (Functor.TwoYoneda.liftBased (Over.forget U)
      (Functor.IsFiberedInGroupoids.over_forget U) x.left (Functor.Fiber.mk (a := x) rfl))
  rw [baseMapOfBasedFunctor_liftBased] at heq
  have key := hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS
    (fun _ _ h => Space.IsSmooth B S hS h)
    (Space.isSmoothLocalOnSourceAndTarget_smooth B S hS)
    (schemeStack.{u, w} B S hS x.left).property
    (schemeStack.{u, w} B S hS U).property
    (yoneda.obj x.left) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS x.left) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver x.left)
    (PresheafOfCategories.sliceElementsEquivalenceOver U)
    (objectMorphism B S hS (schemeFibredCategory B S hS U)
      (Functor.Fiber.mk (a := x) rfl))
  exact key.trans ((Iff.of_eq (congrArg (fun f => Space.IsSmooth B S hS f) heq)).trans
    (Space.isSmooth_yoneda_map_iff B S hS x.hom))

end AlgebraicGeometry.Stack

end
