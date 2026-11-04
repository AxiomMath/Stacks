module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatDescentAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfInclusion
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectMorphismFactor
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Descent of flatness of an object along a faithfully flat morphism

Let `𝒳` be an algebraic stack over `S` and let `f : x ⟶ y` be a morphism of objects of `𝒳`
lying over a morphism of schemes `U ⟶ V` which is flat and surjective. If `x` is a flat object
(the 1-morphism `x : U → 𝒳` is flat, **Stacks 0H14**), then so is `y`.

This is **Stacks 06Q0** at the composite `U → V → 𝒳`: the 1-morphism `x : U → 𝒳` is
2-isomorphic to that composite (**Stacks 004B**,
`AlgebraicGeometry.Stack.objectMorphismFactorIso`), and the first factor is flat and surjective
because `U ⟶ V` is. It is the descent step used twice in the proof of **Stacks 0DR2**, where
flatness of `Spec A ⟶ 𝒳` is deduced from flatness of `Spec A' ⟶ Spec A ⟶ 𝒳` for a faithfully
flat `A → A'`.

## Main results

* `AlgebraicGeometry.Stack.flatObject_of_flat_of_surjective`: the descent statement above.
* `AlgebraicGeometry.Stack.flatObject_iff_of_flat_of_surjective`: together with
  `AlgebraicGeometry.Stack.flatObject_of_flat`, flatness of `x` and of `y` are equivalent.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

/-- The 1-morphism of algebraic stacks induced by a morphism of the site is surjective when the
underlying morphism of schemes is. -/
theorem isSurjective_schemeFibredCategoryMap {V U : BigFppfOver B S hS} (j : V ⟶ U)
    (hj : Surjective ((BigFppfOver.toScheme B S hS).map j)) :
    IsSurjective B S hS
      (Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS j) :
        schemeStack.{u, w} B S hS V ⟶ schemeStack.{u, w} B S hS U) := by
  refine isSurjective_of_isSurjective_representingMap B S hS (yoneda.obj V) (yoneda.obj U)
    (isAlgebraicSpace_yoneda B S hS V) (isAlgebraicSpace_yoneda B S hS U)
    (PresheafOfCategories.sliceElementsEquivalenceOver V)
    (PresheafOfCategories.sliceElementsEquivalenceOver U) _ ?_
  rw [representingMap_schemeFibredCategoryMap]
  exact Space.isSurjective_yoneda_map B S hS j hj

/-- **Flatness of an object descends along a faithfully flat morphism.** If `f : x ⟶ y` lies over
a flat surjective morphism of schemes and `x` is a flat object of `𝒳`, then `y` is a flat object.
This is **Stacks 06Q0** at `x : U → 𝒳`, read as the composite `U → V → 𝒳` by **Stacks 004B**. -/
theorem flatObject_of_flat_of_surjective {x y : 𝒳.val.val.obj} (f : x ⟶ y)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map f).left))
    (hsurj : Surjective (B.inclusion.map (𝒳.val.val.p.map f).left))
    (hx : flatObject B S hS 𝒳.val x) :
    flatObject B S hS 𝒳.val y := by
  let b : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶
      schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y) :=
    Bicategory.InducedBicategory.mkHom (schemeFibredCategoryMap B S hS (𝒳.val.val.p.map f))
  let ly : schemeStack.{u, w} B S hS (𝒳.val.val.p.obj y) ⟶ 𝒳 :=
    Bicategory.InducedBicategory.mkHom
      (objectMorphism B S hS 𝒳.val (Functor.Fiber.mk (a := y) rfl))
  have hcomp : AlgebraicStacks.IsFlat B S hS (b ≫ ly) :=
    (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS (b ≫ ly)).2
      (hasPropertyOnSomeSmoothDiagram_of_twoIso B S hS _
        (objectMorphismFactorIso B S hS 𝒳.val f) hx)
  exact (AlgebraicStacks.isFlat_iff_hasPropertyOnSomeSmoothDiagram B S hS ly).1
    (AlgebraicStacks.isFlat_of_isSurjective_of_isFlat_comp B S hS b ly hcomp
      (isSurjective_schemeFibredCategoryMap.{u, w} B S hS (𝒳.val.val.p.map f) hsurj)
      (isFlat_schemeFibredCategoryMap.{u, w} B S hS (𝒳.val.val.p.map f) hflat))

/-- Along a morphism lying over a flat surjective morphism of schemes, flatness of the source
object and of the target object are equivalent. -/
theorem flatObject_iff_of_flat_of_surjective {x y : 𝒳.val.val.obj} (f : x ⟶ y)
    (hflat : Flat (B.inclusion.map (𝒳.val.val.p.map f).left))
    (hsurj : Surjective (B.inclusion.map (𝒳.val.val.p.map f).left)) :
    flatObject B S hS 𝒳.val x ↔ flatObject B S hS 𝒳.val y :=
  ⟨flatObject_of_flat_of_surjective B S hS 𝒳 f hflat hsurj,
    flatObject_of_flat B S hS 𝒳 f hflat⟩

end AlgebraicGeometry.Stack

end
