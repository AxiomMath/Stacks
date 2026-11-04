module

public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsGroupoidPresentation
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.EquivalenceOverMorSheafTarget
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductDescentIndependentBase
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorSheafIndependentBase

/-!
# The 2-fibre product of the Stacks 0DTG cospan

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site, let `φ : U ⟶ X` be an `R`-invariant morphism of algebraic spaces
over `B` and let `g : X' ⟶ X` be a morphism of algebraic spaces over `B`. The square of
Stacks 0DTG sits over the cospan

    [U/R] ---> 𝒮_X <--- 𝒮_{X'}

whose left leg is the structure arrow of Stacks 044R for the groupoid read over its invariant
target and whose right leg is the 1-morphism of Stacks 0458 attached to `g`. This file builds the
2-fibre product of Stacks 0040 over that cospan and records what is known about it as a category
over the big fppf site: it is fibred in groupoids (Stacks 0041), it is a fibred category
(Stacks 02XQ), its morphism presheaves are sheaves (condition (2) of Stacks 026F) and it is a
stack (Stacks 026G, Stacks 02ZI).

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeTwoFibreProductObj` and
  `AlgebraicGeometry.Stack.baseChangeTwoFibreProduct`: the 2-fibre product
  `[U/R] ×_{𝒮_X} 𝒮_{X'}` and its structure functor.

## Main results

* `AlgebraicGeometry.Stack.isFiberedInSets_liftedFibredCategory` and
  `AlgebraicGeometry.Stack.obj_eq_of_isHomLift_lifted`: the enlarged fibred category of an
  algebraic space is fibred in sets, so the domain of a morphism into it is determined by the
  codomain and the morphism of the site the morphism lies over.
* `AlgebraicGeometry.Stack.isFibredOneMorphism_liftedQuotientStackToBase` and
  `AlgebraicGeometry.Stack.isFibredOneMorphism_liftedAssociatedMap`: the two legs of the cospan
  are 1-morphisms of fibred categories over the site.
* `AlgebraicGeometry.Stack.isFiberedInGroupoids_baseChangeTwoFibreProduct`,
  `AlgebraicGeometry.Stack.isFibered_baseChangeTwoFibreProduct`,
  `AlgebraicGeometry.Stack.isMorSheaf_baseChangeTwoFibreProduct`,
  `AlgebraicGeometry.Stack.isStack_baseChangeTwoFibreProduct` and
  `AlgebraicGeometry.Stack.isStackInGroupoids_baseChangeTwoFibreProduct`: Stacks 0041,
  Stacks 02XQ, condition (2) of Stacks 026F, Stacks 026G and Stacks 02ZI for it.

## Implementation notes

The object-space corners are the **enlarged** fibred categories
`AlgebraicGeometry.Stack.liftedFibredCategory`, whose morphisms live one universe above the
site's, as the quotient stack's do; the enlargement is what lets the three categories of the
cospan share a hom universe, which is what condition (2) of Stacks 026F needs. Both the
universe-independent form of Stacks 026F and that of Stacks 026G apply, the hom universe of the
site being `u` and that of the three categories `u + 1`.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0041](https://stacks.math.columbia.edu/tag/0041)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 026G](https://stacks.math.columbia.edu/tag/026G)
* [Stacks Project, Tag 02XQ](https://stacks.math.columbia.edu/tag/02XQ)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 0458](https://stacks.math.columbia.edu/tag/0458)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The two legs of the cospan -/

/-- **The universe-enlarged fibred category of an algebraic space is fibred in sets.** Its fibres
are the sets of sections of the underlying sheaf, as they are before the enlargement. -/
theorem isFiberedInSets_liftedFibredCategory (X : AlgebraicSpaces C S hS) :
    (liftedFibredCategory X).p.IsFiberedInSets := by
  have : (fibredCategory C S hS X.obj).val.p.IsFiberedInSets :=
    inferInstanceAs (PresheafOfCategories.discreteProjection X.obj).IsFiberedInSets
  exact isFiberedInSets_uliftHom _

/-- **In the enlarged fibred category of an algebraic space the domain of a morphism is
determined by its codomain and by the morphism of the site it lies over.** This is the half of
`CategoryTheory.Functor.IsFiberedInSets.eq_of_isHomLift` that
`AlgebraicGeometry.Stack.hom_eq_of_isHomLift_lifted` does not record. -/
theorem obj_eq_of_isHomLift_lifted {X : AlgebraicSpaces C S hS}
    {V U : BigFppfOver C S hS} (f : V ⟶ U) {x y₁ y₂ : (liftedFibredCategory X).obj}
    (φ₁ : y₁ ⟶ x) (φ₂ : y₂ ⟶ x) (h₁ : (liftedFibredCategory X).p.IsHomLift f φ₁)
    (h₂ : (liftedFibredCategory X).p.IsHomLift f φ₂) : y₁ = y₂ := by
  have := isFiberedInSets_liftedFibredCategory X
  have := h₁
  have := h₂
  exact (Functor.IsFiberedInSets.eq_of_isHomLift (liftedFibredCategory X).p f φ₁ φ₂).choose


/-- **The structure arrow of Stacks 044R is a 1-morphism of fibred categories.** It is strictly
over the site, and preservation of strongly cartesian morphisms is free because the enlarged
fibred category of an algebraic space is fibred in groupoids. -/
theorem isFibredOneMorphism_liftedQuotientStackToBase
    (H : GroupoidInAlgebraicSpaces C S hS B) :
    Functor.IsFibredOneMorphism (quotientStack H).p (liftedFibredCategory B).p
      (liftedQuotientStackToBase H).toFunctor :=
  (isFiberedInGroupoids_liftedFibredCategory B).isFibredOneMorphism
    (liftedQuotientStackToBase H).w

/-- **The enlarged 1-morphism of Stacks 0458 is a 1-morphism of fibred categories.** -/
theorem isFibredOneMorphism_liftedAssociatedMap {X Y : AlgebraicSpaces C S hS} (a : X ⟶ Y) :
    Functor.IsFibredOneMorphism (liftedFibredCategory X).p (liftedFibredCategory Y).p
      (liftedAssociatedMap a).toFunctor :=
  (isFiberedInGroupoids_liftedFibredCategory Y).isFibredOneMorphism (liftedAssociatedMap a).w

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (g : X' ⟶ X)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-! ### The 2-fibre product -/

/-- **The 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`** of Stacks 0040, as a category over the big
fppf site: the 2-fibre product of the structure arrow of Stacks 044R for the groupoid read over
its invariant target and the enlarged 1-morphism of Stacks 0458 attached to `g`. -/
noncomputable abbrev baseChangeTwoFibreProductObj : Type (u + 1) :=
  TwoFibreProductOver (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p
    (liftedFibredCategory X').p (liftedFibredCategory X).p
    (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)).toFunctor
    (liftedAssociatedMap g).toFunctor

/-- The structure functor of the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`. -/
noncomputable abbrev baseChangeTwoFibreProduct :
    baseChangeTwoFibreProductObj G XtoB g φ hφB hφ ⥤ BigFppfOver C S hS :=
  TwoFibreProductOver.structureFunctor _ _ _ _ _

/-- **Stacks 0041** for the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`: it is fibred in groupoids,
because the quotient stack and the two enlarged object-space stacks are and the two legs are
strictly over the site. -/
theorem isFiberedInGroupoids_baseChangeTwoFibreProduct :
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids _ _ _ _ _
    (isFiberedInGroupoids_quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ))
    (isFiberedInGroupoids_liftedFibredCategory X')
    (isFiberedInGroupoids_liftedFibredCategory X)
    (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)).w
    (liftedAssociatedMap g).w

/-- The 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` is a stack over the big fppf site; the public
statements about it are consequences of this. -/
private theorem isStack_baseChangeTwoFibreProduct_aux :
    Functor.IsStack (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (BigFppfOver.topology C S hS) :=
  TwoFibreProductOver.isStack_structureFunctor _ _ _ _ _
    (BigFppfOver.topology C S hS)
    (isStack_quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ))
    (liftedFibredCategory_isStack X') (liftedFibredCategory_isStack X)
    (isFibredOneMorphism_liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ))
    (isFibredOneMorphism_liftedAssociatedMap g)

/-- **Stacks 02XQ** for the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`: it is a fibred category over
the big fppf site. -/
theorem isFibered_baseChangeTwoFibreProduct :
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).IsFibered :=
  (isStack_baseChangeTwoFibreProduct_aux G XtoB g φ hφB hφ).isFibered

/-- **Condition (2) of Stacks 026F for the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`**: its morphism
presheaves are sheaves on the big fppf site. -/
theorem isMorSheaf_baseChangeTwoFibreProduct (T : BigFppfOver C S hS)
    (x y : have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
      (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).Fiber T) :
    have := isFibered_baseChangeTwoFibreProduct G XtoB g φ hφB hφ
    Functor.IsMorSheaf (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (BigFppfOver.topology C S hS) T x y :=
  (isStack_baseChangeTwoFibreProduct_aux G XtoB g φ hφB hφ).isMorSheaf T x y

/-- **Stacks 026G for the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`**: it is a stack over the big
fppf site. -/
theorem isStack_baseChangeTwoFibreProduct :
    Functor.IsStack (baseChangeTwoFibreProduct G XtoB g φ hφB hφ)
      (BigFppfOver.topology C S hS) :=
  isStack_baseChangeTwoFibreProduct_aux G XtoB g φ hφB hφ

/-- **Stacks 02ZI for the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}`**: it is a stack in groupoids
over the big fppf site. -/
theorem isStackInGroupoids_baseChangeTwoFibreProduct :
    (baseChangeTwoFibreProduct G XtoB g φ hφB hφ).IsStackInGroupoids
      (BigFppfOver.topology C S hS) :=
  (isStack_baseChangeTwoFibreProduct G XtoB g φ hφB hφ).isStackInGroupoids
    (isFiberedInGroupoids_baseChangeTwoFibreProduct G XtoB g φ hφB hφ)

end BaseChange

end AlgebraicGeometry.Stack

end
