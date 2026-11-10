module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmallModel
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp

/-!
# The stack of curves with small hom-sets

The category `AlgebraicGeometry.CurveFamily` of families of curves (Stacks 0D4Z) has morphism
universe `u + 1`, because a morphism of total spaces is a morphism of presheaves on the big fppf
site. Its hom-sets are nevertheless `u`-small: a morphism of algebraic spaces is determined by its
composite with a surjective étale atlas `yoneda U ⟶ X`, which is a section of the target over
`U` (Stacks 03HM-style descent along an atlas), so it lies in a set of the universe of the site.

The 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of this library is pinned to categories
fibred in groupoids with morphism universe `u`, so to regard `Curves` as one of its objects it is
replaced by the equivalent category `ShrinkHoms (CurveFamily B hZ)`, with the same objects and
`u`-small hom-sets, over the big fppf site through the same projection. This file constructs that
model and the equivalence over the site, and transports algebraicity to it (Stacks 03YQ).

## Main definitions

* `AlgebraicGeometry.curvesSmallFiberedCategory`: `Curves` with small hom-sets, as a category
  fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.curvesShrinkHomsEquivalenceOver`: its equivalence over the site with
  `AlgebraicGeometry.curvesFiberedCategory`.
* `AlgebraicGeometry.curvesShrinkHomsAlgebraicStack`: given the algebraicity of the stack of curves
  (Stacks 0D5A, in the form
  `Stack.IsAlgebraicStack B integerBase hZ (curvesFiberedCategory B hZ).val`), the stack of curves
  as an object of `AlgebraicGeometry.Stack.AlgebraicStacks`.

## References

* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Morphisms between two algebraic spaces over `S` form a `u`-small type: a morphism is
determined by its composite with a surjective étale atlas of the source, and those composites are
sections of the target over a scheme of the site. -/
theorem small_hom_algebraicSpaces (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X Y : AlgebraicSpaces B S hS) : Small.{u} (X ⟶ Y) := by
  obtain ⟨U, b, hsurj, het⟩ := X.property.exists_atlas
  exact small_of_injective (f := fun φ : X ⟶ Y => yonedaEquiv (b ≫ φ.hom)) fun _ _ h =>
    ObjectProperty.hom_ext _ <| Space.hom_ext_of_etale_atlas B S hS X.property.isSheaf
      Y.property.isSheaf b hsurj het (yonedaEquiv.injective h)

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

attribute [instance] locallySmall_curveFamily

/-- The projection of the small-hom model of the stack of curves to the big fppf site: a family
goes to its base. -/
abbrev curvesSmallProjection : ShrinkHoms (CurveFamily B hZ) ⥤ BigFppfOver B integerBase hZ :=
  ShrinkHoms.inverse (CurveFamily B hZ) ⋙ curvesProjectionOver B hZ

/-- Passing to the small-hom model commutes with the projections to the site. -/
theorem shrinkHomsFunctor_comp_curvesSmallProjection :
    ShrinkHoms.functor (CurveFamily B hZ) ⋙ curvesSmallProjection B hZ =
      curvesProjectionOver B hZ :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => by
    change (curvesProjectionOver B hZ).map ((equivShrink (X ⟶ Y)).symm (equivShrink (X ⟶ Y) f)) =
      _
    rw [Equiv.symm_apply_apply]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm)

/-- The equivalence over the big fppf site between the stack of curves and its small-hom model. -/
def curvesShrinkHomsEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (curvesProjectionOver B hZ)
      (curvesSmallProjection B hZ) where
  hom := ⟨ShrinkHoms.functor _, shrinkHomsFunctor_comp_curvesSmallProjection B hZ⟩
  inv := ⟨ShrinkHoms.inverse _, rfl⟩
  unitIso := (ShrinkHoms.equivalence (CurveFamily B hZ)).unitIso
  counitIso := (ShrinkHoms.equivalence (CurveFamily B hZ)).counitIso
  unit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl
  counit_over := StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ fun _ => IsHomLift.id rfl

/-- The small-hom model of the stack of curves is fibred in groupoids. -/
theorem curvesSmallProjection_isFiberedInGroupoids :
    (curvesSmallProjection B hZ).IsFiberedInGroupoids :=
  StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
    (curvesShrinkHomsEquivalenceOver B hZ).symm (curvesFiberedCategory B hZ).property

/-- The stack of curves with small hom-sets, as a category fibred in groupoids over the big fppf
site. -/
abbrev curvesSmallFiberedCategory :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B integerBase hZ) :=
  CatFiberedInGroupoids.mk (BasedCategory.ofFunctor (curvesSmallProjection B hZ))
    (curvesSmallProjection_isFiberedInGroupoids B hZ)

/-- **Algebraicity transfers to the small-hom model** (Stacks 03YQ, the two categories in
independent universes). -/
theorem isAlgebraicStack_curvesSmall
    (hCurvesAlgebraic : Stack.IsAlgebraicStack.{u, u + 1, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ).val) :
    Stack.IsAlgebraicStack.{u, u + 1} B integerBase hZ (curvesSmallFiberedCategory B hZ).val :=
  Stack.isAlgebraicStack_of_equivalenceOver B integerBase hZ (curvesShrinkHomsEquivalenceOver B hZ)
    hCurvesAlgebraic

/-- The stack of curves as an object of the 2-category of algebraic stacks of this library, given
its algebraicity (Stacks 0D5A): its small-hom model, equivalent over the site to
`AlgebraicGeometry.curvesFiberedCategory`. -/
abbrev curvesShrinkHomsAlgebraicStack
    (hCurvesAlgebraic : Stack.IsAlgebraicStack.{u, u + 1, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ).val) :
    Stack.AlgebraicStacks.{u, u + 1} B integerBase hZ :=
  ⟨curvesSmallFiberedCategory B hZ, isAlgebraicStack_curvesSmall B hZ hCurvesAlgebraic⟩

end AlgebraicGeometry

end
