module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules

/-!
# Restriction of modules along `Over.map` preserves K-injective complexes

Let `(C, J)` be a site, `O` a sheaf of rings on it and `f : V ⟶ U` an arrow of `C`. Restriction of
sheaves of `O|_U`-modules along `Over.map f`, that is Mathlib's `SheafOfModules.overMap`, carries
K-injective complexes to K-injective complexes.

This is Stacks 08FI for the slice-to-slice restriction. The library's form of that tag,
`Stacks.Cohomology.Localization.isKInjective_over`, is the case of the restriction
`SheafOfModules.overFunctor` from the site itself to a slice; the statement below is obtained from
it by the observation that `Over.map f` factors through the *iterated* slice: the slice of `C/U` at
the object `Over.mk f` is the slice `C/V`, and under that equivalence `Over.map f` is the
forgetful functor of a slice. So restriction along `Over.map f` is restriction to the iterated
slice, which is an instance of that tag, followed by a transport along an equivalence of
sites, which preserves K-injectivity because it is one half of an adjoint equivalence and therefore
has an exact left adjoint.

The factorization itself is `Stacks.SheafOfModules.overFunctor_comp_sliceBackward`, an
equality of functors, with `Stacks.SheafOfModules.sliceBackwardComplexIso` its form on cochain
complexes.

## Main results

* `Stacks.Cohomology.Localization.isKInjective_sliceBackward`: transport of sheaves of modules
  from an iterated slice preserves K-injective complexes.
* `Stacks.Cohomology.Localization.isKInjective_overMap`: **Stacks 08FI** for `Over.map`.

## Implementation notes

The equivalence of categories of sheaves of modules is Mathlib's
`SheafOfModules.pushforwardPushforwardEquivalence` at `CategoryTheory.Over.iteratedSliceEquiv`,
with both comparison morphisms of sheaves of rings the identity; its inverse is
`Stacks.SheafOfModules.sliceBackward` on the nose. Its two coherence hypotheses hold because the
structure sheaves of the two sites are the same presheaf of rings read on equivalent sites, so each
side reduces to the functoriality of `O` at an identity.

The universes are collapsed — the objects and the morphisms of `C` in one universe, which is also
the one of the ring and of the module sections — because the library's Stacks 08FI is stated that way.

## References

* [Stacks Project, Tag 08FI](https://stacks.math.columbia.edu/tag/08FI)
* [Stacks Project, Tag 08BJ](https://stacks.math.columbia.edu/tag/08BJ), the adjoint criterion
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Cohomology.Localization

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (O : Sheaf J RingCat.{u})
  {V U : C} (f : V ⟶ U)

/-- Continuity of the functor of `CategoryTheory.Over.iteratedSliceEquiv`, in the spelling instance
search needs: Mathlib states it for `CategoryTheory.Over.iteratedSliceForward` and with the base of
the target slice written as `(Over.mk f).left` rather than as `V`. -/
local instance isContinuous_iteratedSliceEquiv_functor :
    (Over.mk f).iteratedSliceEquiv.functor.IsContinuous ((J.over U).over (Over.mk f))
      (J.over V) :=
  inferInstanceAs ((Over.mk f).iteratedSliceForward.IsContinuous
    ((J.over U).over (Over.mk f)) (J.over (Over.mk f).left))

/-- Continuity of the inverse of `CategoryTheory.Over.iteratedSliceEquiv`, in the spelling instance
search needs. -/
local instance isContinuous_iteratedSliceEquiv_inverse :
    (Over.mk f).iteratedSliceEquiv.inverse.IsContinuous (J.over V)
      ((J.over U).over (Over.mk f)) :=
  inferInstanceAs ((Over.mk f).iteratedSliceBackward.IsContinuous
    (J.over (Over.mk f).left) ((J.over U).over (Over.mk f)))

/-- The equivalence between sheaves of modules on the slice `C/V` and on the iterated slice of
`C/U` at `Over.mk f`, induced by `CategoryTheory.Over.iteratedSliceEquiv`. Its inverse is
`Stacks.SheafOfModules.sliceBackward`. -/
def iteratedSliceModulesEquivalence :
    SheafOfModules.{u} (O.over V) ≌ SheafOfModules.{u} ((O.over U).over (Over.mk f)) :=
  SheafOfModules.pushforwardPushforwardEquivalence.{u} (Over.iteratedSliceEquiv (Over.mk f))
    (S := (O.over U).over (Over.mk f)) (R := O.over V) (𝟙 _) (𝟙 _)
    (by ext : 2; exact O.obj.map_id _) (by ext : 2; exact O.obj.map_id _)

/-- The inverse of `iteratedSliceModulesEquivalence` is transport from the iterated slice. -/
theorem iteratedSliceModulesEquivalence_inverse :
    (iteratedSliceModulesEquivalence J O f).inverse = Stacks.SheafOfModules.sliceBackward.{u} O f :=
  rfl

/-- **Transport of sheaves of modules from an iterated slice preserves K-injective complexes.**
It is one half of an adjoint equivalence, so its left adjoint is the other half, which is exact;
this is the adjoint criterion for K-injectivity, Stacks 08BJ. -/
theorem isKInjective_sliceBackward
    (I : CochainComplex (SheafOfModules.{u} ((O.over U).over (Over.mk f))) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((Stacks.SheafOfModules.sliceBackward.{u} O f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  let e := iteratedSliceModulesEquivalence J O f
  have : e.functor.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_full _
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : (Stacks.SheafOfModules.sliceBackward.{u} O f).Additive := inferInstance
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
    (Stacks.SheafOfModules.sliceBackward.{u} O f) e.functor e.toAdjunction I

/-- **Stacks 08FI for the slice-to-slice restriction.** Restriction of sheaves of modules along
`Over.map f`, for an arrow `f : V ⟶ U` of the site, carries K-injective complexes to K-injective
complexes.

Restriction along `Over.map f` is restriction to the slice of `C/U` at `Over.mk f` followed by the
transport of that iterated slice to `C/V`. The first preserves K-injectivity by the library's form of
Stacks 08FI for `SheafOfModules.overFunctor`, extension by zero being an exact left adjoint of it,
and the second by `isKInjective_sliceBackward`. -/
@[stacks 08FI "for the restriction between two slices, along `Over.map`"]
theorem isKInjective_overMap
    (I : CochainComplex (SheafOfModules.{u} (O.over U)) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((_root_.SheafOfModules.overMap.{u} O f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  have h₁ : CochainComplex.IsKInjective
      (((_root_.SheafOfModules.overFunctor.{u} (O.over U) (Over.mk f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    isKInjective_over (J.over U) (O.over U) (Over.mk f) I
  have h₂ : CochainComplex.IsKInjective
      (((_root_.SheafOfModules.overFunctor.{u} (O.over U) (Over.mk f)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (Stacks.SheafOfModules.sliceBackward.{u} O f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I) :=
    isKInjective_sliceBackward J O f _
  exact CochainComplex.isKInjective_of_iso
    ((Stacks.SheafOfModules.sliceBackwardComplexIso.{u} O f).app I)

end Stacks.Cohomology.Localization

end
