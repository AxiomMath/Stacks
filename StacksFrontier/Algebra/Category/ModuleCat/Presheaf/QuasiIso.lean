module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Crystalline.SheafComparison

/-!
# A map of complexes of presheaves of modules is a quasi-isomorphism sectionwise

A map of cochain complexes of presheaves of modules is a quasi-isomorphism exactly when its
value over each object is one. This file proves the direction that is not formal — from the
sections to the presheaf — by way of the forgetful functor to presheaves of abelian groups,
whose target is a functor category, where Mathlib's
`CategoryTheory.HomologicalComplex.quasiIso_iff_evaluation` applies.

## Main results

* `PresheafOfModules.quasiIso_of_forall_quasiIso_evaluation`: **a map of complexes of presheaves
  of modules whose value over every object is a quasi-isomorphism is a quasi-isomorphism.**

## Implementation notes

Three functors are exact here and so preserve homology, each because it preserves finite limits
and finite colimits: evaluation at an object, the forgetful functor to presheaves of abelian
groups, and the forgetful functor from modules to abelian groups. The one fact that is not an
instance is that the forgetful functor to presheaves of abelian groups *reflects* isomorphisms,
and that is `PresheafOfModules.isIso_of_forall_isIso_app` together with the fact that a bijective
map of modules is invertible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- Evaluation of presheaves of modules at an object is exact, hence preserves homology. -/
instance preservesHomology_evaluation (V : Cᵒᵖ) :
    (PresheafOfModules.evaluation.{w} R V).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The forgetful functor to presheaves of abelian groups is exact, hence preserves homology. -/
instance preservesHomology_toPresheaf :
    (PresheafOfModules.toPresheaf.{w} R).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **The forgetful functor to presheaves of abelian groups reflects isomorphisms**: a map of
presheaves of modules whose underlying map of presheaves of abelian groups is invertible is
invertible, its value over each object being a bijective map of modules. -/
instance reflectsIsomorphisms_toPresheaf :
    (PresheafOfModules.toPresheaf.{w} R).ReflectsIsomorphisms where
  reflects {_M _N} φ _ := by
    refine isIso_of_forall_isIso_app φ fun V => ?_
    have h1 : IsIso (((PresheafOfModules.toPresheaf.{w} R).map φ).app V) := inferInstance
    exact (ConcreteCategory.isIso_iff_bijective (φ.app V)).2
      (ConcreteCategory.bijective_of_isIso (((PresheafOfModules.toPresheaf.{w} R).map φ).app V))

/-- **A map of complexes of presheaves of modules whose value over every object is a
quasi-isomorphism is a quasi-isomorphism.** -/
theorem quasiIso_of_forall_quasiIso_evaluation {ι : Type*} {cs : ComplexShape ι}
    {K L : HomologicalComplex (PresheafOfModules.{w} R) cs} (φ : K ⟶ L)
    (h : ∀ V, QuasiIso (((PresheafOfModules.evaluation.{w} R V).mapHomologicalComplex cs).map φ)) :
    QuasiIso φ := by
  rw [← HomologicalComplex.quasiIso_map_iff_of_preservesHomology φ
    (PresheafOfModules.toPresheaf.{w} R), HomologicalComplex.quasiIso_iff_evaluation]
  intro V
  have := h V
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((PresheafOfModules.evaluation.{w} R V).mapHomologicalComplex cs).map φ)
    (forget₂ (ModuleCat.{w} (R.obj V)) AddCommGrpCat.{w})

end PresheafOfModules

end
