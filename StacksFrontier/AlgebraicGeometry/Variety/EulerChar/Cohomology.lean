module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Sheaf cohomology on a scheme over a field

For a scheme equipped with a structure morphism to the spectrum of a field, the sheaf
cohomology of a module is a module over that field: the right-derived global sections carry
the action obtained by restricting scalars along the structure morphism.

## Main definitions

* `AlgebraicGeometry.cohomologyOverField` regards sheaf cohomology on a scheme over a field as
  a module over that field.

## Implementation notes

Schemes over `k` are represented by explicit structure morphisms to `Spec k`. Cohomology is
formed as the right-derived functor of evaluation on the whole space; restricting scalars along
the composite of the inverse of the canonical isomorphism `Γ(Spec k) ≅ k` with the induced map
on sections supplies the `k`-module structure.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

/-- Evaluating a sheaf of modules on the whole space is an additive functor: the global sections
of a sum of two maps of modules is the sum of their global sections. -/
public instance evaluationAdditive (X : Scheme.{u}) :
    (SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).Additive := by
  unfold SheafOfModules.evaluation
  infer_instance

/-- Cohomology of a module on a scheme over `k`, with its canonical `k`-module structure. -/
public noncomputable def cohomologyOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerived n |>.obj F)

end AlgebraicGeometry
