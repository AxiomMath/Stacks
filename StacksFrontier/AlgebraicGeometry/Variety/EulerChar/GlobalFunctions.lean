module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# Schemes over a field whose global functions are the constants

Let `X` be a scheme over a field `k`. If `H⁰(X, 𝒪_X)` is one-dimensional over `k`, then the
structure map `k → Γ(X, 𝒪_X)` is an isomorphism: it is a ring map out of a field into a nonzero
ring, hence injective, between `k`-vector spaces of the same dimension one. A proper scheme over
`k` whose ring of global functions is `k` is connected: a field has no idempotents other than
`0` and `1`.

## Main results

* `AlgebraicGeometry.isIso_globalSections_of_finrank_cohomologyOverField_unit_zero_eq_one`: if
  `dim_k H⁰(X, 𝒪_X) = 1` then `k → Γ(X, 𝒪_X)` is an isomorphism.

## References

* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **A scheme over a field with one-dimensional `H⁰(X, 𝒪_X)` has only constant global
functions.** If `dim_k H⁰(X, 𝒪_X) = 1`, the structure map `k → Γ(X, 𝒪_X)` is an isomorphism. -/
theorem isIso_globalSections_of_finrank_cohomologyOverField_unit_zero_eq_one
    (f : X ⟶ Spec (.of k))
    (h : Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    simpa [Scheme.Hom.appTop] using f.appLE_eq_app (U := ⊤)
  set ρ := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom with hρ
  let e := (ModuleCat.restrictScalars ρ).mapIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).rightDerivedZeroIsoSelf.app
      (SheafOfModules.unit X.ringCatSheaf))
  let M := (ModuleCat.restrictScalars ρ).obj
    ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj
      (SheafOfModules.unit X.ringCatSheaf))
  have hfr : Module.finrank k M = 1 := e.toLinearEquiv.finrank_eq ▸ h
  have hntM : Nontrivial M := Module.nontrivial_of_finrank_eq_succ hfr
  have hnt : Nontrivial Γ(X, ⊤) := hntM
  have : FiniteDimensional k M := Module.finite_of_finrank_eq_succ hfr
  let φ : k →ₗ[k] M :=
    { toFun := fun a => ρ a
      map_add' := fun a b => map_add ρ a b
      map_smul' := fun a b => map_mul ρ a b }
  have hinj : Function.Injective φ := ρ.injective
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [Module.finrank_self, hfr])).1 hinj
  rw [← happ]
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hinj, hsurj⟩

end AlgebraicGeometry

end
