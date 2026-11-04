module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.GradedCommutativity
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinProjection
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# Wedging with an exact one-form on the left

Let `π : X ⟶ S` be a morphism of schemes and `b ∈ Γ(X, 𝒪_X)`. Wedging a `p`-form with the exact
one-form `d b` can be done on either side, and the two differ by the sign `(-1)^p`. The right
multiplication `ω ↦ ω ∧ d b` is `AlgebraicGeometry.Scheme.Hom.exactFormWedgeHom` and the left one
is `AlgebraicGeometry.Scheme.Hom.formLeftWedgeHom` at the global section `d b`; this file proves
that a morphism out of `Ω^{p+1}_{X/S}` killing the first kills the second.

That is the form in which the comparison is needed: the presentation of [Stacks, Tag 01CJ] wedges
the new degree-one factor on the **left**, while the Gysin construction of [Stacks, Tag 0G83]
kills the forms `ω ∧ d f_j`, with the factor on the **right**.

## Main results

* `AlgebraicGeometry.Scheme.Hom.heq_mul_exactOneFormSection`: **the two wedges with an exact
  one-form differ by the sign `(-1)^p`**, on every local section.
* `AlgebraicGeometry.Scheme.Hom.formLeftWedgeHom_exactOneFormSection_comp_eq_zero`: **a morphism
  killing the right wedge `ω ∧ d b` kills the left wedge `d b ∧ ω`.**

## Implementation notes

The sign is the graded commutativity of the wedge product,
`AlgebraicGeometry.SheafOfModules.ofGradedForm_mul_comm`, in the degrees `(1, p)`: nothing is
re-proved here, and in particular no locality argument appears, because that statement already
holds for arbitrary local sections.

The degree of a product in a sheaf of graded algebras is the sum of the degrees in the order in
which the factors are multiplied, so `d b ∧ ω` lives in degree `1 + p` and `ω ∧ d b` in degree
`p + 1`. The two sheaves are equal but not definitionally so; both are compared to a common
degree `N` through `eqToHom`, which is how
`AlgebraicGeometry.Scheme.Hom.FormKernelGeneratedByEquations` spells the degree of the wedge as
well.

## References

* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped DirectSum

universe u

attribute [local instance] AlgebraicGeometry.SheafOfModules.gradedFormsGOne
  AlgebraicGeometry.SheafOfModules.gradedFormsGMul
  AlgebraicGeometry.SheafOfModules.gradedFormsGRing

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- Two local sections of equal degree which are heterogeneously equal have the same image under
the two degree comparisons into a common degree. -/
private theorem eqToHom_app_eq_eqToHom_app {P Q R : X.Modules} (e₁ : P = R) (e₂ : Q = R)
    (U : X.Opensᵒᵖ) (u : P.val.obj U) (w : Q.val.obj U) (h : HEq u w) :
    (eqToHom e₁).val.app U u = (eqToHom e₂).val.app U w := by
  subst e₁
  subst e₂
  cases h
  rfl

/-- **The two wedges with an exact one-form differ by the sign `(-1)^p`.** On a local section
`ω` of `Ω^p_{X/S}`, the left wedge `d b ∧ ω` is `(-1)^p` times the right wedge `ω ∧ d b`; the two
live in the degrees `1 + p` and `p + 1`, whence the heterogeneous equality.

This is the graded commutativity of the wedge product of [Stacks, Tag 0FM3], available as
`AlgebraicGeometry.SheafOfModules.ofGradedForm_mul_comm`, in the degrees `(1, p)`. -/
theorem heq_mul_exactOneFormSection (π : X ⟶ S) (b : Γ(X, ⊤)) (p : ℕ) (U : X.Opensᵒᵖ)
    (ω : (relativeDifferentialForms π (p : ℤ)).val.obj U) :
    HEq (((relativeDifferentialFormsAlgebra π).mul 1 (p : ℤ)).app U
          ((exactOneFormSection π b).eval U) ω)
      (((-1 : ℤ) ^ p) •
        ((relativeDifferentialFormsAlgebra π).mul (p : ℤ) 1).app U ω
          ((exactOneFormSection π b).eval U)) := by
  refine SheafOfModules.heq_of_ofGradedForm_eq (Scheme.Hom.deRhamAlgebras π) (by omega) ?_
  have h1 := SheafOfModules.ofGradedForm_mul (Scheme.Hom.deRhamAlgebras π) U 1 (p : ℤ)
    ((exactOneFormSection π b).eval U) ω
  have h2 := SheafOfModules.ofGradedForm_mul_comm (Scheme.Hom.deRhamAlgebras π) 1 p U
    ((exactOneFormSection π b).eval U) ω
  have h3 := SheafOfModules.ofGradedForm_mul (Scheme.Hom.deRhamAlgebras π) U (p : ℤ) 1 ω
    ((exactOneFormSection π b).eval U)
  have h4 := map_zsmul (SheafOfModules.ofGradedForm (Scheme.Hom.deRhamAlgebras π) U ((p : ℤ) + 1))
    ((-1 : ℤ) ^ p)
    (((Scheme.Hom.deRhamAlgebras π).exterior.mul (p : ℤ) 1).app U ω
      ((exactOneFormSection π b).eval U))
  rw [one_mul] at h2
  exact h1.trans (h2.trans ((congrArg
    (fun z : SheafOfModules.totalForms (Scheme.Hom.deRhamAlgebras π) U =>
      ((-1 : ℤ) ^ p) • z) h3.symm).trans h4.symm))

/-- **A morphism killing the right wedge with `d b` kills the left wedge with `d b`.**

If `ψ` is a morphism out of `Ω^N_{X/S}` which annihilates every form `ω ∧ d b` with `ω` of
exterior degree `p`, then it annihilates every form `d b ∧ ω`: the two differ by the sign
`(-1)^p`, by `AlgebraicGeometry.Scheme.Hom.heq_mul_exactOneFormSection`. -/
theorem formLeftWedgeHom_exactOneFormSection_comp_eq_zero (π : X ⟶ S) (b : Γ(X, ⊤)) (p : ℕ)
    {N : ℤ}
    (h₁ : 1 + (p : ℤ) = N) (h₂ : (p : ℤ) + 1 = N) {T : X.Modules}
    (ψ : relativeDifferentialForms π N ⟶ T)
    (hψ : exactFormWedgeHom π b (p : ℤ) ≫
      eqToHom (congrArg (relativeDifferentialForms π) h₂) ≫ ψ = 0) :
    formLeftWedgeHom π (exactOneFormSection π b) (p : ℤ) ≫
      eqToHom (congrArg (relativeDifferentialForms π) h₁) ≫ ψ = 0 := by
  set A := relativeDifferentialFormsAlgebra π with hA
  set e₁ := congrArg (relativeDifferentialForms π) h₁ with he₁
  set e₂ := congrArg (relativeDifferentialForms π) h₂ with he₂
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun ω => ?_))
  have hzeroψ : ψ.val.app U ((eqToHom e₂).val.app U
      ((A.mul (p : ℤ) 1).app U ω ((exactOneFormSection π b).eval U))) = 0 := by
    have h : (exactFormWedgeHom π b (p : ℤ) ≫ eqToHom e₂ ≫ ψ).val.app U ω = 0 := by
      rw [hψ]
      rfl
    exact h
  show ψ.val.app U ((eqToHom e₁).val.app U
    ((A.mul 1 (p : ℤ)).app U ((exactOneFormSection π b).eval U) ω)) = 0
  refine Eq.trans (congrArg (ψ.val.app U) (eqToHom_app_eq_eqToHom_app e₁ e₂ U _
    (((-1 : ℤ) ^ p) • (A.mul (p : ℤ) 1).app U ω ((exactOneFormSection π b).eval U))
    (heq_mul_exactOneFormSection π b p U ω))) ?_
  rw [map_zsmul, map_zsmul, hzeroψ, smul_zero]

end AlgebraicGeometry.Scheme.Hom

end
