module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Substitution

/-!
# Binary quadratic forms and the normal form of a nodal power-series hypersurface

A binary quadratic form `q = a x² + b x y + c y²` is *nondegenerate* if `4ac - b² ≠ 0`. Over an
algebraically closed field `k`, the power-series hypersurface `k[[x, y]]/(q)` cut out by a
nondegenerate binary quadratic form is isomorphic to `k[[x, y]]/(xy)`.

## Main definitions

* `Stacks.Curves.nodalBinaryQuadratic` — the binary quadratic form `a x² + b x y + c y²` as a
  power series in two variables.
* `Stacks.Curves.linearSubst` — the substitution family of a `2 × 2` matrix of scalars.
* `Stacks.Curves.linearSubstAlgEquiv` — the algebra automorphism of `k[[x, y]]` given by an
  invertible such substitution.

## Main results

* `Stacks.Curves.exists_linearFactorization_of_nondegenerate` — over an algebraically closed
  field a nondegenerate binary quadratic form is a product of two linearly independent linear
  forms.
* `Stacks.Curves.subst_linearSubst_X_mul_X` — a linear substitution carries `x y` to the
  binary quadratic form with coefficients read off from the matrix.
* `Stacks.Curves.nonempty_quotient_nodalBinaryQuadratic_algEquiv` — over an algebraically
  closed field, `k[[x, y]]/(q)` for a nondegenerate binary quadratic form `q` is isomorphic as
  a `k`-algebra to `k[[x, y]]/(xy)`.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public noncomputable section

open MvPowerSeries

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k]

/-- The binary quadratic form `a x² + b x y + c y²`, regarded as a power series in two
variables. -/
def nodalBinaryQuadratic (a b c : k) : MvPowerSeries (Fin 2) k :=
  C a * X 0 ^ 2 + C b * X 0 * X 1 + C c * X 1 ^ 2

/-- The substitution family of the matrix `!![α, β; γ, δ]`, sending the first variable to
`α x + β y` and the second to `γ x + δ y`. -/
def linearSubst (α β γ δ : k) : Fin 2 → MvPowerSeries (Fin 2) k :=
  ![C α * X 0 + C β * X 1, C γ * X 0 + C δ * X 1]

/-- The first entry of `linearSubst α β γ δ` is `α x + β y`. -/
@[simp]
theorem linearSubst_zero (α β γ δ : k) :
    linearSubst α β γ δ 0 = C α * X 0 + C β * X 1 :=
  rfl

/-- The second entry of `linearSubst α β γ δ` is `γ x + δ y`. -/
@[simp]
theorem linearSubst_one (α β γ δ : k) :
    linearSubst α β γ δ 1 = C γ * X 0 + C δ * X 1 :=
  rfl

/-- A linear substitution family has zero constant coefficients, hence is substitutable. -/
theorem hasSubst_linearSubst (α β γ δ : k) : HasSubst (linearSubst α β γ δ) :=
  hasSubst_of_constantCoeff_zero fun i ↦ by fin_cases i <;> simp

/-- Substitution is `k`-linear on linear forms in the two variables. -/
theorem subst_linear {b : Fin 2 → MvPowerSeries (Fin 2) k} (hb : HasSubst b) (α β : k) :
    subst b (C α * X 0 + C β * X 1) = C α * b 0 + C β * b 1 := by
  rw [subst_add hb, subst_mul hb, subst_mul hb, subst_C, subst_C, subst_X hb, subst_X hb]

/-- The identity matrix substitutes each variable for itself. -/
theorem linearSubst_one_zero_zero_one : linearSubst (1 : k) 0 0 1 = X := by
  funext i
  fin_cases i <;> simp

/-- Composing two linear substitutions is the linear substitution of the product matrix. -/
theorem subst_linearSubst_linearSubst (α β γ δ α' β' γ' δ' : k) :
    (fun s ↦ subst (linearSubst α' β' γ' δ') (linearSubst α β γ δ s)) =
      linearSubst (α * α' + β * γ') (α * β' + β * δ') (γ * α' + δ * γ') (γ * β' + δ * δ') := by
  have h := hasSubst_linearSubst α' β' γ' δ' (k := k)
  funext i
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, linearSubst_zero, linearSubst_one, subst_linear h,
      map_add, map_mul] <;>
    ring

/-- A linear substitution carries `x y` to the binary quadratic form whose coefficients are the
products of matrix entries occurring in the expansion of the corresponding product of linear
forms. -/
theorem subst_linearSubst_X_mul_X (α β γ δ : k) :
    subst (linearSubst α β γ δ) ((X 0 : MvPowerSeries (Fin 2) k) * X 1) =
      nodalBinaryQuadratic (α * γ) (α * δ + β * γ) (β * δ) := by
  have h := hasSubst_linearSubst α β γ δ (k := k)
  rw [subst_mul h, subst_X h, subst_X h, linearSubst_zero, linearSubst_one,
    nodalBinaryQuadratic]
  simp only [map_add, map_mul]
  ring

/-- Two linear substitutions whose matrices are mutually inverse undo each other. -/
theorem subst_subst_linearSubst (α β γ δ α' β' γ' δ' : k)
    (h0 : α * α' + β * γ' = 1) (h1 : α * β' + β * δ' = 0)
    (h2 : γ * α' + δ * γ' = 0) (h3 : γ * β' + δ * δ' = 1)
    (f : MvPowerSeries (Fin 2) k) :
    subst (linearSubst α' β' γ' δ') (subst (linearSubst α β γ δ) f) = f := by
  rw [subst_comp_subst_apply (hasSubst_linearSubst α β γ δ) (hasSubst_linearSubst α' β' γ' δ'),
    subst_linearSubst_linearSubst, h0, h1, h2, h3, linearSubst_one_zero_zero_one]
  exact congrFun subst_self f

/-- The algebra automorphism of `k[[x, y]]` given by an invertible linear substitution. -/
def linearSubstAlgEquiv (α β γ δ : k) (h : α * δ - β * γ ≠ 0) :
    MvPowerSeries (Fin 2) k ≃ₐ[k] MvPowerSeries (Fin 2) k :=
  have he : (α * δ - β * γ) * (α * δ - β * γ)⁻¹ = 1 := mul_inv_cancel₀ h
  AlgEquiv.ofAlgHom (substAlgHom (hasSubst_linearSubst α β γ δ))
    (substAlgHom (hasSubst_linearSubst (δ * (α * δ - β * γ)⁻¹) (-β * (α * δ - β * γ)⁻¹)
      (-γ * (α * δ - β * γ)⁻¹) (α * (α * δ - β * γ)⁻¹)))
    (AlgHom.ext fun f ↦ by
      simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.coe_id, id_eq]
      exact subst_subst_linearSubst _ _ _ _ _ _ _ _ (by linear_combination he) (by ring)
        (by ring) (by linear_combination he) f)
    (AlgHom.ext fun f ↦ by
      simp only [AlgHom.comp_apply, substAlgHom_apply, AlgHom.coe_id, id_eq]
      exact subst_subst_linearSubst _ _ _ _ _ _ _ _ (by linear_combination he) (by ring)
        (by ring) (by linear_combination he) f)

/-- `linearSubstAlgEquiv α β γ δ h` acts by substitution along `linearSubst α β γ δ`. -/
@[simp]
theorem linearSubstAlgEquiv_apply (α β γ δ : k) (h : α * δ - β * γ ≠ 0)
    (f : MvPowerSeries (Fin 2) k) :
    linearSubstAlgEquiv α β γ δ h f = subst (linearSubst α β γ δ) f := by
  simp [linearSubstAlgEquiv]

/-- Over an algebraically closed field every quadratic polynomial with invertible leading
coefficient has a root. -/
theorem exists_eval_quadratic_eq_zero [IsAlgClosed k] {a : k} (ha : a ≠ 0) (b c : k) :
    ∃ z : k, a * z ^ 2 + b * z + c = 0 := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root
    (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X + Polynomial.C c)
    (by rw [Polynomial.degree_quadratic ha]; decide)
  exact ⟨z, by simpa using hz⟩

/-- Over an algebraically closed field a nondegenerate binary quadratic form
`a x² + b x y + c y²` is the product of two linearly independent linear forms
`(α x + β y)(γ x + δ y)`. The coefficients of the product are recorded as the three
equations, and linear independence as `α δ - β γ ≠ 0`. -/
theorem exists_linearFactorization_of_nondegenerate [IsAlgClosed k] (a b c : k)
    (h : 4 * a * c - b ^ 2 ≠ 0) :
    ∃ α β γ δ : k, α * δ - β * γ ≠ 0 ∧ α * γ = a ∧ α * δ + β * γ = b ∧ β * δ = c := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b ≠ 0 := by rintro rfl; simp at h
    exact ⟨0, 1, b, c, by simpa using hb, by ring, by ring, by ring⟩
  · obtain ⟨z, hz⟩ := exists_eval_quadratic_eq_zero ha (-b) c
    refine ⟨a, b - a * z, 1, z, fun h0 ↦ h ?_, by ring, by ring, by linear_combination -hz⟩
    linear_combination 4 * a * hz - (2 * a * z - b) * h0

/-- Over an algebraically closed field, the power-series hypersurface cut out by a
nondegenerate binary quadratic form is isomorphic, as an algebra over the field, to the
hypersurface cut out by `xy`. -/
theorem nonempty_quotient_nodalBinaryQuadratic_algEquiv [IsAlgClosed k] (a b c : k)
    (h : 4 * a * c - b ^ 2 ≠ 0) :
    Nonempty ((MvPowerSeries (Fin 2) k ⧸ Ideal.span {nodalBinaryQuadratic a b c}) ≃ₐ[k]
      (MvPowerSeries (Fin 2) k ⧸ Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1})) := by
  obtain ⟨α, β, γ, δ, hdet, ha, hb, hc⟩ := exists_linearFactorization_of_nondegenerate a b c h
  refine ⟨(Ideal.quotientEquivAlg (Ideal.span {(X 0 : MvPowerSeries (Fin 2) k) * X 1})
    (Ideal.span {nodalBinaryQuadratic a b c}) (linearSubstAlgEquiv α β γ δ hdet) ?_).symm⟩
  simp [Ideal.map_span, subst_linearSubst_X_mul_X, ha, hb, hc]

end Stacks.Curves

end
