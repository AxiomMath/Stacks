module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.LowerBound
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.SmoothUpperBound
public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.CurveModel
public import Mathlib.FieldTheory.SeparablyGenerated

/-!
# The Riemann hypothesis for curves over finite fields

Let `X` be a proper curve over a finite field `k` with `q` elements whose local rings at its
places are discrete valuation rings, and let `N m = #X(k_m)`. Then for some `C`, `m₀` and
`d ≠ 0`,

`q ^ m ≤ N m + C · √q ^ m`  for every `m ≥ m₀` divisible by `d`.

Choose a separating transcendental `x` of the function field `K = R(X)` over the perfect field
`k`, so that `K/k(x)` is finite separable. The Frobenius-fixed points of the integral closure
`B_K` of `k[x]` in `K` are points of `X` (`Stacks.BombieriStepanov.ncard_frobFixed_le`), and the
lower bound for `B_K` is `Stacks.BombieriStepanov.exists_lower_bound_of_isSeparable`.

Together with the upper bound this proves the Riemann hypothesis for a smooth proper
geometrically integral curve, granted the point count formula
`N m = 1 - ∑ α_i ^ m + q ^ m` and the pairing `α_i α_j = q` of the eigenvalues
(`Stacks.BombieriStepanov.norm_eq_sqrt_of_smooth`).

## Main results

* `Stacks.BombieriStepanov.exists_lower_bound_of_isCurve`
* `Stacks.BombieriStepanov.norm_eq_sqrt_of_smooth`
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order Polynomial

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The structure of `k`-algebra on the function field of a curve is the one of the variety. -/
theorem functionFieldAlgebra_eq [IsCurve k p] :
    varietyFunctionFieldAlgebra (⟨X, p⟩ : Variety k) = functionFieldAlgebra p :=
  Algebra.algebra_ext _ _ fun c => functionFieldAlgebraMap_eq_fieldToStalk _ c

/-- **The lower bound of the Riemann hypothesis for curves.** -/
theorem exists_lower_bound_of_isCurve [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    [IsProper p] [IsCurve k p] [IsLocallyNoetherian X]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m) :
    ∃ (C : ℝ) (m₀ d : ℕ), d ≠ 0 ∧ ∀ m : ℕ, m₀ ≤ m → d ∣ m →
      (Fintype.card k : ℝ) ^ m ≤ N m + C * Real.sqrt (Fintype.card k) ^ m := by
  classical
  let : Algebra k X.functionField := functionFieldAlgebra p
  -- the function field is finitely generated of transcendence degree one
  have hess : Algebra.EssFiniteType k X.functionField := by
    have := varietyFunctionField_essFiniteType (⟨X, p⟩ : Variety k)
    rwa [functionFieldAlgebra_eq] at this
  have htrK : Algebra.trdeg k X.functionField = 1 := by
    have := (isCurve_iff_trdeg_functionField_eq_one (⟨X, p⟩ : Variety k)).1 inferInstance
    rwa [functionFieldAlgebra_eq] at this
  -- a separating transcendental element
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k
    X.functionField
  have hcard : s.card = 1 := by
    have h := hs.cardinalMk_eq_trdeg
    rw [htrK, Cardinal.mk_coe_finset] at h
    exact_mod_cast h
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hcard
  have hx : Transcendental k x := by
    have := hs.1.transcendental ⟨x, Finset.mem_singleton_self x⟩
    exact this
  have hrange : Set.range ((↑) : ({x} : Finset X.functionField) → X.functionField) = {x} := by
    ext y
    simp
  set F₀ := IntermediateField.adjoin k ({x} : Set X.functionField)
  have : Algebra.IsSeparable F₀ X.functionField := by
    have h := hsep
    rw [Finset.coe_singleton] at h
    exact h
  have : Algebra.IsAlgebraic F₀ X.functionField := by
    have h := hs.isAlgebraic_field
    rw [hrange] at h
    exact h
  have : Algebra.EssFiniteType F₀ X.functionField := Algebra.EssFiniteType.of_comp k F₀ _
  have : FiniteDimensional F₀ X.functionField := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have htr₀ : Algebra.trdeg k F₀ = 1 := by
    have h := trdeg_add_eq k F₀ (A := X.functionField)
    rw [_root_.trdeg_eq_zero (R := F₀) (A := X.functionField), add_zero, htrK] at h
    exact h
  -- `F₀` is the fraction field of `k[x]`
  let e : RatFunc k ≃ₐ[k] F₀ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra k[X] F₀ := ((e : RatFunc k →+* F₀).comp (algebraMap k[X] (RatFunc k))).toAlgebra
  have : IsScalarTower k k[X] F₀ := IsScalarTower.of_algebraMap_eq fun c => by
    show algebraMap k F₀ c = e (algebraMap k[X] (RatFunc k) (algebraMap k k[X] c))
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  have : IsFractionRing k[X] F₀ :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors k[X])
      { e with commutes' := fun _ => rfl }
  let : Algebra k[X] X.functionField :=
    ((algebraMap F₀ X.functionField).comp (algebraMap k[X] F₀)).toAlgebra
  have : IsScalarTower k[X] F₀ X.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k k[X] X.functionField := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k[X] F₀ X.functionField,
      ← IsScalarTower.algebraMap_apply k k[X] F₀, ← IsScalarTower.algebraMap_apply]
  -- the Frobenius-fixed points of the integral closure of `k[x]` are points of `X`
  set Ω := AlgebraicClosure k
  set A := integralClosure k[X] X.functionField
  have : IsDedekindDomain A := integralClosure.isDedekindDomain k[X] F₀ X.functionField
  have : IsFractionRing A X.functionField :=
    integralClosure.isFractionRing_of_finite_extension F₀ X.functionField
  have hkA : ∀ c : k, algebraMap A X.functionField (algebraMap k A c) =
      (fieldToStalk p (genericPoint X)).hom c := by
    intro c
    rw [← IsScalarTower.algebraMap_apply k A X.functionField]
    rfl
  have hM : ∀ m : ℕ, m ≠ 0 →
      {ψ : PointsOver A (algebraMap k Ω) | ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.Finite ∧
      {ψ : PointsOver A (algebraMap k Ω) | ∀ a, ψ.1 a ^ (Fintype.card k ^ m) = ψ.1 a}.ncard ≤
        N m := fun m hm =>
    ncard_frobFixed_le pr p hdvr hkA (algebraMap k Ω) hm (N m) (hNcard m hm)
  obtain ⟨C, m₀, d, f, hd, h2d, hqf, hbound⟩ :=
    exists_lower_bound_of_isSeparable pr htr₀ (algebraMap k Ω) N hM
  refine ⟨C, m₀, d, hd, fun m hm hdm => ?_⟩
  have h := hbound m hm hdm
  obtain ⟨t, rfl⟩ := h2d.trans hdm
  have hsq : Real.sqrt (Fintype.card k) ^ (2 * t) = (pr : ℝ) ^ ((f : ℕ) * (2 * t) / 2) := by
    rw [pow_mul, Real.sq_sqrt (by positivity), hqf]
    push_cast
    rw [← pow_mul]
    congr 1
    rw [show (f : ℕ) * (2 * t) = 2 * ((f : ℕ) * t) by ring, Nat.mul_div_cancel_left _ two_pos]
  rw [hsq]
  have h' : ((Fintype.card k ^ (2 * t) : ℤ) : ℝ) ≤
      ((N (2 * t) + C * pr ^ (f * (2 * t) / 2) : ℤ) : ℝ) :=
    by exact_mod_cast h
  push_cast at h'
  exact h'

/-- **The Riemann hypothesis for curves over finite fields (Bombieri–Stepanov).** Let `X` be a
smooth proper geometrically integral curve over a finite field `k` with `q` elements, with
`N m = #X(k_m)`. If `N m = 1 - ∑ α_i ^ m + q ^ m` for all `m ≥ 1` (the point count formula of
Tag 03V8, part (3)) and the `α_i` are paired by `α_i α_j = q`, then `‖α_i‖ = √q` for every `i`.
The upper bound is `Stacks.BombieriStepanov.exists_upper_bound_of_smooth` and the lower bound
is `Stacks.BombieriStepanov.exists_lower_bound_of_isCurve`. -/
theorem norm_eq_sqrt_of_smooth [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    [IsProper p] [Smooth p] [GeometricallyIntegral p] [IsCurve k p]
    (N : ℕ → ℕ) (hNcard : ∀ m : ℕ, m ≠ 0 → ∀ (K : Type u) [Field K] [Algebra k K] [Finite K],
      Module.finrank k K = m → Nat.card (Stacks.EtaleCohomology.fieldValuedPoints p K) = N m)
    {ι : Type*} [Fintype ι] (α : ι → ℂ)
    (hN : ∀ m : ℕ, m ≠ 0 → (N m : ℂ) = 1 - (∑ i, α i ^ m) + (Fintype.card k : ℂ) ^ m)
    (hpair : ∀ i, ∃ j, α i * α j = Fintype.card k) (i : ι) :
    ‖α i‖ = Real.sqrt (Fintype.card k) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨C, m₀, d, hd, hlower⟩ := exists_lower_bound_of_isCurve p pr
    (isDiscreteValuationRing_stalk_of_coheight_eq_one p) N hNcard
  exact norm_eq_sqrt_of_lower_bound_of_smooth p pr N hNcard α hN C m₀ d hd hlower hpair i

end Stacks.BombieriStepanov

end
