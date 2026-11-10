module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniLinearCombinationCodimTwo
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniUniversalDivisorIrreducible

/-!
# The function field of the universal divisor over a trivializing chart

Let `R` be a commutative ring and let `g₀, …, gₙ ∈ R` with `g₀` invertible. Eliminating the
first variable from the universal linear form `x₀g₀ + ⋯ + xₙgₙ` identifies
`R[x₀, …, xₙ]/(x₀g₀ + ⋯ + xₙgₙ)` with the polynomial ring `R[x₁, …, xₙ]`. Over a domain `A` of
finite type over a field `k` this computes the function field of the universal divisor over an
affine chart on which the first section is invertible: it is `K(x₁, …, xₙ)` for `K = Frac(A)`.

## Main definitions

* `Algebra.eliminateFirst` is the `R`-algebra map `R[x₀, …, xₙ] → R[x₁, …, xₙ]` substituting
  `-∑ᵢ u gᵢ₊₁ xᵢ` for `x₀`, where `u` is an inverse of `g₀`.
* `Algebra.quotientSpanUniversalLinearFormEquiv` is the resulting identification
  `R[x₀, …, xₙ]/(x₀g₀ + ⋯ + xₙgₙ) ≃ₐ[R] R[x₁, …, xₙ]`.
* `Algebra.universalDivisorChartMap` is the map `A[x₀, …, xₙ] → Ω` of the chart into a fraction
  field of its ring.

## Main results

* `Algebra.isDomain_quotient_span_universalLinearForm`: over a domain the chart ring is a
  domain, so the universal divisor over the chart is integral.
* `Algebra.algebraicIndependent_algebraMap_X` and
  `Algebra.adjoin_range_algebraMap_X_eq_top`: a fraction field of `K[x₁, …, xₙ]` is generated
  over `K` by the algebraically independent variables, and
  `Algebra.algebraicIndependent_and_adjoin_eq_top_of_isFractionRing` is the same for a fraction
  field presented over `A[x₁, …, xₙ]`.
* `Algebra.isGeometricallyIrreducible_chartFunctionField` and
  `Algebra.isGeometricallyIrreducible_chartFunctionField_of_isFractionRing`: the function field
  `K(x₁, …, xₙ)` of the chart is geometrically irreducible over the subfield generated over `k`
  by the variables and by the linear combination `∑ᵢ gᵢxᵢ`, for `Ω` presented as a fraction
  field of `K[x₁, …, xₙ]` and of `A[x₁, …, xₙ]` respectively.
* `Algebra.isGeometricallyIrreducible_universalDivisorChart`: the same statement with `Ω`
  presented as a fraction field of the chart ring `A[x₀, …, xₙ]/(x₀f₀ + ⋯ + xₙfₙ)` itself and
  the base field generated over `k` by the images of all the parameters `x₀, …, xₙ`.
* `Algebra.algebraicIndependent_universalDivisorChartMap_X`: the images of the parameters
  `x₀, …, xₙ` in that fraction field are algebraically independent over `k`.

## References

* [Stacks Project, Tag 0G4F](https://stacks.math.columbia.edu/tag/0G4F)
* [Stacks Project, Tag 0G4D](https://stacks.math.columbia.edu/tag/0G4D)
* [Stacks Project, Tag 0G4E](https://stacks.math.columbia.edu/tag/0G4E)
-/

@[expose] public section

universe u

open MvPolynomial

namespace Algebra

/-! ### Eliminating the first variable -/

section Eliminate

variable {R : Type u} [CommRing R] {n : ℕ}

/-- The `R`-algebra map `R[x₀, …, xₙ] → R[x₁, …, xₙ]` substituting `-∑ᵢ u gᵢ₊₁ xᵢ` for `x₀`
and `xᵢ` for `xᵢ₊₁`. -/
noncomputable def eliminateFirst (g : Fin (n + 1) → R) (u : R) :
    MvPolynomial (Fin (n + 1)) R →ₐ[R] MvPolynomial (Fin n) R :=
  aeval (Fin.cases (-∑ i : Fin n, C (u * g i.succ) * X i) fun i => X i)

/-- `Algebra.eliminateFirst` fixes the constants. -/
@[simp]
theorem eliminateFirst_C (g : Fin (n + 1) → R) (u : R) (a : R) :
    eliminateFirst g u (C a) = C a := by
  simp [eliminateFirst]

/-- `Algebra.eliminateFirst` sends `x₀` to `-∑ᵢ u gᵢ₊₁ xᵢ`. -/
@[simp]
theorem eliminateFirst_X_zero (g : Fin (n + 1) → R) (u : R) :
    eliminateFirst g u (X 0) = -∑ i : Fin n, C (u * g i.succ) * X i := by
  simp [eliminateFirst]

/-- `Algebra.eliminateFirst` sends `xᵢ₊₁` to `xᵢ`. -/
@[simp]
theorem eliminateFirst_X_succ (g : Fin (n + 1) → R) (u : R) (i : Fin n) :
    eliminateFirst g u (X i.succ) = X i := by
  simp [eliminateFirst]

/-- **The universal linear form is killed by the elimination of `x₀`.** -/
theorem eliminateFirst_universalLinearForm (g : Fin (n + 1) → R) {u : R} (hu : u * g 0 = 1) :
    eliminateFirst g u (universalLinearForm g) = 0 := by
  have hsucc : ∀ i : Fin n,
      eliminateFirst g u (C (g i.succ) * X i.succ) = C (g i.succ) * X i := by
    intro i
    rw [map_mul, eliminateFirst_C, eliminateFirst_X_succ]
  have hzero : eliminateFirst g u (C (g 0) * X 0) = -∑ i : Fin n, C (g i.succ) * X i := by
    rw [map_mul, eliminateFirst_C, eliminateFirst_X_zero, mul_neg, Finset.mul_sum]
    refine congrArg Neg.neg (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [← mul_assoc, ← C_mul, ← mul_assoc, mul_comm (g 0) u, hu, one_mul]
  rw [universalLinearForm, map_sum, Fin.sum_univ_succ, hzero,
    Finset.sum_congr rfl fun i _ ↦ hsucc i, neg_add_cancel]

/-- The relation that the universal linear form imposes on the first variable: `x₀` is the
linear combination `-∑ᵢ u gᵢ₊₁ xᵢ₊₁` modulo the form. -/
theorem X_zero_add_sum_eq_C_mul_universalLinearForm (g : Fin (n + 1) → R) {u : R}
    (hu : u * g 0 = 1) :
    X 0 + ∑ i : Fin n, C (u * g i.succ) * X i.succ = C u * universalLinearForm g := by
  rw [universalLinearForm, Finset.mul_sum, Fin.sum_univ_succ]
  congr 1
  · rw [← mul_assoc, ← C_mul, hu, C_1, one_mul]
  · exact Finset.sum_congr rfl fun i _ ↦ by rw [← mul_assoc, ← C_mul]

/-- **Eliminating the first variable.** If `g₀` is invertible then the quotient of
`R[x₀, …, xₙ]` by the universal linear form of `g` is the polynomial ring `R[x₁, …, xₙ]`. -/
noncomputable def quotientSpanUniversalLinearFormEquiv (g : Fin (n + 1) → R) {u : R}
    (hu : u * g 0 = 1) :
    (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {universalLinearForm g}) ≃ₐ[R]
      MvPolynomial (Fin n) R := by
  have hker : ∀ a : MvPolynomial (Fin (n + 1)) R,
      a ∈ Ideal.span {universalLinearForm g} → eliminateFirst g u a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, eliminateFirst_universalLinearForm g hu, zero_mul]
  refine AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ (eliminateFirst g u) hker)
    ((Ideal.Quotient.mkₐ R (Ideal.span {universalLinearForm g})).comp (rename Fin.succ))
    ?_ ?_
  · rw [← AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp]
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rw [AlgHom.comp_apply, rename_X, eliminateFirst_X_succ, AlgHom.coe_id, id_eq]
  · refine Ideal.Quotient.algHom_ext (R₁ := R) ?_
    rw [AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp, AlgHom.id_comp]
    refine MvPolynomial.algHom_ext fun j ↦ ?_
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    refine Fin.cases ?_ (fun i ↦ ?_) j
    · rw [eliminateFirst_X_zero, Ideal.Quotient.eq]
      have hren : (rename (R := R) Fin.succ) (-∑ i : Fin n, C (u * g i.succ) * X i) =
          -∑ i : Fin n, C (u * g i.succ) * X i.succ := by
        simp
      have hsub : -∑ i : Fin n, C (u * g i.succ) * X i.succ - X (0 : Fin (n + 1)) =
          -(C u * universalLinearForm g) := by
        rw [← X_zero_add_sum_eq_C_mul_universalLinearForm g hu]; ring
      rw [hren, hsub]
      exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))
    · rw [eliminateFirst_X_succ, rename_X]

/-- **The chart ring contains its base.** If `g₀` is invertible then the structural map
`R → R[x₀, …, xₙ]/(∑ᵢ gᵢxᵢ)` is injective. -/
theorem injective_algebraMap_quotient_span_universalLinearForm (g : Fin (n + 1) → R) {u : R}
    (hu : u * g 0 = 1) :
    Function.Injective
      (algebraMap R (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {universalLinearForm g})) := by
  intro x y hxy
  refine MvPolynomial.C_injective (Fin n) R ?_
  rw [← MvPolynomial.algebraMap_eq, ← (quotientSpanUniversalLinearFormEquiv g hu).commutes,
    ← (quotientSpanUniversalLinearFormEquiv g hu).commutes, hxy]

/-- **Over a domain the chart ring is a domain.** If `R` is a domain and `g₀` is invertible,
the quotient of `R[x₀, …, xₙ]` by the universal linear form of `g` is a domain. -/
theorem isDomain_quotient_span_universalLinearForm [IsDomain R] (g : Fin (n + 1) → R) {u : R}
    (hu : u * g 0 = 1) :
    IsDomain (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {universalLinearForm g}) := by
  have e := quotientSpanUniversalLinearFormEquiv g hu
  have : Nontrivial (MvPolynomial (Fin (n + 1)) R ⧸ Ideal.span {universalLinearForm g}) :=
    e.toEquiv.nontrivial
  exact Function.Injective.isDomain (e : _ →+* MvPolynomial (Fin n) R) e.injective

end Eliminate

/-! ### The function field of the chart -/

section FunctionField

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] {σ : Type*}
  [Algebra (MvPolynomial σ K) Ω] [IsScalarTower K (MvPolynomial σ K) Ω]
  [IsFractionRing (MvPolynomial σ K) Ω]

/-- **The variables of a chart are algebraically independent.** The images of the variables in a
fraction field of `K[xᵢ : i ∈ σ]` are algebraically independent over `K`. -/
theorem algebraicIndependent_algebraMap_X :
    AlgebraicIndependent K
      (fun i : σ => algebraMap (MvPolynomial σ K) Ω (X i)) :=
  (MvPolynomial.algebraicIndependent_X σ K).map'
    (f := IsScalarTower.toAlgHom K (MvPolynomial σ K) Ω)
    (IsFractionRing.injective (MvPolynomial σ K) Ω)

/-- **A chart's function field is generated by its variables.** A fraction field of
`K[xᵢ : i ∈ σ]` is generated over `K`, as a field, by the images of the variables. -/
theorem adjoin_range_algebraMap_X_eq_top :
    IntermediateField.adjoin K
      (Set.range fun i : σ => algebraMap (MvPolynomial σ K) Ω (X i)) = ⊤ := by
  have himage : (Set.range fun i : σ ↦ algebraMap (MvPolynomial σ K) Ω (X i)) =
      IsScalarTower.toAlgHom K (MvPolynomial σ K) Ω ''
        Set.range (X : σ → MvPolynomial σ K) := by
    rw [← Set.range_comp]; rfl
  have hrange : (IsScalarTower.toAlgHom K (MvPolynomial σ K) Ω).range =
      Algebra.adjoin K
        (Set.range fun i : σ ↦ algebraMap (MvPolynomial σ K) Ω (X i)) := by
    rw [himage, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
  have h := IsFractionRing.algHom_fieldRange_eq_of_comp_eq_of_range_eq
    (g := IsScalarTower.toAlgHom K (MvPolynomial σ K) Ω) (f := AlgHom.id K Ω)
    (by ext <;> rfl) hrange
  rw [AlgHom.fieldRange_eq_top.mpr fun y ↦ ⟨y, rfl⟩] at h
  exact h.symm

end FunctionField

/-- **The function field of the universal divisor over a chart is geometrically irreducible over
the field generated by the parameters.** Let `A` be a domain of finite type over a field `k`
with fraction field `K`, let `n ≥ 2` and let `g₁, …, gₙ ∈ A` be such that the common zero locus
of `g₁` and `g₂` has an irreducible component of codimension two in `Spec A`. Let `Ω` be a
fraction field of `K[x₁, …, xₙ]`. If `K` is geometrically irreducible over `k`, then `Ω` is
geometrically irreducible over the subfield generated over `k` by the variables `x₁, …, xₙ` and
by `ξ = ∑ᵢ gᵢxᵢ`. -/
theorem isGeometricallyIrreducible_chartFunctionField
    (k A K Ω : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K]
    [IsScalarTower k A K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) K) Ω]
    [IsScalarTower K (MvPolynomial (Fin n) K) Ω]
    [IsFractionRing (MvPolynomial (Fin n) K) Ω]
    (hn : 2 ≤ n) (hK : Algebra.IsGeometricallyIrreducible k K) (g : Fin n → A)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {g ⟨0, by omega⟩, g ⟨1, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    let x : Fin n → Ω := fun i => algebraMap (MvPolynomial (Fin n) K) Ω (X i)
    let ξ : Ω := ∑ i, algebraMap K Ω (algebraMap A K (g i)) * x i
    let F : IntermediateField k Ω := IntermediateField.adjoin k (Set.range x ∪ {ξ})
    letI : Algebra F Ω := F.toSubalgebra.toAlgebra
    Algebra.IsGeometricallyIrreducible F Ω :=
  isGeometricallyIrreducible_adjoin_linearCombination_of_codimTwo k A K Ω hn _
    (adjoin_range_algebraMap_X_eq_top K Ω) (algebraicIndependent_algebraMap_X K Ω) hK g hcodim

/-! ### The chart's own coordinates -/

section ChartCoordinates

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- **The variables of a chart presented over its own ring of functions.** If `Ω` is a fraction
field of `A[x₁, …, xₙ]`, for `A` a domain with fraction field `K`, then the images of the
variables in `Ω` are algebraically independent over `K` and generate `Ω` over `K` as a field.
The hypothesis `hcompat` says that the two maps `A → K → Ω` and `A → A[x₁, …, xₙ] → Ω`
agree. -/
theorem algebraicIndependent_and_adjoin_eq_top_of_isFractionRing
    (A K Ω : Type u) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Ω] [Algebra K Ω] {n : ℕ} [Algebra (MvPolynomial (Fin n) A) Ω]
    [IsFractionRing (MvPolynomial (Fin n) A) Ω]
    (hcompat : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      algebraMap (MvPolynomial (Fin n) A) Ω (C a)) :
    AlgebraicIndependent K (fun i : Fin n => algebraMap (MvPolynomial (Fin n) A) Ω (X i)) ∧
      IntermediateField.adjoin K
        (Set.range fun i : Fin n => algebraMap (MvPolynomial (Fin n) A) Ω (X i)) = ⊤ := by
  set x : Fin n → Ω := fun i ↦ algebraMap (MvPolynomial (Fin n) A) Ω (X i)
  let ψ : MvPolynomial (Fin n) K →ₐ[K] Ω := MvPolynomial.aeval x
  let : Algebra (MvPolynomial (Fin n) K) Ω := ψ.toRingHom.toAlgebra
  have halg : algebraMap (MvPolynomial (Fin n) K) Ω = ψ.toRingHom := rfl
  have : IsScalarTower K (MvPolynomial (Fin n) K) Ω :=
    .of_algebraMap_eq fun a ↦ (ψ.commutes a).symm
  have : IsScalarTower (MvPolynomial (Fin n) A) (MvPolynomial (Fin n) K) Ω := by
    refine .of_algebraMap_eq' (MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_))
    · rw [halg]
      change algebraMap (MvPolynomial (Fin n) A) Ω (C a) =
        ψ (MvPolynomial.map (algebraMap A K) (C a))
      rw [map_C]
      change _ = ψ (algebraMap K (MvPolynomial (Fin n) K) (algebraMap A K a))
      rw [ψ.commutes]
      exact (hcompat a).symm
    · rw [halg]
      change algebraMap (MvPolynomial (Fin n) A) Ω (X i) =
        ψ (MvPolynomial.map (algebraMap A K) (X i))
      rw [map_X]
      exact (MvPolynomial.aeval_X x i).symm
  have : IsLocalization ((nonZeroDivisors A).map (C (σ := Fin n))) (MvPolynomial (Fin n) K) :=
    MvPolynomial.isLocalization _ _
  have : IsFractionRing (MvPolynomial (Fin n) K) Ω :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      ((nonZeroDivisors A).map (C (σ := Fin n))) (MvPolynomial (Fin n) K) Ω
  have hxeq : (fun i : Fin n ↦ algebraMap (MvPolynomial (Fin n) K) Ω (X i)) = x :=
    funext (MvPolynomial.aeval_X x)
  rw [← hxeq]
  exact ⟨algebraicIndependent_algebraMap_X K Ω, adjoin_range_algebraMap_X_eq_top K Ω⟩

/-- **The function field of the universal divisor over a chart, in the chart's own
coordinates.** Same statement as `Algebra.isGeometricallyIrreducible_chartFunctionField`, but
with `Ω` presented as a fraction field of the integral chart ring `A[x₁, …, xₙ]` rather than of
its base change `K[x₁, …, xₙ]`; the variables `x₁, …, xₙ` are then the images of the
coordinates of the chart itself. The hypothesis `hcompat` says that the two maps `A → K → Ω`
and `A → A[x₁, …, xₙ] → Ω` agree. -/
theorem isGeometricallyIrreducible_chartFunctionField_of_isFractionRing
    (k A K Ω : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K]
    [IsScalarTower k A K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {n : ℕ} [Algebra (MvPolynomial (Fin n) A) Ω] [IsFractionRing (MvPolynomial (Fin n) A) Ω]
    (hcompat : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      algebraMap (MvPolynomial (Fin n) A) Ω (C a))
    (hn : 2 ≤ n) (hK : Algebra.IsGeometricallyIrreducible k K) (g : Fin n → A)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {g ⟨0, by omega⟩, g ⟨1, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    let x : Fin n → Ω := fun i => algebraMap (MvPolynomial (Fin n) A) Ω (X i)
    let ξ : Ω := ∑ i, algebraMap K Ω (algebraMap A K (g i)) * x i
    let F : IntermediateField k Ω := IntermediateField.adjoin k (Set.range x ∪ {ξ})
    letI : Algebra F Ω := F.toSubalgebra.toAlgebra
    Algebra.IsGeometricallyIrreducible F Ω := by
  intro x
  obtain ⟨hind, hgen⟩ := algebraicIndependent_and_adjoin_eq_top_of_isFractionRing A K Ω hcompat
  exact isGeometricallyIrreducible_adjoin_linearCombination_of_codimTwo k A K Ω hn x hgen hind
    hK g hcodim

/-- Multiplying a pair of generators by a unit, and negating, does not change the ideal they
generate. -/
private theorem span_pair_neg_mul {R : Type u} [CommRing R] {u v : R} (huv : u * v = 1)
    (a b : R) : Ideal.span {-(u * a), -(u * b)} = Ideal.span ({a, b} : Set R) := by
  have hgen (c : R) (hc : -(u * c) ∈ Ideal.span ({-(u * a), -(u * b)} : Set R)) :
      c ∈ Ideal.span ({-(u * a), -(u * b)} : Set R) := by
    have key : -v * -(u * c) = c := by rw [neg_mul_neg, ← mul_assoc, mul_comm v u, huv, one_mul]
    simpa only [key] using Ideal.mul_mem_left _ (-v) hc
  refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_le.mpr ?_)
  · rintro _ (rfl | rfl) <;> exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  · rintro _ (rfl | rfl) <;> exact hgen _ (Ideal.subset_span (by simp))

/-- The codimension-two hypothesis on `f₁, f₂` transfers to `-(u f₁), -(u f₂)` for `u` an inverse
of `f₀`. -/
private theorem codim_two_neg_mul {A : Type u} [CommRing A] {n : ℕ} (hn : 2 ≤ n)
    (f : Fin (n + 1) → A) {u : A} (hu : u * f 0 = 1)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {f ⟨1, by omega⟩, f ⟨2, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    ∃ p : Ideal A,
      p ∈ (Ideal.span {-(u * f (Fin.succ ⟨0, by omega⟩)),
        -(u * f (Fin.succ ⟨1, by omega⟩))}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A := by
  rwa [span_pair_neg_mul hu]

/-- The ring map `A[x₀, …, xₙ] → Ω` of a chart of the universal divisor into a fraction field
`Ω` of its ring: the quotient map followed by the inclusion of the chart ring in `Ω`. -/
noncomputable def universalDivisorChartMap (A Ω : Type u) [CommRing A] [CommRing Ω]
    {σ : Type*} [Fintype σ] (f : σ → A)
    [Algebra (MvPolynomial σ A ⧸ Ideal.span {universalLinearForm f}) Ω] :
    MvPolynomial σ A →+* Ω :=
  (algebraMap (MvPolynomial σ A ⧸ Ideal.span {universalLinearForm f}) Ω).comp
    (Ideal.Quotient.mk (Ideal.span {universalLinearForm f}))

/-- The images of the chart's coordinates are the images of `x₁, …, xₙ` together with the image
of the coordinate `x₀` that the universal linear form eliminates. -/
theorem range_universalDivisorChartMap_X {A Ω : Type u} [CommRing A] [CommRing Ω] {n : ℕ}
    (f : Fin (n + 1) → A)
    [Algebra (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω] :
    (Set.range fun j : Fin (n + 1) => universalDivisorChartMap A Ω f (X j)) =
      (Set.range fun i : Fin n => universalDivisorChartMap A Ω f (X i.succ)) ∪
        {universalDivisorChartMap A Ω f (X 0)} := by
  ext z
  simp only [Set.mem_range, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    exact Fin.cases (Or.inr rfl) (fun i ↦ Or.inl ⟨i, rfl⟩) j
  · rintro (⟨i, rfl⟩ | rfl)
    · exact ⟨i.succ, rfl⟩
    · exact ⟨0, rfl⟩

/-- **The chart's own coordinates after eliminating `x₀`.** Let `Ω` be a fraction field of the
chart ring `A[x₀, …, xₙ]/(x₀f₀ + ⋯ + xₙfₙ)`, with `A` a domain with fraction field `K` and `f₀`
invertible. Then the images of `x₁, …, xₙ` in `Ω` are algebraically independent over `K` and
generate `Ω` over `K` as a field, and the image of the eliminated coordinate `x₀` is the linear
combination `∑ᵢ -(u fᵢ₊₁) xᵢ₊₁` of the others, for `u` an inverse of `f₀`. -/
private theorem universalDivisorChart_eliminateFirst (A K Ω : Type u) [CommRing A] [IsDomain A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Field Ω] [Algebra K Ω]
    {n : ℕ} (f : Fin (n + 1) → A) {u : A} (hu : u * f 0 = 1)
    [Algebra (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    [IsFractionRing (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    (hcompat : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      universalDivisorChartMap A Ω f (C a)) :
    AlgebraicIndependent K (fun i : Fin n => universalDivisorChartMap A Ω f (X i.succ)) ∧
      IntermediateField.adjoin K
          (Set.range fun i : Fin n => universalDivisorChartMap A Ω f (X i.succ)) = ⊤ ∧
      universalDivisorChartMap A Ω f (X 0) =
        ∑ i : Fin n, algebraMap K Ω (algebraMap A K (-(u * f i.succ))) *
          universalDivisorChartMap A Ω f (X i.succ) := by
  set e := quotientSpanUniversalLinearFormEquiv f hu with he
  let : Algebra (MvPolynomial (Fin n) A) Ω :=
    ((algebraMap (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω).comp
      e.toRingEquiv.symm.toRingHom).toAlgebra
  have : IsFractionRing (MvPolynomial (Fin n) A) Ω :=
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv Ω e.toRingEquiv).mp inferInstance
  have hπ : ∀ p : MvPolynomial (Fin n) A,
      algebraMap (MvPolynomial (Fin n) A) Ω p =
        universalDivisorChartMap A Ω f (rename Fin.succ p) := fun _ ↦ rfl
  have hπC : ∀ a : A, universalDivisorChartMap A Ω f (C a) =
      algebraMap K Ω (algebraMap A K a) := fun a ↦ (hcompat a).symm
  have hxeq : (fun i : Fin n ↦ algebraMap (MvPolynomial (Fin n) A) Ω (X i)) =
      fun i : Fin n ↦ universalDivisorChartMap A Ω f (X i.succ) := by
    funext i
    simpa using hπ (X i)
  have hcompat' : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      algebraMap (MvPolynomial (Fin n) A) Ω (C a) := by
    intro a
    rw [hπ (C a), rename_C, hπC]
  obtain ⟨hind, hgen⟩ := algebraicIndependent_and_adjoin_eq_top_of_isFractionRing A K Ω hcompat'
  rw [hxeq] at hind hgen
  refine ⟨hind, hgen, ?_⟩
  have hrel : Ideal.Quotient.mk (Ideal.span {universalLinearForm f}) (X 0) =
      Ideal.Quotient.mk (Ideal.span {universalLinearForm f})
        (-∑ i : Fin n, C (u * f i.succ) * X i.succ) := by
    rw [Ideal.Quotient.eq]
    have hdiff : X (0 : Fin (n + 1)) - -∑ i : Fin n, C (u * f i.succ) * X i.succ =
        C u * universalLinearForm f := by
      rw [← X_zero_add_sum_eq_C_mul_universalLinearForm f hu]; ring
    rw [hdiff]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  have hstep : universalDivisorChartMap A Ω f (X 0) =
      universalDivisorChartMap A Ω f (-∑ i : Fin n, C (u * f i.succ) * X i.succ) :=
    congrArg (algebraMap _ Ω) hrel
  rw [hstep, map_neg, map_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, ← neg_mul]
  congr 1
  rw [← hπC, map_neg, map_neg]

/-- **The function field of the universal divisor over a trivializing chart is geometrically
irreducible over the field generated by the parameters.**

Let `A` be a domain of finite type over a field `k` with fraction field `K` geometrically
irreducible over `k`, let `n ≥ 2` and let `f₀, …, fₙ ∈ A` with `f₀` invertible. If the common
zero locus of `f₁` and `f₂` has an irreducible component of codimension two in `Spec A`, then a
fraction field `Ω` of the chart ring `A[x₀, …, xₙ]/(x₀f₀ + ⋯ + xₙfₙ)` of the universal divisor
is geometrically irreducible over the subfield generated over `k` by the images of the
coordinates `x₀, …, xₙ`. The hypothesis `hcompat` says that the two maps `A → K → Ω` and
`A → A[x₀, …, xₙ] → Ω` agree. -/
@[stacks 0G4F "the generic fibre over a trivializing affine chart, in field-theoretic form"]
theorem isGeometricallyIrreducible_universalDivisorChart
    (k A K Ω : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K]
    [IsScalarTower k A K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {n : ℕ} (hn : 2 ≤ n) (f : Fin (n + 1) → A) {u : A} (hu : u * f 0 = 1)
    [Algebra (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    [IsFractionRing (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    (hcompat : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      universalDivisorChartMap A Ω f (C a))
    (hK : Algebra.IsGeometricallyIrreducible k K)
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {f ⟨1, by omega⟩, f ⟨2, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    letI F : IntermediateField k Ω :=
      IntermediateField.adjoin k
        (Set.range fun j : Fin (n + 1) => universalDivisorChartMap A Ω f (X j))
    letI : Algebra F Ω := F.toSubalgebra.toAlgebra
    Algebra.IsGeometricallyIrreducible F Ω := by
  obtain ⟨hind, hgen, hX0⟩ := universalDivisorChart_eliminateFirst A K Ω f hu hcompat
  set g : Fin n → A := fun i ↦ -(u * f i.succ)
  have hgcodim := codim_two_neg_mul hn f hu hcodim
  rw [range_universalDivisorChartMap_X f, hX0]
  exact isGeometricallyIrreducible_adjoin_linearCombination_of_codimTwo k A K Ω hn _ hgen hind
    hK g hgcodim

/-- **The parameters of the chart are algebraically independent over the base field.** In the
situation of `Algebra.isGeometricallyIrreducible_universalDivisorChart` the `n + 1` images of the
coordinates `x₀, …, xₙ` in a fraction field `Ω` of the chart ring
`A[x₀, …, xₙ]/(x₀f₀ + ⋯ + xₙfₙ)` are algebraically independent over `k`; equivalently, the
polynomial ring `k[x₀, …, xₙ]` injects into `Ω`. -/
@[stacks 0G4F "the dominance over the parameter space, read on a trivializing affine chart"]
theorem algebraicIndependent_universalDivisorChartMap_X
    (k A K Ω : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] [Algebra k K]
    [IsScalarTower k A K] [Field Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    {n : ℕ} (hn : 2 ≤ n) (f : Fin (n + 1) → A) {u : A} (hu : u * f 0 = 1)
    [Algebra (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    [IsFractionRing (MvPolynomial (Fin (n + 1)) A ⧸ Ideal.span {universalLinearForm f}) Ω]
    (hcompat : ∀ a : A, algebraMap K Ω (algebraMap A K a) =
      universalDivisorChartMap A Ω f (C a))
    (hcodim : ∃ p : Ideal A,
      p ∈ (Ideal.span {f ⟨1, by omega⟩, f ⟨2, by omega⟩}).minimalPrimes ∧
        ringKrullDim (A ⧸ p) + 2 = ringKrullDim A) :
    AlgebraicIndependent k fun j : Fin (n + 1) => universalDivisorChartMap A Ω f (X j) := by
  obtain ⟨hind, -, hX0⟩ := universalDivisorChart_eliminateFirst A K Ω f hu hcompat
  set g : Fin n → A := fun i ↦ -(u * f i.succ)
  have hgcodim := codim_two_neg_mul hn f hu hcodim
  have hbase := algebraicIndependent_linearCombination_of_codimTwo k A K Ω hn
    (fun i : Fin n ↦ universalDivisorChartMap A Ω f (X i.succ)) hind g hgcodim
  have hφ : Function.Injective fun j : Fin (n + 1) ↦
      (Fin.cases (Sum.inr ()) Sum.inl j : Fin n ⊕ Unit) :=
    Function.LeftInverse.injective
      (g := Sum.elim Fin.succ fun _ : Unit ↦ (0 : Fin (n + 1)))
      fun j ↦ Fin.cases rfl (fun _ ↦ rfl) j
  convert hbase.comp _ hφ using 1
  funext j
  exact Fin.cases hX0 (fun _ ↦ rfl) j

end ChartCoordinates

end Algebra

end
