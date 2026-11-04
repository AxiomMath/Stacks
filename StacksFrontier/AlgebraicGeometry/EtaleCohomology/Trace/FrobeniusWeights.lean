module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import StacksCore.Tactic.StacksAttribute

/-!
# Weights of the Frobenius action on compactly supported cohomology

Let `X` be a variety over a finite field with `q` elements and let `ℱ_ρ` be the lisse sheaf
attached to a continuous representation `ρ` of `π_1(X, x̄)` whose local Frobenius eigenvalues
are of absolute value `1`.  Weil II describes the eigenvalues of the geometric Frobenius
`π_X^*` on `H^i_c(X_k̄, ℱ_ρ)`: they are algebraic numbers `α` with `|α| = q ^ (w / 2)` for an
integer `w ≤ i`, and `w = i` when `X` is smooth and projective.

This module introduces the `q`-Weil numbers of weight `w` and the mixed and pure Frobenius
actions they measure, and proves the two implications that statement rests on: mixedness of
weight at most `i` propagates along the excision sequence of an open-closed decomposition of
`X`, and Poincaré duality upgrades mixedness in degree `i` to purity of weight exactly `i`.

## Main definitions

* `Stacks.EtaleCohomology.IsWeilNumber`: a `q`-Weil number of weight `w`, an algebraic number
  of complex absolute value `q ^ (w / 2)`.
* `Stacks.EtaleCohomology.IsMixedOfWeightLE` and `Stacks.EtaleCohomology.IsPureOfWeight`: the
  eigenvalues of an endomorphism are `q`-Weil numbers of some weight at most `i`, resp. of
  weight exactly `w`.

## Main results

* `Stacks.EtaleCohomology.IsWeilNumber.weight_unique`: for `1 < q` the weight of a `q`-Weil
  number is unique.
* `Stacks.EtaleCohomology.IsWeilNumber.zpow_div`: the dual `q ^ d / α` of a `q`-Weil number of
  weight `w` is a `q`-Weil number of weight `2 * d - w`.
* `Stacks.EtaleCohomology.hasEigenvalue_or_of_exact`: an eigenvalue of the middle term of an
  exact sequence of equivariant maps is an eigenvalue of one of the outer terms; hence
  `Stacks.EtaleCohomology.IsMixedOfWeightLE.of_exact`, mixedness of weight at most `i`
  propagates to the middle term.
* `Stacks.EtaleCohomology.isPureOfWeight_of_duality`: mixedness in degree `i` and in the dual
  degree `2 * d - i`, together with the duality matching of the two spectra, give purity of
  weight `i`.

## Implementation notes

The coefficient field `K` of the cohomology — `ℚ_ℓ` in the source — is arbitrary, and the
complex absolute value of an eigenvalue is taken along a ring homomorphism `ι : K →+* ℂ`,
which is how the source reads the eigenvalues, a priori `ℓ`-adic, as complex algebraic
numbers.

The cohomology itself is not constructed here: as elsewhere in this chapter the Frobenius
action is data, an endomorphism of a finite-dimensional vector space.  The excision sequence
of an open-closed decomposition `X = U ⊔ Z`, the long exact cohomology sequence of the short
exact sequence `0 → j_! j^{-1}ℱ → ℱ → i_* i^{-1}ℱ → 0` of
[Tag 095L](https://stacks.math.columbia.edu/tag/095L), enters as the equivariance and
exactness hypotheses, and the Poincaré duality pairing of `H^i_c(X_k̄, ℱ_ρ)` with the
cohomology of the dual sheaf in degree `2 * dim X - i` enters as the matching of the two
spectra.  The hypotheses on `ρ` of the conjecture preceding the theorem in the source enter
only through the weight data, exactly as they do there.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH), the theorem of
  Deligne whose proof there is the citation [WeilII]; the weight data of that citation is
  carried here as the mixedness hypotheses.
-/

@[expose] public noncomputable section

namespace Stacks.EtaleCohomology

/-! ### Weil numbers -/

/-- A `q`-Weil number of weight `w`: an algebraic number whose complex absolute value is
`q ^ (w / 2)`. -/
public structure IsWeilNumber (q : ℕ) (w : ℤ) (α : ℂ) : Prop where
  /-- A Weil number is an algebraic number. -/
  isAlgebraic : IsAlgebraic ℚ α
  /-- A `q`-Weil number of weight `w` has complex absolute value `q ^ (w / 2)`. -/
  norm_eq : ‖α‖ = (q : ℝ) ^ ((w : ℝ) / 2)

namespace IsWeilNumber

variable {q : ℕ} {w w' : ℤ} {α : ℂ}

/-- A `q`-Weil number for positive `q` has positive absolute value. -/
public theorem norm_pos (h : IsWeilNumber q w α) (hq : 0 < q) : 0 < ‖α‖ := by
  rw [h.norm_eq]
  exact Real.rpow_pos_of_pos (Nat.cast_pos.2 hq) _

/-- A `q`-Weil number for positive `q` is nonzero. -/
public theorem ne_zero (h : IsWeilNumber q w α) (hq : 0 < q) : α ≠ 0 := by
  intro h0
  have h1 := h.norm_pos hq
  rw [h0, norm_zero] at h1
  exact lt_irrefl 0 h1

/-- The weight of a `q`-Weil number is unique as soon as `1 < q`. -/
public theorem weight_unique (h : IsWeilNumber q w α) (h' : IsWeilNumber q w' α) (hq : 1 < q) :
    w = w' := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have heq := h.norm_eq.symm.trans h'.norm_eq
  have h2 : ((w : ℝ) / 2) = ((w' : ℝ) / 2) :=
    (Real.rpow_right_inj (by linarith) (ne_of_gt hq1)).1 heq
  have h3 : (w : ℝ) = (w' : ℝ) := by linarith
  exact_mod_cast h3

/-- The number `q ^ d / α` dual to a `q`-Weil number `α` of weight `w` is a `q`-Weil number of
weight `2 * d - w`. -/
public theorem zpow_div (h : IsWeilNumber q w α) (hq : 0 < q) (d : ℤ) :
    IsWeilNumber q (2 * d - w) ((q : ℂ) ^ d / α) where
  isAlgebraic := by
    have halg : IsAlgebraic ℚ ((q : ℂ) ^ d) := by
      have hcast : ((q : ℂ) ^ d) = (((q : ℚ) ^ d : ℚ) : ℂ) := by push_cast; rfl
      rw [hcast]
      exact isAlgebraic_ratCast ℚ _
    rw [div_eq_mul_inv]
    exact halg.mul h.isAlgebraic.inv
  norm_eq := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 hq
    rw [norm_div, norm_zpow, Complex.norm_natCast, h.norm_eq, ← Real.rpow_intCast (q : ℝ) d,
      ← Real.rpow_sub hq0]
    congr 1
    push_cast
    ring

end IsWeilNumber

/-! ### Mixed and pure Frobenius actions -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- An endomorphism `f` is mixed of weight at most `i`, relative to `q` and to an embedding `ι`
of the coefficient field in `ℂ`, when each of its eigenvalues is a `q`-Weil number of some
integer weight at most `i`. -/
public def IsMixedOfWeightLE (q : ℕ) (ι : K →+* ℂ) (i : ℤ) (f : Module.End K V) : Prop :=
  ∀ α : K, f.HasEigenvalue α → ∃ w ≤ i, IsWeilNumber q w (ι α)

/-- An endomorphism `f` is pure of weight `w`, relative to `q` and to an embedding `ι` of the
coefficient field in `ℂ`, when each of its eigenvalues is a `q`-Weil number of weight `w`. -/
public def IsPureOfWeight (q : ℕ) (ι : K →+* ℂ) (w : ℤ) (f : Module.End K V) : Prop :=
  ∀ α : K, f.HasEigenvalue α → IsWeilNumber q w (ι α)

variable {q : ℕ} {ι : K →+* ℂ} {i i' : ℤ} {f : Module.End K V}

/-- Raising the bound preserves mixedness. -/
public theorem IsMixedOfWeightLE.mono (h : IsMixedOfWeightLE q ι i f) (hi : i ≤ i') :
    IsMixedOfWeightLE q ι i' f := fun α hα =>
  let ⟨w, hw, hwα⟩ := h α hα
  ⟨w, hw.trans hi, hwα⟩

/-- An action pure of weight at most `i` is mixed of weight at most `i`. -/
public theorem IsPureOfWeight.isMixedOfWeightLE {w : ℤ} (h : IsPureOfWeight q ι w f)
    (hw : w ≤ i) : IsMixedOfWeightLE q ι i f := fun α hα => ⟨w, hw, h α hα⟩

/-! ### Eigenvalues along an exact sequence -/

/-- In finite dimension, `α` is an eigenvalue of `g` iff `g - α • 1` is not surjective. -/
private theorem hasEigenvalue_iff_not_surjective [FiniteDimensional K W] (g : Module.End K W)
    (α : K) : g.HasEigenvalue α ↔ ¬ Function.Surjective (g - α • (1 : Module.End K W)) := by
  rw [Module.End.hasEigenvalue_iff, Module.End.eigenspace_def, ← LinearMap.injective_iff_surjective,
    ← LinearMap.ker_eq_bot]

/-- An eigenvalue of an equivariant quotient is an eigenvalue of the original: if `σ` is
surjective and intertwines `f` and `g`, then every eigenvalue of `g` is one of `f`. -/
public theorem hasEigenvalue_of_surjective [FiniteDimensional K V] [FiniteDimensional K W]
    {g : Module.End K W} {σ : V →ₗ[K] W} (hσ : Function.Surjective σ)
    (hcomm : ∀ v, σ (f v) = g (σ v)) {α : K} (hα : g.HasEigenvalue α) : f.HasEigenvalue α := by
  rw [hasEigenvalue_iff_not_surjective] at hα ⊢
  intro hsurjf
  refine hα fun y => ?_
  obtain ⟨x, rfl⟩ := hσ y
  obtain ⟨u, hu⟩ := hsurjf x
  refine ⟨σ u, ?_⟩
  have hmap : σ ((f - α • (1 : Module.End K V)) u) = (g - α • (1 : Module.End K W)) (σ u) := by
    simp [hcomm]
  rw [← hmap, hu]

/-- Eigenvalues in an exact sequence: if `j` and `p` intertwine the endomorphisms `fA`, `fB`,
`fC` and the sequence `A → B → C` is exact at `B`, then every eigenvalue of `fB` is an
eigenvalue of `fA` or of `fC`. -/
public theorem hasEigenvalue_or_of_exact {A B C : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C] [FiniteDimensional K A]
    [FiniteDimensional K B] {fA : Module.End K A} {fB : Module.End K B} {fC : Module.End K C}
    {j : A →ₗ[K] B} {p : B →ₗ[K] C} (hj : ∀ a, j (fA a) = fB (j a))
    (hp : ∀ b, p (fB b) = fC (p b)) (hexact : LinearMap.ker p ≤ LinearMap.range j) {α : K}
    (hα : fB.HasEigenvalue α) : fA.HasEigenvalue α ∨ fC.HasEigenvalue α := by
  by_cases hC : fC.HasEigenvalue α
  · exact Or.inr hC
  refine Or.inl ?_
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hfv : fB v = α • v := hv.apply_eq_smul
  have hpv : p v = 0 := by
    by_contra h
    refine hC (Module.End.hasEigenvalue_of_hasEigenvector (x := p v) ⟨?_, h⟩)
    rw [Module.End.mem_eigenspace_iff, ← hp, hfv, map_smul]
  have hmaps : ∀ x ∈ LinearMap.range j, fB x ∈ LinearMap.range j := by
    rintro x ⟨a, rfl⟩
    exact ⟨fA a, hj a⟩
  have hvmem : v ∈ LinearMap.range j := hexact (LinearMap.mem_ker.2 hpv)
  have hres : Module.End.HasEigenvalue (fB.restrict hmaps) α := by
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨v, hvmem⟩) ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      exact Subtype.ext (by simpa [LinearMap.coe_restrict_apply] using hfv)
    · simpa [Subtype.ext_iff] using hv0
  have hequiv : ∀ a, j.rangeRestrict (fA a) = (fB.restrict hmaps) (j.rangeRestrict a) :=
    fun a => Subtype.ext (by simpa [LinearMap.coe_restrict_apply] using hj a)
  exact hasEigenvalue_of_surjective (g := fB.restrict hmaps) j.surjective_rangeRestrict hequiv hres

/-! ### The weight statement of Weil II -/

/-- Mixedness of weight at most `i` propagates along an exact sequence: in the excision
sequence `H^i_c(U) → H^i_c(X) → H^i_c(Z)` of an open-closed decomposition `X = U ⊔ Z`, if the
Frobenius actions on the two outer terms are mixed of weight at most `i`, then so is the
Frobenius action on `H^i_c(X)`, whose eigenvalues are therefore algebraic numbers of absolute
value `q ^ (w / 2)` with `w` an integer at most `i`. -/
@[stacks 03VH "the weight bound: the eigenvalues on H^i_c are algebraic numbers of absolute \
value q ^ (w / 2) with w an integer at most i. The weight datum is the cited theorem of \
[WeilII]; it is carried here for the two outer terms of the excision sequence of an \
open-closed decomposition of X and propagated to H^i_c(X)"]
public theorem IsMixedOfWeightLE.of_exact {A B C : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C] [FiniteDimensional K A]
    [FiniteDimensional K B] {fA : Module.End K A} {fB : Module.End K B} {fC : Module.End K C}
    {j : A →ₗ[K] B} {p : B →ₗ[K] C} (hA : IsMixedOfWeightLE q ι i fA)
    (hC : IsMixedOfWeightLE q ι i fC) (hj : ∀ a, j (fA a) = fB (j a))
    (hp : ∀ b, p (fB b) = fC (p b)) (hexact : LinearMap.ker p ≤ LinearMap.range j) :
    IsMixedOfWeightLE q ι i fB := fun α hα =>
  (hasEigenvalue_or_of_exact hj hp hexact hα).elim (hA α) (hC α)

/-- Poincaré duality turns mixedness into purity: if the Frobenius action `f` on `H^i_c` is
mixed of weight at most `i`, the action `g` on the cohomology of the dual sheaf in degree
`2 * d - i` is mixed of weight at most `2 * d - i`, and duality matches each eigenvalue `α` of
`f` with the eigenvalue `q ^ d / α` of `g`, then `f` is pure of weight `i`. -/
@[stacks 03VH "the final assertion, that w = i when X is smooth and projective of dimension \
d: proved from mixedness in degree i and in the dual degree 2 * d - i together with the \
Poincare duality matching of the two spectra"]
public theorem isPureOfWeight_of_duality {d : ℤ} {g : Module.End K W}
    (hf : IsMixedOfWeightLE q ι i f) (hg : IsMixedOfWeightLE q ι (2 * d - i) g)
    (hdual : ∀ α : K, f.HasEigenvalue α → g.HasEigenvalue ((q : K) ^ d / α)) (hq : 1 < q) :
    IsPureOfWeight q ι i f := by
  intro α hα
  obtain ⟨w, hwi, hw⟩ := hf α hα
  obtain ⟨w', hw'i, hw'⟩ := hg _ (hdual α hα)
  have hmap : ι ((q : K) ^ d / α) = (q : ℂ) ^ d / ι α := by
    rw [map_div₀, map_zpow₀, map_natCast]
  rw [hmap] at hw'
  have hdualwt : IsWeilNumber q (2 * d - w) ((q : ℂ) ^ d / ι α) :=
    hw.zpow_div (lt_trans zero_lt_one hq) d
  have hw'eq : w' = 2 * d - w := hw'.weight_unique hdualwt hq
  have hiw : i ≤ w := by omega
  have hweq : w = i := le_antisymm hwi hiw
  exact hweq ▸ hw

end Stacks.EtaleCohomology

end
