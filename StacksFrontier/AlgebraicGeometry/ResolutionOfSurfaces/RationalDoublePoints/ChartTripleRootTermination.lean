module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartCaseTwo
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.RationalDoublePointLevelStep
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.CaseDichotomy
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartPresentation
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.FormPolynomial
public import StacksFrontier.AlgebraicGeometry.Surfaces.BlowUpNormality

/-!
# Case II of a rational double point: runs of triple roots are short

Let `A` be the ring of a Situation 0BGC which is not in case I. Its maximal ideal has generators
`x₁, x₂, x₃` with `x₃² = Σ aₚᵩᵣ xₚxᵩxᵣ`, and a singular point of the blowup sits at a multiple root
of the cubic `c(t₁, t₂)` this relation restricts to on the double line `t₃ = 0`. At a double root
the point carries a unit-special coordinate (`AlgebraicGeometry.IsUnitSpecialCoordinate`), along
which the blowups then proceed with a fixed element. At a triple root it does not (`E₈ → E₇`), and
the tracked element changes. This happens at most twice in a row: among three successive singular
points over a ring which is not in case I, one is in case I or carries a unit-special coordinate.

## Main results

* `AlgebraicGeometry.isCaseOne_or_exists_of_sq_eq_mul`: the local analysis at a point of a chart,
  for a relation `w² = t·G` with `G ≡ H(v)` modulo `(t, w)` and `H` of degree at most three.
* `RationalDoublePointSituation.exists_isCaseOne_or_isUnitSpecialCoordinate_of_three_blowUps`:
  among three successive singular points over a ring not in case I, one is in case I or carries a
  unit-special coordinate.
* `AlgebraicGeometry.RationalDoublePointSituation.isUnitSpecialCoordinate_of_isSpecialCoordinate`:
  under the dimension formula, a special coordinate (`AlgebraicGeometry.IsSpecialCoordinate`) is
  unit-special.

## Implementation notes

At the first triple root the relation reads `w² = t(λv³ + t·a + w·b)` with `λ` a unit
(`AlgebraicGeometry.IsTripleRootData`). One blowup later `λ` is the coefficient of `v` in `a`
(`AlgebraicGeometry.IsTripleRootSecond`), which rules out a third triple root.

## References

* [Stacks Project, Tag 0BGE](https://stacks.math.columbia.edu/tag/0BGE)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u

namespace AlgebraicGeometry

section Defs

variable (B : Type u) [CommRing B] [IsLocalRing B]

/-- The shape at a triple root of the cubic on the double line: generators `t, v, w` of the
maximal ideal with `w² = t·(λv³ + t·a + w·b)`, `λ` a unit, `a = Σ αᵢxᵢ` and `b = Σ βᵢxᵢ`. -/
def IsTripleRootData : Prop :=
  ∃ (x : Fin 3 → B) (lam : B) (α β : Fin 3 → B), Ideal.span (Set.range x) = maximalIdeal B ∧
    lam ∉ maximalIdeal B ∧
    x 2 * x 2 = x 0 * (lam * x 1 ^ 3 + x 0 * ∑ i, α i * x i + x 2 * ∑ i, β i * x i)

/-- The shape at a second triple root in a row: `AlgebraicGeometry.IsTripleRootData` with the
coefficient `α₂` of `v` in `a` a unit. -/
def IsTripleRootSecond : Prop :=
  ∃ (x : Fin 3 → B) (lam : B) (α β : Fin 3 → B), Ideal.span (Set.range x) = maximalIdeal B ∧
    lam ∉ maximalIdeal B ∧ α 1 ∉ maximalIdeal B ∧
    x 2 * x 2 = x 0 * (lam * x 1 ^ 3 + x 0 * ∑ i, α i * x i + x 2 * ∑ i, β i * x i)

end Defs

/-! ### Transport along ring isomorphisms -/

section Transport

variable {B B' : Type*} [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']

/-- A ring isomorphism of local rings preserves membership in the maximal ideal. -/
theorem ringEquiv_mem_maximalIdeal_iff (e : B ≃+* B') {b : B} :
    e b ∈ maximalIdeal B' ↔ b ∈ maximalIdeal B := by
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_map_iff]

/-- A ring isomorphism of local rings maps `𝔪 ^ n` into `𝔪 ^ n`. -/
theorem ringEquiv_mem_maximalIdeal_pow (e : B ≃+* B') {b : B} {n : ℕ}
    (hb : b ∈ maximalIdeal B ^ n) :
    e b ∈ maximalIdeal B' ^ n := by
  rw [← map_ringEquiv_maximalIdeal e, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hb

/-- A ring isomorphism of local rings maps three generators of the maximal ideal to three
generators of the maximal ideal. -/
theorem ringEquiv_span_range (e : B ≃+* B') {x : Fin 3 → B}
    (hx : Ideal.span (Set.range x) = maximalIdeal B) :
    Ideal.span (Set.range fun i => e (x i)) = maximalIdeal B' := by
  rw [← map_ringEquiv_maximalIdeal e, ← hx, Ideal.map_span, ← Set.range_comp]
  rfl

/-- A unit-special coordinate is carried along a ring isomorphism. -/
theorem IsUnitSpecialCoordinate.of_ringEquiv (e : B ≃+* B') {c : B}
    (h : IsUnitSpecialCoordinate B c) :
    IsUnitSpecialCoordinate B' (e c) := by
  obtain ⟨x, q, hx0, hx, hq, hrel⟩ := h
  refine ⟨fun i => e (x i), fun i j => e (q i j), by simp only [hx0], ringEquiv_span_range e hx,
    (ringEquiv_mem_maximalIdeal_iff e).not.mpr hq, ?_⟩
  simpa only [map_add, map_mul, map_sum] using ringEquiv_mem_maximalIdeal_pow e hrel

/-- The shape `AlgebraicGeometry.IsTripleRootData` is carried along a ring isomorphism. -/
theorem IsTripleRootData.of_ringEquiv (e : B ≃+* B') (h : IsTripleRootData B) :
    IsTripleRootData B' := by
  obtain ⟨x, lam, α, β, hx, hlam, hrel⟩ := h
  refine ⟨fun i => e (x i), e lam, fun i => e (α i), fun i => e (β i), ringEquiv_span_range e hx,
    (ringEquiv_mem_maximalIdeal_iff e).not.mpr hlam, ?_⟩
  simpa only [map_add, map_mul, map_sum, map_pow] using congrArg e hrel

/-- The shape `AlgebraicGeometry.IsTripleRootSecond` is carried along a ring isomorphism. -/
theorem IsTripleRootSecond.of_ringEquiv (e : B ≃+* B') (h : IsTripleRootSecond B) :
    IsTripleRootSecond B' := by
  obtain ⟨x, lam, α, β, hx, hlam, hα, hrel⟩ := h
  refine ⟨fun i => e (x i), e lam, fun i => e (α i), fun i => e (β i), ringEquiv_span_range e hx,
    (ringEquiv_mem_maximalIdeal_iff e).not.mpr hlam,
    (ringEquiv_mem_maximalIdeal_iff e).not.mpr hα, ?_⟩
  simpa only [map_add, map_mul, map_sum, map_pow] using congrArg e hrel

end Transport

/-! ### Normality -/

/-- In a ring integrally closed in its total ring of fractions, `w² = t·(t·a + w·b)` with `t` a
nonzerodivisor forces `t ∣ w`: the fraction `w/t` is a root of `z² - bz - a`. -/
theorem mem_span_singleton_of_sq_eq_of_mem_nonZeroDivisors {C : Type*} [CommRing C]
    [IsIntegrallyClosed C] {t w a b : C} (ht : t ∈ nonZeroDivisors C)
    (h : w * w = t * (t * a + w * b)) : w ∈ Ideal.span {t} := by
  set K := FractionRing C
  have htK : IsUnit (algebraMap C K t) := IsLocalization.map_units K ⟨t, ht⟩
  set z := algebraMap C K w * ↑htK.unit⁻¹ with hz
  have hzt : z * algebraMap C K t = algebraMap C K w := by
    rw [hz, mul_assoc, htK.val_inv_mul, mul_one]
  have hint : _root_.IsIntegral C z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a, ?_, ?_⟩
    · have : (Polynomial.X ^ 2 - Polynomial.C b * Polynomial.X - Polynomial.C a :
          Polynomial C) = Polynomial.X ^ 2 - (Polynomial.C b * Polynomial.X + Polynomial.C a) := by
        ring
      rw [this]
      refine Polynomial.monic_X_pow_sub ?_
      compute_degree!
    · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Polynomial.eval₂_X]
      have h2 := congrArg (algebraMap C K) h
      simp only [map_mul, map_add] at h2
      apply (htK.pow 2).mul_left_injective
      simp only [zero_mul]
      linear_combination h2 + (z * algebraMap C K t + algebraMap C K w) * hzt -
        algebraMap C K b * algebraMap C K t * hzt
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  refine Ideal.mem_span_singleton'.mpr ⟨y, IsFractionRing.injective C K ?_⟩
  rw [map_mul, hy, hzt]

/-- In a normal domain, `w² = t·(t·a + w·b)` with `t ≠ 0` forces `t ∣ w`. -/
theorem mem_span_singleton_of_sq_eq {C : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
    {t w a b : C} (ht : t ≠ 0) (h : w * w = t * (t * a + w * b)) : w ∈ Ideal.span {t} :=
  mem_span_singleton_of_sq_eq_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht) h

/-! ### Completing the square at a triple root -/

/-- **Completing the square at a triple root.** If `t, v, w` generate the maximal ideal and
`w² = t(λv³ + t·a + w·b)` with `λ` a unit, then `C` is in case I or carries the shape
`AlgebraicGeometry.IsTripleRootData`. -/
theorem isCaseOne_or_isTripleRootData_of_cube {C : Type*} [CommRing C] [IsLocalRing C]
    {t v w lam a b : C} (hlam : lam ∉ maximalIdeal C) (ht : t ∈ maximalIdeal C)
    (hvm : v ∈ maximalIdeal C) (hwm : w ∈ maximalIdeal C)
    (hgen : maximalIdeal C = Ideal.span {t, v, w})
    (hrel : w * w = t * (lam * v ^ 3 + t * a + w * b)) :
    IsCaseOne C ∨ IsTripleRootData C := by
  set M : Fin 3 → Fin 3 → C := ![![-a, 0, -b], ![0, 0, 0], ![0, 0, 1]] with hM
  set X3 : Fin 3 → C := ![t, v, w] with hX3
  have hspan3 : Ideal.span (Set.range X3) = maximalIdeal C := by
    rw [range_fin_three]; exact hgen.symm
  have hrelI : ∑ p, ∑ r, M p r * (X3 p * X3 r) ∈ maximalIdeal C ^ 3 := by
    have : ∑ p, ∑ r, M p r * (X3 p * X3 r) = t * (lam * (v * (v * v))) := by
      simp only [hM, hX3, Fin.sum_univ_three]
      simp
      linear_combination hrel
    rw [this, pow_succ', pow_succ', pow_one]
    exact Ideal.mul_mem_mul ht (Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hvm
      (Ideal.mul_mem_left _ _ hvm)))
  by_cases hF : IsScalarSqLinear (fun p r => residue C (M p r))
  swap
  · left
    refine ⟨X3, M, hspan3, ?_, ⟨2, 2, le_rfl, ?_⟩, hrelI, hF⟩
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> simp [hM] at hpr ⊢
    · simp [hM]
  right
  obtain ⟨c', l, hd, ho⟩ := hF
  have hd0 := hd 0
  have hd2 := hd 2
  have ho02 := ho 0 2 (by decide)
  simp only [hM] at hd0 hd2 ho02
  simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
    map_neg, Matrix.cons_val, Matrix.cons_val_one, map_one, map_zero, add_zero] at hd0 hd2 ho02
  obtain ⟨lamb, hlamb⟩ := IsLocalRing.residue_surjective (c' * l 0 * l 2)
  set W := w + lamb * t with hW
  obtain ⟨a', ha'⟩ : ∃ a', a' = a - lamb * b - lamb ^ 2 := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = b + 2 * lamb := ⟨_, rfl⟩
  have ha'm : a' ∈ maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, ha']
    simp only [map_sub, map_mul, map_pow, hlamb]
    linear_combination (-1 : ResidueField C) * hd0 + (c' * l 0 * l 2) * ho02 -
      (c' * l 0 * l 0) * hd2
  have hb'm : b' ∈ maximalIdeal C := by
    rw [← IsLocalRing.residue_eq_zero_iff, hb']
    simp only [map_add, map_mul, map_ofNat, hlamb]
    linear_combination (-1 : ResidueField C) * ho02
  have hWm : W ∈ maximalIdeal C := add_mem hwm (Ideal.mul_mem_left _ _ ht)
  have hspanW : Ideal.span (Set.range ![t, v, W]) = maximalIdeal C := by
    rw [range_fin_three]
    refine le_antisymm (Ideal.span_le.mpr ?_) ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, Set.insert_subset_iff, Set.singleton_subset_iff,
        SetLike.mem_coe]
      exact ⟨ht, hvm, hWm⟩
    · rw [hgen, Ideal.span_le]
      simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
      refine ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp), ?_⟩
      rw [show w = W - lamb * t by rw [hW]; ring]
      exact sub_mem (Ideal.subset_span (by simp))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
  obtain ⟨ca, hca⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp
    (show a' ∈ Submodule.span C (Set.range ![t, v, W]) by rw [← Ideal.span, hspanW]; exact ha'm)
  obtain ⟨cb, hcb⟩ := (Submodule.mem_span_range_iff_exists_fun C).mp
    (show b' ∈ Submodule.span C (Set.range ![t, v, W]) by rw [← Ideal.span, hspanW]; exact hb'm)
  simp only [smul_eq_mul] at hca hcb
  refine ⟨![t, v, W], lam, ca, cb, hspanW, hlam, ?_⟩
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  rw [hca, hcb, ha', hb', hW]
  linear_combination hrel

/-! ### The local analysis at a point of a chart -/

section Core

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- **The local analysis at a point of a chart of the blowup of a case II singularity.** Let `C`
be a two-dimensional Noetherian normal local domain over `B` which is not regular, with
`w² = t·G`, `t ≠ 0`, `G ≡ H(v)` modulo `(t, w)` for a polynomial `H` over `B` whose reduction has
degree at most three, the image of the maximal ideal of `B` in `t·C`, and every element of `C`
a polynomial in `v` modulo `w` up to a unit. Then `C` is in case I, or the point sits at a root
`μ` of the reduction of `H`, the maximal ideal is generated by `t`, `v - μ` and `w`, and either
the root is exactly double and `t` is a unit-special coordinate, or the root is at least triple
and `C` is in case I or has the shape `AlgebraicGeometry.IsTripleRootData`. -/
theorem isCaseOne_or_exists_of_sq_eq_mul [IsNoetherianRing C] [IsDomain C] [IsIntegrallyClosed C]
    (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {t v w G : C} (ht0 : t ≠ 0) (ht : t ∈ maximalIdeal C)
    (hφm : ∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {t})
    (hrel : w * w = t * G) (H : B[X]) (hG : G - H.eval₂ φ v ∈ Ideal.span {t, w})
    (hdeg : (H.map (residue B)).natDegree ≤ 3)
    (hloc : ∀ c : C, ∃ (b : C) (P : B[X]), IsUnit b ∧ b * c - P.eval₂ φ v ∈ Ideal.span {w}) :
    IsCaseOne C ∨ ∃ μ : B, H.map (residue B) ≠ 0 ∧ maximalIdeal C = Ideal.span {t, v - φ μ, w} ∧
      (((Polynomial.X - Polynomial.C (residue B μ)) ^ 2 ∣ H.map (residue B) ∧
        ¬ (Polynomial.X - Polynomial.C (residue B μ)) ^ 3 ∣ H.map (residue B) ∧
        (IsCaseOne C ∨ IsUnitSpecialCoordinate C t)) ∨
      ((Polynomial.X - Polynomial.C (residue B μ)) ^ 3 ∣ H.map (residue B) ∧
        (IsCaseOne C ∨ IsTripleRootData C))) := by
  classical
  have hwm : w ∈ maximalIdeal C := by
    have hww : w * w ∈ maximalIdeal C := hrel ▸ Ideal.mul_mem_right _ _ ht
    exact ((IsLocalRing.maximalIdeal.isMaximal C).isPrime.mem_or_mem hww).elim id id
  set θ := residuePolyEval φ v with hθ
  obtain ⟨g, hg⟩ : ∃ g, RingHom.ker θ = Ideal.span {g} :=
    ⟨Submodule.IsPrincipal.generator (RingHom.ker θ), (Ideal.span_singleton_generator _).symm⟩
  obtain ⟨G', hG'⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective g
  have hgen := maximalIdeal_eq_span_of_ker φ ht hwm hφm hloc hg hG'
  have hHres : ∀ P : B[X], θ (P.map (residue B)) = residue C (P.eval₂ φ v) :=
    fun P => (residue_eval₂ φ v P).symm
  have hmem_ker : ∀ {g' : (ResidueField B)[X]}, RingHom.ker θ = Ideal.span {g'} →
      ∀ P, θ P = 0 → g' ∣ P := fun hg' P hP => by
    rw [← Ideal.mem_span_singleton, ← hg']
    exact hP
  obtain ⟨a₀, b₀, hab⟩ := Ideal.mem_span_pair.mp hG
  have hGe : G = H.eval₂ φ v + t * a₀ + w * b₀ := by linear_combination -hab
  set h := H.map (residue B) with hh
  have hlift : ∀ P : B[X], P.map (residue B) = 0 → ∃ s, P.eval₂ φ v = t * s := fun P hP => by
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (eval₂_mem_of_map_residue_eq_zero φ hφm v hP)
    exact ⟨s, by rw [← hs, mul_comm]⟩
  by_cases hh0 : h = 0
  · exfalso
    obtain ⟨s, hs⟩ := hlift H hh0
    have hw : w ∈ Ideal.span {t} := mem_span_singleton_of_sq_eq ht0
      (a := s + a₀) (b := b₀) (by rw [hrel, hGe, hs]; ring)
    apply hsing
    refine isRegularLocalRing_of_maximalIdeal_eq_span_pair hdimC (u := t) (v := G'.eval₂ φ v) ?_
    rw [hgen]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono (by simp [Set.insert_subset_iff]))
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Ideal.subset_span (by simp), Ideal.subset_span (by simp), Ideal.span_mono (by simp) hw⟩
  by_cases hdiv : g ∣ h
  swap
  · exfalso
    have hHu : H.eval₂ φ v ∉ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hHres]
      exact fun h0 => hdiv (hmem_ker hg _ h0)
    have hu : IsUnit G := by
      refine IsLocalRing.notMem_maximalIdeal.mp fun hm => hHu ?_
      have : H.eval₂ φ v = G - (t * a₀ + w * b₀) := by rw [hGe]; ring
      rw [this]
      exact sub_mem hm (add_mem (Ideal.mul_mem_right _ _ ht) (Ideal.mul_mem_right _ _ hwm))
    have htw : t ∈ Ideal.span {w} := Ideal.mem_span_singleton'.mpr ⟨w * ↑hu.unit⁻¹, by
      rw [mul_right_comm, hrel, mul_assoc, hu.mul_val_inv, mul_one]⟩
    apply hsing
    refine isRegularLocalRing_of_maximalIdeal_eq_span_pair hdimC
      (u := G'.eval₂ φ v) (v := w) ?_
    rw [hgen]
    refine le_antisymm (Ideal.span_le.mpr ?_) (Ideal.span_mono (by simp))
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact ⟨Ideal.span_mono (by simp) htw, Ideal.subset_span (by simp), Ideal.subset_span (by simp)⟩
  obtain ⟨k, hk⟩ := hdiv
  by_cases hdiv2 : g * g ∣ h
  swap
  · left
    have hgk : ¬ g ∣ k := fun ⟨k', hk'⟩ => hdiv2 ⟨k', by rw [hk, hk', mul_assoc]⟩
    obtain ⟨K, hK⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective k
    have hKu : K.eval₂ φ v ∉ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hHres, hK]
      exact fun h0 => hgk (hmem_ker hg _ h0)
    have hdiff : (H - G' * K).map (residue B) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, hG', hK, ← hh, hk, sub_self]
    obtain ⟨s, hs⟩ := hlift _ hdiff
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul] at hs
    refine ⟨![t, G'.eval₂ φ v, w], ![![-(s + a₀), -K.eval₂ φ v, -b₀], ![0, 0, 0], ![0, 0, 1]],
      ?_, ?_, ⟨2, 2, le_rfl, ?_⟩, ?_, ?_⟩
    · rw [range_fin_three]
      exact hgen.symm
    · intro p r hpr
      fin_cases p <;> fin_cases r <;> simp at hpr ⊢
    · simp
    · have : ∑ p, ∑ r, ![![-(s + a₀), -K.eval₂ φ v, -b₀], ![0, 0, 0], ![0, 0, 1]] p r *
          (![t, G'.eval₂ φ v, w] p * ![t, G'.eval₂ φ v, w] r) = 0 := by
        simp only [Fin.sum_univ_three]
        simp
        linear_combination hrel + t * hGe + t * hs
      rw [this]
      exact zero_mem _
    · apply not_isScalarSqLinear_of_coeff
      · simp
      · simp
      · simpa using IsLocalRing.notMem_maximalIdeal.mp hKu
  right
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hh0 (by rw [hk, zero_mul])
  have hgnu : ¬ IsUnit g := by
    intro hu
    have h1 : θ 1 = 0 := by
      have : (1 : (ResidueField B)[X]) ∈ RingHom.ker θ := by
        rw [hg, Ideal.mem_span_singleton]; exact hu.dvd
      exact this
    exact one_ne_zero (by rw [map_one] at h1; exact h1)
  have hdeg1 : g.natDegree = 1 := by
    have h1 : (g * g).natDegree ≤ h.natDegree := Polynomial.natDegree_le_of_dvd hdiv2 hh0
    rw [Polynomial.natDegree_mul hg0 hg0] at h1
    have h3 : g.natDegree ≠ 0 := fun h0 => hgnu
      (Polynomial.isUnit_iff_degree_eq_zero.mpr
        (by rw [Polynomial.degree_eq_natDegree hg0, h0]; rfl))
    lia
  set α := g.coeff 1 with hα_def
  have hα : α ≠ 0 := by
    have : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg0
    rwa [Polynomial.leadingCoeff, hdeg1] at this
  obtain ⟨μ, hμ⟩ := IsLocalRing.residue_surjective (-(g.coeff 0) / α)
  set μb := residue B μ with hμb
  have hgX : g = Polynomial.C α * (Polynomial.X - Polynomial.C μb) := by
    have hαμ : α * μb = -(g.coeff 0) := by rw [hμ]; field_simp
    calc g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) :=
          Polynomial.eq_X_add_C_of_natDegree_le_one hdeg1.le
      _ = Polynomial.C α * (Polynomial.X - Polynomial.C μb) := by
          rw [mul_sub, ← Polynomial.C_mul, hαμ, Polynomial.C_neg]; ring
  have hkerμ : RingHom.ker θ = Ideal.span {Polynomial.X - Polynomial.C μb} := by
    rw [hg, hgX, Ideal.span_singleton_mul_left_unit
      (Polynomial.isUnit_C.mpr (IsUnit.mk0 α hα))]
  have hgen' := maximalIdeal_eq_span_of_ker φ ht hwm hφm hloc hkerμ
    (G := Polynomial.X - Polynomial.C μ) (by simp [hμb])
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hgen'
  refine ⟨μ, hh0, hgen', ?_⟩
  set γ := v - φ μ with hγ
  have hγm : γ ∈ maximalIdeal C := hgen' ▸ Ideal.subset_span (by simp)
  have hsq : (Polynomial.X - Polynomial.C μb) ^ 2 ∣ h :=
    dvd_trans ⟨Polynomial.C α * Polynomial.C α, by rw [hgX]; ring⟩ hdiv2
  have hevalXμ : (Polynomial.X - Polynomial.C μ).eval₂ φ v = γ := by simp [hγ]
  by_cases h3 : (Polynomial.X - Polynomial.C μb) ^ 3 ∣ h
  · right
    refine ⟨h3, ?_⟩
    obtain ⟨m', hm'⟩ := h3
    have hm'0 : m' ≠ 0 := by rintro rfl; exact hh0 (by rw [hm', mul_zero])
    have hdm : m'.natDegree = 0 := by
      have := congrArg Polynomial.natDegree hm'
      rw [Polynomial.natDegree_mul (pow_ne_zero 3 (Polynomial.X_sub_C_ne_zero μb)) hm'0,
        Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at this
      lia
    have hm'C : m' = Polynomial.C (m'.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdm
    have hc0 : m'.coeff 0 ≠ 0 := fun h0 => hm'0 (by rw [hm'C, h0, map_zero])
    obtain ⟨c', hc'⟩ := IsLocalRing.residue_surjective (m'.coeff 0)
    have hc'm : φ c' ∉ maximalIdeal C := by
      refine notMem_maximalIdeal_map φ fun hm => hc0 ?_
      rw [← hc']; exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
    have hdiff : (H - Polynomial.C c' * (Polynomial.X - Polynomial.C μ) ^ 3).map (residue B) =
        0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, Polynomial.map_C, ← hh, hm', hm'C, hc', ← hμb]
      ring
    obtain ⟨s, hs⟩ := hlift _ hdiff
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, hevalXμ,
      Polynomial.eval₂_C] at hs
    exact isCaseOne_or_isTripleRootData_of_cube hc'm ht hγm hwm hgen'
      (a := s + a₀) (b := b₀) (by rw [hrel, hGe]; linear_combination t * hs)
  · left
    refine ⟨hsq, h3, ?_⟩
    obtain ⟨m', hm'⟩ := hsq
    have hm'r : θ m' ≠ 0 := by
      intro h0
      obtain ⟨m'', hm''⟩ := hmem_ker hkerμ _ h0
      exact h3 ⟨m'', by rw [hm', hm'']; ring⟩
    obtain ⟨M, hM⟩ := Polynomial.map_surjective (residue B) IsLocalRing.residue_surjective m'
    have hMu : M.eval₂ φ v ∉ maximalIdeal C := by
      rw [← IsLocalRing.residue_eq_zero_iff, ← hHres, hM]
      exact hm'r
    have hdiff : (H - (Polynomial.X - Polynomial.C μ) ^ 2 * M).map (residue B) = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub,
        Polynomial.map_X, Polynomial.map_C, ← hh, hm', hM, ← hμb, sub_self]
    obtain ⟨s, hs⟩ := hlift _ hdiff
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, hevalXμ] at hs
    exact isCaseOne_or_isUnitSpecialCoordinate_of_sq (t := t) (v := γ) (w := w)
        (c := -M.eval₂ φ v) (d := 0) (f := 0) (α' := 0) (β' := 0) (L₀ := -b₀)
        (c₀ := s + a₀) (fun hm => hMu (by simpa using neg_mem hm)) ht hγm hwm hgen'
        (by rw [hrel, hGe]; linear_combination t * hs)

end Core

/-! ### Polynomial facts -/

/-- A nonzero polynomial of degree at most one is not divisible by the square of a linear
polynomial. -/
theorem not_sq_dvd_of_natDegree_le_one {k : Type*} [Field k] {h : k[X]} (h0 : h ≠ 0)
    (hd : h.natDegree ≤ 1) (μ : k) : ¬ (Polynomial.X - Polynomial.C μ) ^ 2 ∣ h := by
  intro hdvd
  have := Polynomial.natDegree_le_of_dvd hdvd h0
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at this
  lia

/-- If `(X - μ)³` divides the nonzero polynomial `X²(a + bX)`, then `μ = 0` and `a = 0`. -/
theorem eq_zero_and_eq_zero_of_cube_dvd {k : Type*} [Field k] {a b μ : k}
    (h0 : Polynomial.X ^ 2 * (Polynomial.C a + Polynomial.C b * Polynomial.X) ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C μ) ^ 3 ∣
      Polynomial.X ^ 2 * (Polynomial.C a + Polynomial.C b * Polynomial.X)) :
    μ = 0 ∧ a = 0 := by
  have hl0 : Polynomial.C a + Polynomial.C b * Polynomial.X ≠ 0 := by
    rintro h; exact h0 (by rw [h, mul_zero])
  by_cases hμ : μ = 0
  · refine ⟨hμ, ?_⟩
    rw [hμ, map_zero, sub_zero, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero 2 X_ne_zero)]
      at hdvd
    have := Polynomial.X_dvd_iff.mp hdvd
    simpa using this
  · exfalso
    have hcop : IsCoprime (Polynomial.X - Polynomial.C μ) Polynomial.X := by
      refine ⟨Polynomial.C (-μ⁻¹), Polynomial.C μ⁻¹, ?_⟩
      rw [← sub_eq_zero]
      have : Polynomial.C (-μ⁻¹) * (Polynomial.X - Polynomial.C μ) +
          Polynomial.C μ⁻¹ * Polynomial.X - 1 = Polynomial.C (μ⁻¹ * μ) - 1 := by
        simp only [map_neg, map_mul]; ring
      rw [this, inv_mul_cancel₀ hμ, map_one, sub_self]
    have hd := (hcop.pow (m := 3) (n := 2)).dvd_of_dvd_mul_left hdvd
    have := Polynomial.natDegree_le_of_dvd hd hl0
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C] at this
    have h1 : (Polynomial.C a + Polynomial.C b * Polynomial.X).natDegree ≤ 1 := by
      compute_degree
    lia

/-- The reduction of `a + bX` modulo the maximal ideal has degree at most one. -/
theorem natDegree_map_C_add_C_mul_X_le {B : Type*} [CommRing B] [IsLocalRing B] (a b : B) :
    ((Polynomial.C a + Polynomial.C b * Polynomial.X).map (residue B)).natDegree ≤ 1 := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_C,
    Polynomial.map_X]
  compute_degree!

/-! ### The charts of the blowup at a triple root -/

section TripleRootCharts

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- In a chart `φ (x k) = φ (x j) * Y k`, the image of the maximal ideal lies in `(φ (x j))`, and
`φ (x j)` lies in the maximal ideal. -/
private theorem map_mem_span_and_mem_maximalIdeal_of_chart {x : Fin 3 → B}
    (hx : Ideal.span (Set.range x) = maximalIdeal B) {j : Fin 3} {Y : Fin 3 → C}
    (hY : ∀ k, φ (x k) = φ (x j) * Y k) :
    (∀ b ∈ maximalIdeal B, φ b ∈ Ideal.span {φ (x j)}) ∧ φ (x j) ∈ maximalIdeal C :=
  ⟨map_mem_span_of_generators φ hx fun k => by
      rw [hY k]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _),
    map_nonunit φ _ (hx ▸ Ideal.subset_span ⟨j, rfl⟩)⟩

/-- **The blowup at a triple root, at a point of a chart.** Let `x₁, x₂, x₃` generate the maximal
ideal of `B` with `x₃² = x₁(λx₂³ + x₁·Σ αᵢxᵢ + x₃·Σ βᵢxᵢ)`, `λ` a unit, and let `C` be a
two-dimensional Noetherian normal local domain over `B` which is not regular, a localization of
the chart at `x_j` in the sense of `AlgebraicGeometry.exists_chartData`. Then `C` is in case I,
or carries a unit-special coordinate, or `α₂` lies in the maximal ideal and `C` has the shape
`AlgebraicGeometry.IsTripleRootSecond`. -/
theorem isCaseOne_or_of_isTripleRootData_chart [IsDomain C] [IsNoetherianRing C]
    [IsIntegrallyClosed C] (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {x : Fin 3 → B} (hx : Ideal.span (Set.range x) = maximalIdeal B) {lam : B}
    (hlam : lam ∉ maximalIdeal B) {α β : Fin 3 → B}
    (hrel : x 2 * x 2 = x 0 * (lam * x 1 ^ 3 + x 0 * ∑ i, α i * x i + x 2 * ∑ i, β i * x i))
    (j : Fin 3) (Y : Fin 3 → C) (hYj : Y j = 1) (hY : ∀ k, φ (x k) = φ (x j) * Y k)
    (hxj : φ (x j) ≠ 0)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : MvPolynomial (Fin 3) B), IsUnit b ∧
      b * c = MvPolynomial.eval₂ φ Y P ∧ b = MvPolynomial.eval₂ φ Y Q) :
    IsCaseOne C ∨ (∃ e, IsUnitSpecialCoordinate C e) ∨
      (α 1 ∈ maximalIdeal B ∧ IsTripleRootSecond C) := by
  classical
  obtain ⟨hφm, ht⟩ := map_mem_span_and_mem_maximalIdeal_of_chart φ hx hY
  set t := φ (x j) with ht_def
  set A := ∑ i, φ (α i) * Y i with hA
  set Bb := ∑ i, φ (β i) * Y i with hBb
  have hrelC : Y 2 * Y 2 = t * (Y 0 * (φ lam * t * Y 1 ^ 3 + Y 0 * A + Y 2 * Bb)) := by
    have h1 := congrArg φ hrel
    simp only [map_add, map_mul, map_pow, map_sum, hY] at h1
    refine mul_left_cancel₀ (pow_ne_zero 2 hxj) ?_
    rw [hA, hBb]
    simp only [Fin.sum_univ_three] at h1 ⊢
    linear_combination h1
  have hlamC : φ lam ∉ maximalIdeal C := notMem_maximalIdeal_map φ hlam
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · left
    have hloc' := exists_polynomial_of_mvPolynomial φ ![1, Polynomial.X, 0] (v := Y 1) (w := Y 2)
      (fun i => by fin_cases i <;> simp [hYj]) hloc
    have hG : (φ lam * t * Y 1 ^ 3 + A + Y 2 * Bb) -
        (Polynomial.C (α 0) + Polynomial.C (α 1) * Polynomial.X).eval₂ φ (Y 1) ∈
          Ideal.span {t, Y 2} := by
      refine Ideal.mem_span_pair.mpr ⟨φ lam * Y 1 ^ 3, φ (α 2) + Bb, ?_⟩
      simp only [hA, Fin.sum_univ_three, hYj, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X]
      ring
    rcases isCaseOne_or_exists_of_sq_eq_mul φ hdimC hsing hxj ht hφm
        (by rw [hrelC, hYj, one_mul, one_mul]) _ hG ((natDegree_map_C_add_C_mul_X_le _ _).trans
          (by norm_num))
        (fun c => let ⟨b, P, _, hb, hP, _⟩ := hloc' c; ⟨b, P, hb, hP⟩)
      with hI | ⟨μ, hne, -, h2 | h3⟩
    · exact hI
    · exact absurd h2.1 (not_sq_dvd_of_natDegree_le_one hne
        (natDegree_map_C_add_C_mul_X_le _ _) _)
    · exact absurd (dvd_trans (pow_dvd_pow _ (by norm_num)) h3.1)
        (not_sq_dvd_of_natDegree_le_one hne (natDegree_map_C_add_C_mul_X_le _ _) _)
  · have hloc' := exists_polynomial_of_mvPolynomial φ ![Polynomial.X, 1, 0] (v := Y 0) (w := Y 2)
      (fun i => by fin_cases i <;> simp [hYj]) hloc
    set H : B[X] := Polynomial.X ^ 2 * (Polynomial.C (α 1) + Polynomial.C (α 0) * Polynomial.X)
      with hH
    have hG : Y 0 * (φ lam * t * Y 1 ^ 3 + Y 0 * A + Y 2 * Bb) - H.eval₂ φ (Y 0) ∈
        Ideal.span {t, Y 2} := by
      refine Ideal.mem_span_pair.mpr ⟨Y 0 * φ lam, Y 0 * Y 0 * φ (α 2) + Y 0 * Bb, ?_⟩
      simp only [hA, hH, Fin.sum_univ_three, hYj, Polynomial.eval₂_add, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_X_pow]
      ring
    have hHmap : H.map (residue B) = Polynomial.X ^ 2 * (Polynomial.C (residue B (α 1)) +
        Polynomial.C (residue B (α 0)) * Polynomial.X) := by
      simp [hH]
    rcases isCaseOne_or_exists_of_sq_eq_mul φ hdimC hsing hxj ht hφm hrelC H hG
        (by rw [hHmap]; compute_degree)
        (fun c => let ⟨b, P, _, hb, hP, _⟩ := hloc' c; ⟨b, P, hb, hP⟩)
      with hI | ⟨μ, hne, hgen, h2 | h3⟩
    · exact Or.inl hI
    · rcases h2.2.2 with hI | hU
      · exact Or.inl hI
      · exact Or.inr (Or.inl ⟨_, hU⟩)
    · right; right
      rw [hHmap] at hne h3
      obtain ⟨hμ0, hα1⟩ := eq_zero_and_eq_zero_of_cube_dvd hne h3.1
      have hα1m : α 1 ∈ maximalIdeal B := (IsLocalRing.residue_eq_zero_iff _).mp hα1
      have hμm : μ ∈ maximalIdeal B := (IsLocalRing.residue_eq_zero_iff _).mp hμ0
      have hα0 : φ (α 0) ∉ maximalIdeal C := by
        refine notMem_maximalIdeal_map φ fun hm => hne ?_
        rw [hα1, (IsLocalRing.residue_eq_zero_iff _).mpr hm]
        simp
      obtain ⟨α', hα'⟩ := Ideal.mem_span_singleton'.mp (hφm _ hα1m)
      obtain ⟨μ', hμ'⟩ := Ideal.mem_span_singleton'.mp (hφm _ hμm)
      have hY0m : Y 0 ∈ maximalIdeal C := by
        have h1 : Y 0 - φ μ ∈ maximalIdeal C := hgen ▸ Ideal.subset_span (by simp)
        simpa using add_mem h1 (map_nonunit φ _ hμm)
      refine ⟨hα1m, ![t, Y 0, Y 2], φ (α 0), ![0, φ lam + α' * Y 0, 0],
        ![0, φ (α 2) * Y 0 + Bb, 0], ?_, hα0, ?_, ?_⟩
      · rw [range_fin_three, hgen]
        apply le_antisymm
        · rw [Ideal.span_le]
          intro y hy
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
            Matrix.tail_cons, Matrix.head_cons, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Ideal.subset_span (by simp)
          · have : Y 0 = (Y 0 - φ μ) + μ' * t := by rw [hμ']; ring
            have hmem : (Y 0 - φ μ) + μ' * t ∈ Ideal.span {t, Y 0 - φ μ, Y 2} :=
              add_mem (Ideal.subset_span (by simp))
                (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
            rwa [← this] at hmem
          · exact Ideal.subset_span (by simp)
        · rw [Ideal.span_le]
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl | rfl
          · exact Ideal.subset_span (by simp)
          · rw [← hμ']
            exact sub_mem (Ideal.subset_span (by simp))
              (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
          · exact Ideal.subset_span (by simp)
      · intro h
        apply hlamC
        have : φ lam = (φ lam + α' * Y 0) - α' * Y 0 := by ring
        rw [this]
        exact sub_mem (by simpa using h) (Ideal.mul_mem_left _ _ hY0m)
      · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
        rw [hrelC, hA, hBb]
        simp only [Fin.sum_univ_three, hYj]
        linear_combination (-t * Y 0 ^ 2) * hα'
  · exfalso
    rw [hYj, one_mul] at hrelC
    exact one_notMem_maximalIdeal' C (hrelC ▸ Ideal.mul_mem_right _ _ ht)

end TripleRootCharts

/-! ### The charts of the blowup of a case II singularity -/

section CubicCharts

variable {B C : Type*} [CommRing B] [IsLocalRing B] [CommRing C] [IsLocalRing C]
  (φ : B →+* C) [IsLocalHom φ]

/-- The cubic on the double line, in a chart: `Σ bₚᵩᵣ eₚeᵩeᵣ` for polynomials `eᵢ` of degree at
most one. -/
def cubicChartPoly (b : Fin 3 → Fin 3 → Fin 3 → B) (ev : Fin 3 → B[X]) : B[X] :=
  ∑ p, ∑ q, ∑ r, Polynomial.C (b p q r) * (ev p * ev q * ev r)

/-- The reduction of `AlgebraicGeometry.cubicChartPoly b ev` modulo the maximal ideal has degree at
most three when every `ev i` has degree at most one. -/
theorem natDegree_map_cubicChartPoly_le (b : Fin 3 → Fin 3 → Fin 3 → B) {ev : Fin 3 → B[X]}
    (hev : ∀ i, (ev i).natDegree ≤ 1) :
    ((cubicChartPoly b ev).map (residue B)).natDegree ≤ 3 := by
  have hev' : ∀ i, ((ev i).map (residue B)).natDegree ≤ 1 :=
    fun i => (Polynomial.natDegree_map_le).trans (hev i)
  simp only [cubicChartPoly, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun q _ => ?_
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r _ => ?_
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  have := (Polynomial.natDegree_mul_le (p := (ev p).map (residue B))
    (q := (ev q).map (residue B))).trans (add_le_add (hev' p) (hev' q))
  have := add_le_add this (hev' r)
  lia

/-- **The blowup of a case II singularity, at a point of a chart.** Let `x₁, x₂, x₃` generate the
maximal ideal of `B` with `x₃² = Σ bₚᵩᵣ xₚxᵩxᵣ`, and let `C` be a two-dimensional Noetherian normal
local domain over `B` which is not regular, a localization of the chart at `x_j` in the sense of
`AlgebraicGeometry.exists_chartData`. Then `C` is in case I, or carries a unit-special
coordinate, or has the shape `AlgebraicGeometry.IsTripleRootData`. -/
theorem isCaseOne_or_of_cubic_chart [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    (hdimC : ringKrullDim C = 2) (hsing : ¬ IsRegularLocalRing C)
    {x : Fin 3 → B} (hx : Ideal.span (Set.range x) = maximalIdeal B)
    {b : Fin 3 → Fin 3 → Fin 3 → B}
    (hrel : x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r))
    (j : Fin 3) (Y : Fin 3 → C) (hYj : Y j = 1) (hY : ∀ k, φ (x k) = φ (x j) * Y k)
    (hxj : φ (x j) ≠ 0)
    (hloc : ∀ c : C, ∃ (b : C) (P Q : MvPolynomial (Fin 3) B), IsUnit b ∧
      b * c = MvPolynomial.eval₂ φ Y P ∧ b = MvPolynomial.eval₂ φ Y Q) :
    IsCaseOne C ∨ (∃ e, IsUnitSpecialCoordinate C e) ∨ IsTripleRootData C := by
  classical
  obtain ⟨hφm, ht⟩ := map_mem_span_and_mem_maximalIdeal_of_chart φ hx hY
  set t := φ (x j) with ht_def
  set P : MvPolynomial (Fin 3) B := ∑ p, ∑ q, ∑ r, MvPolynomial.C (b p q r) *
    (MvPolynomial.X p * MvPolynomial.X q * MvPolynomial.X r) with hP
  set G := MvPolynomial.eval₂ φ Y P with hGdef
  have hrelC : Y 2 * Y 2 = t * G := by
    have h1 := congrArg φ hrel
    simp only [map_mul, map_sum, hY] at h1
    refine mul_left_cancel₀ (pow_ne_zero 2 hxj) ?_
    simp only [hGdef, hP, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_X, Finset.mul_sum] at h1 ⊢
    rw [show t ^ 2 * (Y 2 * Y 2) = t * Y 2 * (t * Y 2) by ring, h1]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
      Finset.sum_congr rfl fun r _ => ?_
    ring
  have key : ∀ (v : C) (ev : Fin 3 → B[X]), (∀ i, (ev i).natDegree ≤ 1) →
      (∀ i, Y i - (ev i).eval₂ φ v ∈ Ideal.span {Y 2}) →
      IsCaseOne C ∨ (∃ e, IsUnitSpecialCoordinate C e) ∨ IsTripleRootData C := by
    intro v ev hev hs
    have hloc' := exists_polynomial_of_mvPolynomial φ ev hs hloc
    have hHeval : (cubicChartPoly b ev).eval₂ φ v =
        MvPolynomial.eval₂ φ (fun i => (ev i).eval₂ φ v) P := by
      simp only [cubicChartPoly, hP, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
        Polynomial.eval₂_C, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
        MvPolynomial.eval₂_X]
    have hG : G - (cubicChartPoly b ev).eval₂ φ v ∈ Ideal.span {t, Y 2} := by
      rw [hHeval]
      exact (Ideal.span_mono (by simp)) (MvPolynomial.eval₂_sub_eval₂_mem φ _ _ _ hs P)
    rcases isCaseOne_or_exists_of_sq_eq_mul φ hdimC hsing hxj ht hφm hrelC _ hG
        (natDegree_map_cubicChartPoly_le b hev)
        (fun c => let ⟨b, P, _, hb, hP, _⟩ := hloc' c; ⟨b, P, hb, hP⟩)
      with hI | ⟨μ, -, -, h2 | h3⟩
    · exact Or.inl hI
    · rcases h2.2.2 with hI | hU
      · exact Or.inl hI
      · exact Or.inr (Or.inl ⟨_, hU⟩)
    · rcases h3.2 with hI | hT
      · exact Or.inl hI
      · exact Or.inr (Or.inr hT)
  obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  · refine key (Y 1) ![1, Polynomial.X, 0] (fun i => by fin_cases i <;> simp) fun i => ?_
    fin_cases i <;> simp [hYj]
  · refine key (Y 0) ![Polynomial.X, 1, 0] (fun i => by fin_cases i <;> simp) fun i => ?_
    fin_cases i <;> simp [hYj]
  · exfalso
    rw [hYj, one_mul] at hrelC
    exact one_notMem_maximalIdeal' C (hrelC ▸ Ideal.mul_mem_right _ _ ht)

end CubicCharts

/-! ### Three successive singular points -/

namespace RationalDoublePointSituation

/-- A Situation 0BGC which is not in case I has, given the dimension formula, generators
`x₁, x₂, x₃` of the maximal ideal with `x₃² = Σ bₚᵩᵣ xₚxᵩxᵣ`. -/
theorem exists_sq_eq_cubicExpansion_of_not_isCaseOne (S : RationalDoublePointSituation.{u})
    (hdim : ∀ n, Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1)
    (hnot : ¬ IsCaseOne S.A) :
    ∃ (x : Fin 3 → S.A) (b : Fin 3 → Fin 3 → Fin 3 → S.A),
      Ideal.span (Set.range x) = IsLocalRing.maximalIdeal S.A ∧
        x 2 * x 2 = ∑ p, ∑ q, ∑ r, b p q r * (x p * x q * x r) := by
  rcases exists_sq_eq_cubicExpansion_or_not_isScalarSqLinear (by rw [hdim]) (by rw [hdim])
    with h | ⟨x, a, b, hspan, hupper, hunit, hrel, hcase⟩
  · exact h
  · exfalso
    apply hnot
    refine ⟨x, a, hspan, hupper, hunit, ?_, hcase⟩
    rw [hrel]
    have hxm : ∀ i, x i ∈ IsLocalRing.maximalIdeal S.A :=
      fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
    refine Ideal.sum_mem _ fun p _ => Ideal.sum_mem _ fun q _ => Ideal.sum_mem _ fun r _ => ?_
    refine Ideal.mul_mem_left _ _ ?_
    rw [pow_succ]
    exact Ideal.mul_mem_mul (by rw [sq]; exact Ideal.mul_mem_mul (hxm p) (hxm q)) (hxm r)

/-- The local ring at a singular point of the blowup of a Situation 0BGC is local over `A`,
Noetherian, a normal domain, and of dimension two. -/
theorem stalk_blowUp_facts (S : RationalDoublePointSituation.{u})
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    IsLocalHom (blowUpStalkHom S.A x) ∧
      IsNoetherianRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
      IsNormalDomain ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∧
      ringKrullDim ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) = 2 := by
  have hover := S.blowUpToBase_eq_closedPoint_of_mem_singularLocus x hx
  have hclosed := S.isClosed_singleton_of_mem_singularLocus_blowUp x hx
  have : IsLocallyNoetherian (blowUp (maximalIdealSheaf S.A)) :=
    LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (maximalIdealSheaf S.A))
  exact ⟨isLocalHom_germ_appTop (blowUpToBase (maximalIdealSheaf S.A)) x hover, inferInstance,
    S.isNormalDomain_stalk_blowUp x, S.ringKrullDim_stalk_blowUp_eq_two x hclosed⟩

/-- **The first singular point over a case II singularity.** For a Situation 0BGC satisfying the
dimension formula and not in case I, the local ring at a singular point of the blowup is in case I,
carries a unit-special coordinate, or has the shape `AlgebraicGeometry.IsTripleRootData`. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_or_isTripleRootData_stalk_blowUp
    (S : RationalDoublePointSituation.{u})
    (hdim : ∀ n, Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1)
    (hnot : ¬ IsCaseOne S.A) (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∨
      (∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) e) ∨
      IsTripleRootData ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) := by
  obtain ⟨g, b, hspan, hrel⟩ := S.exists_sq_eq_cubicExpansion_of_not_isCaseOne hdim hnot
  obtain ⟨hloc, hnoeth, hnorm, hdimC⟩ := S.stalk_blowUp_facts x hx
  obtain ⟨j, Y, hYj, hY, hxj, hpoly⟩ := exists_chartData_blowUp S.A hspan x
  exact isCaseOne_or_of_cubic_chart (blowUpStalkHom S.A x) hdimC hx hspan hrel j Y hYj hY hxj
    hpoly

/-- **The singular points over a triple root.** For a Situation 0BGC of the shape
`AlgebraicGeometry.IsTripleRootData`, the local ring at a singular point of the blowup is in
case I, carries a unit-special coordinate, or has the shape
`AlgebraicGeometry.IsTripleRootSecond`. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_or_isTripleRootSecond_stalk_blowUp
    (S : RationalDoublePointSituation.{u}) (hS : IsTripleRootData S.A)
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∨
      (∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) e) ∨
      IsTripleRootSecond ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) := by
  obtain ⟨g, lam, α, β, hspan, hlam, hrel⟩ := hS
  obtain ⟨hloc, hnoeth, hnorm, hdimC⟩ := S.stalk_blowUp_facts x hx
  obtain ⟨j, Y, hYj, hY, hxj, hpoly⟩ := exists_chartData_blowUp S.A hspan x
  rcases isCaseOne_or_of_isTripleRootData_chart (blowUpStalkHom S.A x) hdimC hx hspan hlam hrel
      j Y hYj hY hxj hpoly with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.2)

/-- **The singular points over a second triple root in a row.** For a Situation 0BGC of the shape
`AlgebraicGeometry.IsTripleRootSecond`, the local ring at a singular point of the blowup is in
case I or carries a unit-special coordinate. -/
theorem isCaseOne_or_isUnitSpecialCoordinate_stalk_blowUp_of_isTripleRootSecond
    (S : RationalDoublePointSituation.{u}) (hS : IsTripleRootSecond S.A)
    (x : blowUp (maximalIdealSheaf S.A))
    (hx : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x)) :
    IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) ∨
      ∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x) e := by
  obtain ⟨g, lam, α, β, hspan, hlam, hα, hrel⟩ := hS
  obtain ⟨hloc, hnoeth, hnorm, hdimC⟩ := S.stalk_blowUp_facts x hx
  obtain ⟨j, Y, hYj, hY, hxj, hpoly⟩ := exists_chartData_blowUp S.A hspan x
  rcases isCaseOne_or_of_isTripleRootData_chart (blowUpStalkHom S.A x) hdimC hx hspan hlam hrel
      j Y hYj hY hxj hpoly with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h.1 hα

/-- **Among three successive singular points over a case II rational double point, one is in
case I or carries a unit-special coordinate.** Let `S` be a Situation 0BGC satisfying the
dimension formula `dim 𝔪ⁿ/𝔪ⁿ⁺¹ = 2n + 1` and not in case I; let `x₁` be a singular point of the
blowup of `Spec(A)` in its maximal ideal, `T₁` a Situation 0BGC whose ring is the local ring at
`x₁`, `x₂` a singular point of the blowup of `Spec(T₁.A)`, `T₂` a Situation 0BGC whose ring is
the local ring at `x₂`, and `x₃` a singular point of the blowup of `Spec(T₂.A)`. Then the local
ring at one of `x₁, x₂, x₃` is in case I or has a unit-special coordinate. -/
theorem exists_isCaseOne_or_isUnitSpecialCoordinate_of_three_blowUps
    (S : RationalDoublePointSituation.{u})
    (hdim : ∀ n, Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1)
    (hnot : ¬ IsCaseOne S.A)
    (x₁ : blowUp (maximalIdealSheaf S.A))
    (h₁ : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x₁))
    (T₁ : RationalDoublePointSituation.{u})
    (e₁ : T₁.A ≃+* (blowUp (maximalIdealSheaf S.A)).presheaf.stalk x₁)
    (x₂ : blowUp (maximalIdealSheaf T₁.A))
    (h₂ : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf T₁.A)).presheaf.stalk x₂))
    (T₂ : RationalDoublePointSituation.{u})
    (e₂ : T₂.A ≃+* (blowUp (maximalIdealSheaf T₁.A)).presheaf.stalk x₂)
    (x₃ : blowUp (maximalIdealSheaf T₂.A))
    (h₃ : ¬ IsRegularLocalRing ((blowUp (maximalIdealSheaf T₂.A)).presheaf.stalk x₃)) :
    (IsCaseOne ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x₁) ∨
        ∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf S.A)).presheaf.stalk x₁) e) ∨
      (IsCaseOne ((blowUp (maximalIdealSheaf T₁.A)).presheaf.stalk x₂) ∨
        ∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf T₁.A)).presheaf.stalk x₂) e) ∨
      (IsCaseOne ((blowUp (maximalIdealSheaf T₂.A)).presheaf.stalk x₃) ∨
        ∃ e, IsUnitSpecialCoordinate ((blowUp (maximalIdealSheaf T₂.A)).presheaf.stalk x₃) e) := by
  rcases S.isCaseOne_or_isUnitSpecialCoordinate_or_isTripleRootData_stalk_blowUp hdim hnot x₁ h₁
    with h | h | hT₁
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  rcases T₁.isCaseOne_or_isUnitSpecialCoordinate_or_isTripleRootSecond_stalk_blowUp
      (hT₁.of_ringEquiv e₁.symm) x₂ h₂ with h | h | hT₂
  · exact Or.inr (Or.inl (Or.inl h))
  · exact Or.inr (Or.inl (Or.inr h))
  exact Or.inr (Or.inr
    (T₂.isCaseOne_or_isUnitSpecialCoordinate_stalk_blowUp_of_isTripleRootSecond
      (hT₂.of_ringEquiv e₂.symm) x₃ h₃))

end RationalDoublePointSituation

/-! ### Special coordinates are unit-special -/

namespace RationalDoublePointSituation

/-- **A special coordinate of a rational double point is unit-special.** Under the dimension
formula, the coefficient `a` of `x₂²` in `x₃² + x₁(a x₂² + b x₂x₃ + c x₃²) ∈ 𝔪⁴` is a unit. -/
theorem isUnitSpecialCoordinate_of_isSpecialCoordinate (S : RationalDoublePointSituation.{u})
    (hdim : ∀ n, Module.finrank (ResidueField S.A) (IsLocalRing.gradedPiece S.A n) = 2 * n + 1)
    {e : S.A} (he : IsSpecialCoordinate S.A e) : IsUnitSpecialCoordinate S.A e := by
  classical
  obtain ⟨x, a, b, c, hx0, hspan, hrel⟩ := he
  by_cases ha : a ∉ IsLocalRing.maximalIdeal S.A
  · refine ⟨x, ![![0, 0, 0], ![0, a, b], ![0, 0, c]], hx0, hspan, by simpa using ha, ?_⟩
    simp only [Fin.sum_univ_three]
    simpa [add_mul, mul_add, add_assoc, mul_assoc] using hrel
  exfalso
  push Not at ha
  have hxm : ∀ i, x i ∈ IsLocalRing.maximalIdeal S.A := fun i => hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  have hsq3 : x 2 * x 2 ∈ IsLocalRing.maximalIdeal S.A ^ 3 := by
    have h4 : IsLocalRing.maximalIdeal S.A ^ 4 ≤ IsLocalRing.maximalIdeal S.A ^ 3 :=
      Ideal.pow_le_pow_right (by norm_num)
    have : x 2 * x 2 = (x 2 * x 2 + x 0 * (a * (x 1 * x 1) + b * (x 1 * x 2) + c * (x 2 * x 2))) -
        x 0 * (a * (x 1 * x 1) + b * (x 1 * x 2) + c * (x 2 * x 2)) := by ring
    rw [this]
    refine sub_mem (h4 hrel) ?_
    rw [pow_succ', sq]
    refine Ideal.mul_mem_mul (hxm 0) (add_mem (add_mem ?_ ?_) ?_) <;>
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (hxm _) (hxm _))
  set M : Fin 3 → Fin 3 → S.A := ![![0, 0, 0], ![0, 0, 0], ![0, 0, 1]] with hM
  have hI := gradedRelationIdeal_eq_span_quadraticFormPoly hxm hspan hdim M
    (fun p r hpr => by fin_cases p <;> fin_cases r <;> simp [hM] at hpr ⊢)
    ⟨2, 2, le_rfl, by simp [hM]⟩
    (by simpa [hM, Fin.sum_univ_three] using hsq3)
  have hq : (quadraticFormPoly fun p r => IsLocalRing.residue S.A (M p r)) =
      MvPolynomial.X 2 * MvPolynomial.X 2 := by
    simp [quadraticFormPoly, hM, Fin.sum_univ_three]
  rw [hq] at hI
  have hdvd : ¬ (MvPolynomial.X (0 : Fin 3) ∣
      (MvPolynomial.X 2 * MvPolynomial.X 2 : MvPolynomial (Fin 3) (ResidueField S.A))) := by
    rintro ⟨r, hr⟩
    have := congrArg (MvPolynomial.eval ![0, 0, 1]) hr
    simp at this
  have hsup : ∀ (m : ℕ) (w : S.A), w ∈ IsLocalRing.maximalIdeal S.A ^ m →
      x 0 * w ∈ IsLocalRing.maximalIdeal S.A ^ (m + 2) →
        w ∈ IsLocalRing.maximalIdeal S.A ^ (m + 1) :=
    fun m w hw hmul => mem_pow_succ_of_mul_mem_pow hxm hspan hI hdvd hw hmul
  set A' := affineBlowupAlgebra (IsLocalRing.maximalIdeal S.A) (x 0)
    (Localization.Away (x 0)) with hA'
  have hnorm : IsNormalRing A' := by
    have hg := mem_ideal_ofIdealTop_isAffineOpen_top S.A (IsLocalRing.maximalIdeal S.A) (hxm 0)
    have h1 := isNormalRing_affineBlowupAlgebra_of_isNormal_blowUp (maximalIdealSheaf S.A)
      S.isNormal_blowUp ⟨⊤, isAffineOpen_top _⟩ _ hg
    obtain ⟨E, -⟩ := exists_ringEquiv_blowupChartRing_ofIdealTop S.A
      (IsLocalRing.maximalIdeal S.A) (x 0) ⟨_, hg⟩ rfl
    exact IsNormalRing.congr E.symm h1
  have : IsIntegrallyClosed A' := hnorm.isIntegrallyClosed
  set ι := algebraMap S.A A' with hι
  have hreg := Stacks.Blowup.isRegular_algebraMap_affineBlowupAlgebra
    (IsLocalRing.maximalIdeal S.A) (x 0) (Localization.Away (x 0))
  have hmap : ∀ y ∈ IsLocalRing.maximalIdeal S.A, ι y ∈ Ideal.span {ι (x 0)} := by
    intro y hy
    rw [← Stacks.Blowup.map_ideal_algebraMap_affineBlowupAlgebra _ _ _ (hxm 0)]
    exact Ideal.mem_map_of_mem _ hy
  set fr : Fin 3 → A' := fun i => affineBlowupFraction (IsLocalRing.maximalIdeal S.A) (x 0)
    (Localization.Away (x 0)) (hxm i) with hfr
  have hfr' : ∀ i, ι (x 0) * fr i = ι (x i) := fun i =>
    algebraMap_mul_affineBlowupFraction _ _ _ (hxm i)
  have hfr0 : fr 0 = 1 := by
    apply Subtype.ext
    change IsLocalization.mk' (Localization.Away (x 0)) (x 0)
      ⟨x 0, Submonoid.mem_powers (x 0)⟩ = 1
    exact IsLocalization.mk'_self' (M := Submonoid.powers (x 0)) (Localization.Away (x 0))
      (x := ⟨x 0, Submonoid.mem_powers (x 0)⟩)
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp (hmap a ha)
  obtain ⟨r', hr'⟩ : ∃ r', ι (x 2 * x 2 + x 0 * (a * (x 1 * x 1) + b * (x 1 * x 2) +
      c * (x 2 * x 2))) = ι (x 0) ^ 4 * r' := by
    have hle : Ideal.map ι (IsLocalRing.maximalIdeal S.A ^ 4) ≤ Ideal.span {ι (x 0) ^ 4} := by
      rw [Ideal.map_pow, ← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hmap) 4
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (hle (Ideal.mem_map_of_mem ι hrel))
    exact ⟨r, by rw [← hr, mul_comm]⟩
  set t := ι (x 0)
  have hrelA : fr 2 * fr 2 + t * (a' * t * (fr 1 * fr 1) + ι b * (fr 1 * fr 2) +
      ι c * (fr 2 * fr 2)) = t ^ 2 * r' := by
    refine (hreg.left.pow 2) ?_
    simp only [map_add, map_mul, ← hfr', ← ha', hfr0, mul_one] at hr'
    change t ^ 2 * _ = t ^ 2 * _
    linear_combination hr'
  set u := 1 + t * ι c
  have hW : u * fr 2 ∈ Ideal.span {t} := by
    refine mem_span_singleton_of_sq_eq_of_mem_nonZeroDivisors
      hreg.mem_nonZeroDivisors (a := u * (r' - a' * (fr 1 * fr 1)))
      (b := -(ι b * fr 1)) ?_
    linear_combination u * hrelA
  have hy2 : fr 2 ∈ Ideal.span {t} := by
    have : fr 2 = u * fr 2 - t * (ι c * fr 2) := by ring
    rw [this]
    exact sub_mem hW (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self t))
  have hfrac : affineBlowupAlgebra.fraction (S := Localization.Away (x 0))
      (IsLocalRing.maximalIdeal S.A) (x 0) 1 ⟨x 2, by rw [pow_one]; exact hxm 2⟩ = fr 2 := by
    refine (hreg.left.pow 1) ?_
    change t ^ 1 * _ = t ^ 1 * _
    rw [affineBlowupAlgebra.algebraMap_pow_mul_fraction]
    simp only [pow_one]
    exact (hfr' 2).symm
  have hx2 : x 2 ∈ IsLocalRing.maximalIdeal S.A ^ 2 :=
    mem_pow_succ_of_fraction_mem_span_singleton (Localization.Away (x 0)) hxm hsup
      (n := 1) _ (by rw [hfrac]; exact hy2)
  apply S.not_isRegularLocalRing
  have hle : IsLocalRing.maximalIdeal S.A ≤ Ideal.span {x 0, x 1} := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
    rw [← hspan, range_fin_three, Ideal.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Submodule.mem_sup_left (Ideal.subset_span (by simp))
    · exact Submodule.mem_sup_left (Ideal.subset_span (by simp))
    · refine Submodule.mem_sup_right ?_
      have h3 : Ideal.span {x 0, x 1, x 2} = IsLocalRing.maximalIdeal S.A := by
        rw [← range_fin_three]; exact hspan
      rw [h3, smul_eq_mul, ← sq]
      exact hx2
  refine isRegularLocalRing_of_maximalIdeal_eq_span_pair S.dimension_two
    (le_antisymm hle (Ideal.span_le.mpr ?_))
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl <;> exact hxm _

end RationalDoublePointSituation

end AlgebraicGeometry

end
