module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.PlaneCurveModelBaseChange
public import StacksFrontier.RingTheory.NodalChart.Regularity
public import StacksFrontier.AlgebraicGeometry.RelativeProj.FlatOverBase
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover

/-!
# The split conic `T₁T₂ = πT₀²` over a discrete valuation ring

Let `R` be a ring and `a ∈ R`. The plane conic

`V(T₁T₂ - aT₀²) = Proj (R[T₀, T₁, T₂]/(T₁T₂ - aT₀²)) ⊆ ℙ²_R`

is, for `R` a discrete valuation ring and `a = π` a uniformizer, the scheme of
[Stacks, Tag 0CA0]. This file shows that it is regular and flat over `R`, and that its
homogeneous coordinate ring is a domain when `R` is a unique factorization domain and `a ≠ 0`.

## Main definitions

* `Stacks.Models.GenusZero.conicEquation`: the form `T₁T₂ - aT₀²`.
* `Stacks.Models.GenusZero.conicScheme`: the plane conic it cuts out.

## Main results

* `Stacks.Models.GenusZero.prime_conicEquation`: `T₁T₂ - aT₀²` is a prime element of
  `R[T₀, T₁, T₂]`, for `R` a unique factorization domain and `a ≠ 0`.
* `Stacks.Models.GenusZero.isRegular_conicScheme`: for `π` a uniformizer of a discrete valuation
  ring, the conic is regular.
* `Stacks.Models.GenusZero.flat_conicToSpec`: the conic is flat over the discrete valuation ring.

## Implementation notes

The charts are `R[Y₀, Y₁]/(Y₀Y₁ - π)` on `D₊(T₀)`, which is the nodal chart ring of
`StacksFrontier/RingTheory/NodalChart/Regularity.lean`, and `R[Y₀, Y₁]/(Y₁ - πY₀²)` on `D₊(T₁)` and
`D₊(T₂)`, where the partial derivative in `Y₁` is a unit. Flatness is torsion-freeness over the
discrete valuation ring: `π` is a nonzerodivisor on `R[T₀, T₁, T₂]/(T₁T₂ - πT₀²)`, because the
equation does not vanish modulo `π`, and so `π` is a nonzerodivisor on every degree-zero
localization.

## References

* [Stacks Project, Tag 0CA0](https://stacks.math.columbia.edu/tag/0CA0)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Models.GenusZero

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (a : R)

/-- The quadratic form `T₁T₂ - aT₀²`. -/
def conicEquation : MvPolynomial (Fin 3) R := X 1 * X 2 - C a * X 0 ^ 2

/-- The form `T₁T₂ - aT₀²` is homogeneous of degree `2`. -/
theorem isHomogeneous_conicEquation : (conicEquation a).IsHomogeneous 2 := by
  refine IsHomogeneous.sub ?_ ?_
  · simpa using (isHomogeneous_X R (1 : Fin 3)).mul (isHomogeneous_X R (2 : Fin 3))
  · simpa using (isHomogeneous_C (Fin 3) a).mul ((isHomogeneous_X R (0 : Fin 3)).pow 2)

/-- **The conic `X = V(T₁T₂ - aT₀²) ⊆ ℙ²_R`.** -/
abbrev conicScheme : Scheme.{u} :=
  PlaneCurveModel.scheme (conicEquation a) (isHomogeneous_conicEquation a)

/-- The structure morphism `X ⟶ Spec R`. -/
abbrev conicToSpec : conicScheme a ⟶ Spec (CommRingCat.of R) :=
  PlaneCurveModel.toSpec (conicEquation a) (isHomogeneous_conicEquation a)

/-- The ideal `(T₁T₂ - aT₀²)` of `R[T₀, T₁, T₂]`. -/
abbrev conicIdeal : Ideal (MvPolynomial (Fin 3) R) :=
  (PlaneCurveModel.equationIdeal (conicEquation a) (isHomogeneous_conicEquation a)).toIdeal

/-- The image of the coordinate `Tᵢ` in `R[T₀, T₁, T₂]/(T₁T₂ - aT₀²)`. -/
abbrev conicCoord (i : Fin 3) : MvPolynomial (Fin 3) R ⧸ conicIdeal a :=
  Ideal.Quotient.mk (conicIdeal a) (X i)

/-- The coordinate `T₀` does not divide `T₁T₂ - aT₀²`: the form is `1` at `(0 : 1 : 1)`. -/
theorem not_X_zero_dvd_conicEquation [Nontrivial R] :
    ¬ (X 0 : MvPolynomial (Fin 3) R) ∣ conicEquation a :=
  PlaneCurveModel.not_X_dvd_of_eval_ne_zero (conicEquation a) (v := ![0, 1, 1]) rfl
    (by simp [conicEquation])

/-- The image of `T₁T₂ - aT₀²` under a change of coefficients. -/
theorem map_conicEquation {S : Type u} [CommRing S] (φ : R →+* S) :
    MvPolynomial.map φ (conicEquation a) = conicEquation (φ a) := by
  simp [conicEquation]

/-! ### The chart equations -/

/-- The dehomogenization of `T₁T₂ - aT₀²` at `T₀` is the nodal equation `Y₀Y₁ - a`. -/
theorem dehomCoeff_conicEquation_zero :
    Stacks.ProjectiveChart.dehomCoeff R 0 (conicEquation a) = nodalEquation R a := by
  have h0 : finSuccEquiv' (0 : Fin 3) 0 = none := by decide
  have h1 : finSuccEquiv' (0 : Fin 3) 1 = some 0 := by decide
  have h2 : finSuccEquiv' (0 : Fin 3) 2 = some 1 := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, conicEquation, nodalEquation_def]
  simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-- The dehomogenization of `T₁T₂ - aT₀²` at `T₁` is `Y₁ - aY₀²`. -/
theorem dehomCoeff_conicEquation_one :
    Stacks.ProjectiveChart.dehomCoeff R 1 (conicEquation a) = X 1 - C a * X 0 ^ 2 := by
  have h0 : finSuccEquiv' (1 : Fin 3) 0 = some 0 := by decide
  have h1 : finSuccEquiv' (1 : Fin 3) 1 = none := by decide
  have h2 : finSuccEquiv' (1 : Fin 3) 2 = some 1 := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, conicEquation]
  simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-- The dehomogenization of `T₁T₂ - aT₀²` at `T₂` is `Y₁ - aY₀²`. -/
theorem dehomCoeff_conicEquation_two :
    Stacks.ProjectiveChart.dehomCoeff R 2 (conicEquation a) = X 1 - C a * X 0 ^ 2 := by
  have h0 : finSuccEquiv' (2 : Fin 3) 0 = some 0 := by decide
  have h1 : finSuccEquiv' (2 : Fin 3) 1 = some 1 := by decide
  have h2 : finSuccEquiv' (2 : Fin 3) 2 = none := by decide
  rw [Stacks.ProjectiveChart.dehomCoeff_eq_aeval, conicEquation]
  simp only [map_sub, map_mul, map_pow, aeval_X, aeval_C, h0, h1, h2,
    Option.elim_none, Option.elim_some, algebraMap_eq]
  ring

/-! ### The equation is prime -/

section Prime

variable {a} [IsDomain R] [UniqueFactorizationMonoid R]

/-- **`T₁T₂ - aT₀²` is a prime element of `R[T₀, T₁, T₂]`** for `R` a unique factorization domain
and `a ≠ 0`: as a polynomial in `T₂` it is `T₁ · T₂ - aT₀²`, of degree one with coprime
coefficients. -/
theorem prime_conicEquation (ha : a ≠ 0) : Prime (conicEquation a) := by
  let σ : Fin 3 ≃ Fin 3 := Equiv.swap 0 2
  let e := (renameEquiv R σ).trans (finSuccEquiv R 2)
  have hX0 : (X 0 : MvPolynomial (Fin 2) R) ≠ 0 := X_ne_zero 0
  have hndvd : ¬ (X 0 : MvPolynomial (Fin 2) R) ∣ -(C a * X 1 ^ 2) := by
    rintro ⟨g, hg⟩
    apply ha
    have hev := congrArg (MvPolynomial.eval ![0, 1]) hg
    simpa using hev
  have hrel : IsRelPrime (X 0 : MvPolynomial (Fin 2) R) (-(C a * X 1 ^ 2)) :=
    (MvPolynomial.X_prime (σ := Fin 2) (R := R) (i := 0)).irreducible.isRelPrime_iff_not_dvd.2
      hndvd
  have hirr : Prime
      (Polynomial.C (X 0 : MvPolynomial (Fin 2) R) * Polynomial.X +
        Polynomial.C (-(C a * X 1 ^ 2))) :=
    (UniqueFactorizationMonoid.irreducible_iff_prime
      (α := Polynomial (MvPolynomial (Fin 2) R))).1
      (Polynomial.irreducible_C_mul_X_add_C hX0 hrel)
  have he0 : e (X 0) = Polynomial.C (X 1) := by
    change finSuccEquiv R 2 (rename σ (X 0)) = _
    rw [rename_X, show σ 0 = Fin.succ 1 from rfl, finSuccEquiv_X_succ]
  have he1 : e (X 1) = Polynomial.C (X 0) := by
    change finSuccEquiv R 2 (rename σ (X 1)) = _
    rw [rename_X, show σ 1 = Fin.succ 0 from rfl, finSuccEquiv_X_succ]
  have he2 : e (X 2) = Polynomial.X := by
    change finSuccEquiv R 2 (rename σ (X 2)) = _
    rw [rename_X, show σ 2 = 0 from rfl, finSuccEquiv_X_zero]
  have heC : e (C a) = Polynomial.C (C a) := by
    change finSuccEquiv R 2 (rename σ (C a)) = _
    rw [rename_C]
    simpa using (finSuccEquiv R 2).commutes a
  have key : e (conicEquation a) =
      Polynomial.C (X 0 : MvPolynomial (Fin 2) R) * Polynomial.X +
        Polynomial.C (-(C a * X 1 ^ 2)) := by
    rw [conicEquation, map_sub, map_mul, map_mul, map_pow, he0, he1, he2, heC, map_neg,
      Polynomial.C_mul, Polynomial.C_pow]
    ring
  rw [← MulEquiv.prime_iff e.toMulEquiv, show e.toMulEquiv (conicEquation a) = _ from key]
  exact hirr

/-- The homogeneous coordinate ring `R[T₀, T₁, T₂]/(T₁T₂ - aT₀²)` is a domain. -/
theorem isDomain_conicRing (ha : a ≠ 0) :
    IsDomain (MvPolynomial (Fin 3) R ⧸
      (PlaneCurveModel.equationIdeal (conicEquation a) (isHomogeneous_conicEquation a)).toIdeal) :=
  have : (PlaneCurveModel.equationIdeal (conicEquation a)
      (isHomogeneous_conicEquation a)).toIdeal.IsPrime := by
    rw [PlaneCurveModel.toIdeal_equationIdeal]
    exact (Ideal.span_singleton_prime (prime_conicEquation ha).ne_zero).2 (prime_conicEquation ha)
  Ideal.Quotient.isDomain _

end Prime

/-! ### The charts cover the conic -/

/-- The images of the coordinates span the irrelevant ideal of `R[T₀, T₁, T₂]/(F)`. -/
theorem irrelevant_le_span_mk_X {F : MvPolynomial (Fin 3) R} {d : ℕ} (hF : F.IsHomogeneous d) :
    (HomogeneousIdeal.irrelevant (PlaneCurveModel.grading F hF)).toIdeal ≤
      Ideal.span (Set.range fun i : Fin 3 =>
        Ideal.Quotient.mk (PlaneCurveModel.equationIdeal F hF).toIdeal (X i)) := by
  refine (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr fun i hi x hx => ?_
  obtain ⟨p, hp, rfl⟩ := (Stacks.HomogeneousIdeal.mem_quotientGrading_iff _ x).1 hx
  have hspan := Stacks.AlgebraicGeometry.ProjPolyChart.homogeneous_mem_span_X R 2 hi hp
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk (PlaneCurveModel.equationIdeal F hF).toIdeal)
    hspan
  rwa [Ideal.map_span, ← Set.range_comp] at this

/-! ### Regularity -/

section Regular

variable {π : R} [IsDomain R] [IsDiscreteValuationRing R]

/-- `R[Y₀, Y₁]/(Y₁ - aY₀²)` is a regular ring: the partial derivative of the equation in `Y₁` is
`1`. -/
theorem isRegularRing_chart_one (a : R) :
    IsRegularRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {(X 1 - C a * X 0 ^ 2 :
      MvPolynomial (Fin 2) R)}) := by
  refine isRegularRing_quotient_span_singleton_of_forall_notMem_sq _ ?_
  intro p hp hfp
  refine notMem_sq_of_derivation ((MvPolynomial.pderiv (R := R) 1).restrictScalars ℤ) ?_
  change (MvPolynomial.pderiv (R := R) 1) (X 1 - C a * X 0 ^ 2) ∉ p
  have hd : (MvPolynomial.pderiv (R := R) 1) (X 1 - C a * X 0 ^ 2 :
      MvPolynomial (Fin 2) R) = 1 := by
    simp [pderiv_X]
  rw [hd]
  exact fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)

/-- **The conic `V(T₁T₂ - πT₀²) ⊆ ℙ²_R` is regular**, for `π` a uniformizer of a discrete
valuation ring. Its three standard charts have regular rings. -/
theorem isRegular_conicScheme (hπ : Irreducible π) : IsRegular (conicScheme π) := by
  intro x
  have hx : x ∈ (⨆ k : Fin 3, PlaneCurveModel.chart (conicEquation π)
      (isHomogeneous_conicEquation π) k) := by
    rw [PlaneCurveModel.iSup_chart_eq_top]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨⟨_, PlaneCurveModel.isAffineOpen_chart (conicEquation π)
    (isHomogeneous_conicEquation π) k⟩, hk, ?_⟩
  have hreg : IsRegularRing (MvPolynomial (Fin 2) R ⧸
      Ideal.span {Stacks.ProjectiveChart.dehomCoeff R k (conicEquation π)}) := by
    obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
    · rw [dehomCoeff_conicEquation_zero]
      exact isRegularRing_nodalChartRing hπ
    · rw [dehomCoeff_conicEquation_one]
      exact isRegularRing_chart_one π
    · rw [dehomCoeff_conicEquation_two]
      exact isRegularRing_chart_one π
  exact IsRegularRing.of_ringEquiv (PlaneCurveModel.chartEquiv (conicEquation π)
    (isHomogeneous_conicEquation π) 0 (not_X_zero_dvd_conicEquation π) k)

end Regular

/-! ### Flatness -/

section Flat

variable {π : R} [IsDomain R] [IsDiscreteValuationRing R]

/-- A module over a discrete valuation ring on which a uniformizer acts injectively is
torsion-free. -/
theorem isTorsionFree_of_uniformizer {M : Type*} [AddCommGroup M] [Module R M]
    (hπ : Irreducible π) (h : ∀ m : M, π • m = 0 → m = 0) : Module.IsTorsionFree R M where
  isSMulRegular r hr := by
    have hπreg : IsSMulRegular M π := fun x y hxy => by
      have := h (x - y) (by rw [smul_sub, sub_eq_zero]; exact hxy)
      exact sub_eq_zero.mp this
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (hr.ne_zero) hπ
    rw [hu]
    exact (u.isUnit.isSMulRegular M).mul (hπreg.pow n)

/-- **A uniformizer is a nonzerodivisor on `R[T₀, T₁, T₂]/(T₁T₂ - πT₀²)`.** If `π p = F h`, then
reducing modulo `π` gives `T₁T₂ h̄ = 0`, so `π` divides `h` and `F` divides `p`. -/
theorem mk_C_mul_eq_zero (hπ : Irreducible π) (x : MvPolynomial (Fin 3) R ⧸
    (PlaneCurveModel.equationIdeal (conicEquation π) (isHomogeneous_conicEquation π)).toIdeal)
    (hx : Ideal.Quotient.mk _ (C π) * x = 0) : x = 0 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, PlaneCurveModel.toIdeal_equationIdeal,
    Ideal.mem_span_singleton] at hx
  obtain ⟨h, hh⟩ := hx
  let res := IsLocalRing.residue R
  have hmap := congrArg (MvPolynomial.map res) hh
  have hres0 : res π = 0 := (IsLocalRing.residue_eq_zero_iff π).2 hπ.not_isUnit
  rw [map_mul, map_mul, map_C, map_conicEquation, hres0, map_zero, zero_mul] at hmap
  simp only [conicEquation, map_zero, zero_mul, sub_zero] at hmap
  have hne : (X 1 * X 2 : MvPolynomial (Fin 3) (IsLocalRing.ResidueField R)) ≠ 0 :=
    mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have hh0 : MvPolynomial.map res h = 0 := (mul_eq_zero.mp hmap.symm).resolve_left hne
  have hker : h ∈ RingHom.ker (MvPolynomial.map res : MvPolynomial (Fin 3) R →+* _) := hh0
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue, hπ.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Ideal.mem_span_singleton] at hker
  obtain ⟨h', rfl⟩ := hker
  have hCπ : (C π : MvPolynomial (Fin 3) R) ≠ 0 := by
    rw [Ne, C_eq_zero]; exact hπ.ne_zero
  have hp : p = conicEquation π * h' := by
    apply mul_left_cancel₀ hCπ
    rw [hh]; ring
  rw [Ideal.Quotient.eq_zero_iff_mem, PlaneCurveModel.toIdeal_equationIdeal, hp]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- The chart rings of the conic are flat over the discrete valuation ring. -/
theorem flat_chart (hπ : Irreducible π) (i : Fin 3) :
    RingHom.Flat ((HomogeneousLocalization.fromZeroRingHom
      (PlaneCurveModel.grading (conicEquation π) (isHomogeneous_conicEquation π))
      (Submonoid.powers (conicCoord π i))).comp
      (PlaneCurveModel.toGradingZero (conicEquation π) (isHomogeneous_conicEquation π))) := by
  set φ := (HomogeneousLocalization.fromZeroRingHom
      (PlaneCurveModel.grading (conicEquation π) (isHomogeneous_conicEquation π))
      (Submonoid.powers (conicCoord π i))).comp
      (PlaneCurveModel.toGradingZero (conicEquation π) (isHomogeneous_conicEquation π))
  let _ := φ.toAlgebra
  suffices Module.IsTorsionFree R (HomogeneousLocalization.Away
      (PlaneCurveModel.grading (conicEquation π) (isHomogeneous_conicEquation π))
      (conicCoord π i)) from
    RingHom.flat_algebraMap_iff.mpr inferInstance
  refine isTorsionFree_of_uniformizer hπ fun y hy => ?_
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero]
  have hy' := congrArg HomogeneousLocalization.val hy
  rw [Algebra.smul_def, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero] at hy'
  have hφ : (algebraMap R (HomogeneousLocalization.Away
      (PlaneCurveModel.grading (conicEquation π) (isHomogeneous_conicEquation π))
      (conicCoord π i)) π).val =
      algebraMap _ (Localization.Away (conicCoord π i))
        (Ideal.Quotient.mk (conicIdeal π) (C π)) := by
    change (HomogeneousLocalization.mk ⟨0, PlaneCurveModel.toGradingZero _ _ π, 1,
      one_mem _⟩).val = _
    rw [HomogeneousLocalization.val_mk]
    exact Localization.mk_one_eq_algebraMap _
  rw [hφ] at hy'
  generalize y.val = z at hy' ⊢
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (conicCoord π i)) z
  rw [← IsLocalization.mk'_one (M := Submonoid.powers (conicCoord π i))
    (Localization.Away (conicCoord π i)), ← IsLocalization.mk'_mul, one_mul,
    IsLocalization.mk'_eq_zero_iff] at hy'
  obtain ⟨c, hc⟩ := hy'
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨c, mk_C_mul_eq_zero hπ _ ?_⟩
  rw [← hc]; ring

/-- **The conic is flat over the discrete valuation ring.** -/
theorem flat_conicToSpec (hπ : Irreducible π) : Flat (conicToSpec π) := by
  unfold conicToSpec
  rw [PlaneCurveModel.toSpec_eq]
  exact AlgebraicGeometry.Proj.flat_toSpecZero_comp_of_flat_away' _
    (CommRingCat.ofHom (PlaneCurveModel.toGradingZero (conicEquation π)
      (isHomogeneous_conicEquation π)))
    (fun i : Fin 3 => conicCoord π i) (fun _ => 1) (fun _ => one_pos)
    (fun i => Stacks.HomogeneousIdeal.mk_mem_quotientGrading _
      ((mem_homogeneousSubmodule _ _).2 (isHomogeneous_X R i)))
    (irrelevant_le_span_mk_X _) (flat_chart hπ)

end Flat

end Stacks.Models.GenusZero

end
