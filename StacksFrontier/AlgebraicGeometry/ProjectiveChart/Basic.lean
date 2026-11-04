module

public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Away
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import StacksCore.Tactic.StacksAttribute

/-!
# The standard charts of projective space are affine spaces

Projective `n`-space over a commutative ring `R` is `Proj` of the polynomial ring
`R[T₀, …, Tₙ]` with its total-degree grading. The homogeneous coordinates `Tᵢ` cut out the
standard opens `D₊(Tᵢ)`, and this file proves the two halves of Tag 01NG: the `D₊(Tᵢ)` cover
`Proj`, and each one is affine `n`-space.

The geometric statement rests on a purely ring-theoretic identification, which is isolated here
as a named declaration because it is what consumers actually need: the degree-zero homogeneous
localization `R[T₀, …, Tₙ]_{(Tᵢ)}` is a polynomial ring in `n` variables over `R`. The map sends
the `j`-th affine coordinate to the ratio `T_{σ j} / Tᵢ`, where `σ = Fin.succAbove i` enumerates
the coordinates other than the `i`-th in their natural order. Surjectivity is Mathlib's
`HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top` applied to the coordinate variables;
injectivity comes from an explicit left inverse, dehomogenization, which sets `Tᵢ = 1` and is
built by `IsLocalization.Away.lift`.

Being a ring isomorphism, that identification transports every property of a polynomial ring to
the chart ring. The ones recorded here are the three a divisor-theoretic argument needs — domain,
Noetherian, and unique factorization — both for the chart ring itself and, through Mathlib's
`Proj.basicOpenIsoAway`, for the sections `Γ(Proj R[T₀, …, Tₙ], D₊(Tᵢ))`. Without them the chart
ring is not even known to be a domain.

## Main definitions

* `Stacks.ProjectiveChart.degreeZeroEquiv`: the degree-zero graded piece of a polynomial ring is
  its coefficient ring.
* `Stacks.ProjectiveChart.chartRingEquiv`: **the chart identification** — the `i`-th chart ring
  of projective `n`-space over `R` is `R[Y₁, …, Yₙ]`.
* `Stacks.ProjectiveChart.sectionsChartEquiv`: the same identification read on sections of the
  structure sheaf.
* `Stacks.ProjectiveChart.chartIsoAffineSpace`: each standard open is affine `n`-space, for any
  index type equivalent to `Fin n`.

## Main results

* `Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top`: the coordinate standard opens cover
  projective space.
* `Stacks.ProjectiveChart.basicOpen_X_iso_affineSpace`: each coordinate standard open is affine
  `n`-space.
* `Stacks.ProjectiveChart.uniqueFactorizationMonoid_chartRing` and
  `Stacks.ProjectiveChart.uniqueFactorizationMonoid_sections`: the chart ring and its ring of
  sections are unique factorization domains when `R` is.

## Implementation notes

The affine coordinates are indexed by `Fin n` while `AlgebraicGeometry.AffineSpace` wants an
index type in the same universe as the base. `chartIsoAffineSpace` therefore takes the index type
and an equivalence to `Fin n` as parameters, so that it covers both `Fin n` over a base in
`Type 0` and `ULift (Fin n)` over a base in `Type u`;
`basicOpen_X_iso_affineSpace` is the `Fin n` case.

The three transfer statements are deliberately theorems rather than instances: the grading they
are stated over is itself only a local instance here, following the convention of the
neighbouring files, so instance search could not use them in a consumer that had not already
introduced the grading.

## References

* [Stacks Project, Tag 01NG](https://stacks.math.columbia.edu/tag/01NG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveChart

universe u

variable (R : Type u) [CommRing R]

/-- Each coordinate variable is homogeneous of degree one. -/
theorem X_mem_degree_one {n : ℕ} (k : Fin (n + 1)) :
    MvPolynomial.X k ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 1 := by
  simpa only [MvPolynomial.mem_homogeneousSubmodule] using
    (MvPolynomial.isHomogeneous_X R k)

/-- Degree-zero homogeneous polynomials are the constants. -/
noncomputable def degreeZeroEquiv (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) ≃+* R where
  toFun x := MvPolynomial.eval (fun _ => 0) x.1
  invFun z := ⟨MvPolynomial.C z,
    (MvPolynomial.mem_homogeneousSubmodule 0 (MvPolynomial.C z)).2
      (MvPolynomial.isHomogeneous_C (Fin (n + 1)) z)⟩
  left_inv x := by
    apply Subtype.ext
    have hx : x.1.totalDegree = 0 :=
      (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).2 x.2
    rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hx]
    simp [MvPolynomial.constantCoeff_eq]
  right_inv z := by
    change MvPolynomial.eval (fun _ => 0) (MvPolynomial.C z) = z
    simp
  map_mul' x y := by simp
  map_add' x y := by simp

/-- `degreeZeroEquiv` evaluates a degree-zero polynomial at the origin. -/
theorem degreeZeroEquiv_apply {n : ℕ}
    (x : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) :
    degreeZeroEquiv R n x = MvPolynomial.eval (fun _ => 0) x.1 := rfl

/-- A degree-zero homogeneous polynomial is the constant `degreeZeroEquiv R n x`. -/
theorem coe_eq_C_degreeZeroEquiv {n : ℕ}
    (x : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) :
    (x : MvPolynomial (Fin (n + 1)) R) = MvPolynomial.C (degreeZeroEquiv R n x) := by
  have hx : x.1.totalDegree = 0 :=
    (MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1))).2 x.2
  rw [(MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp hx]
  simp [degreeZeroEquiv_apply, MvPolynomial.constantCoeff_eq]

/-- Notation: the degree-zero part of the polynomial ring. -/
abbrev Deg0 (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0

/-- The chart ring: degree-zero homogeneous localization at the `i`-th coordinate. -/
abbrev ChartRing (n : ℕ) (i : Fin (n + 1)) :=
  HomogeneousLocalization.Away
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)

/-- The ratio `X k / X i`, an element of the `i`-th chart ring. -/
noncomputable def ratio {n : ℕ} (i k : Fin (n + 1)) : ChartRing R n i :=
  HomogeneousLocalization.Away.isLocalizationElem
    (X_mem_degree_one R i) (X_mem_degree_one R k)

/-- The chart comparison: send the `j`-th affine coordinate to `X (i.succAbove j) / X i`. -/
noncomputable def chartHom {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin n) (Deg0 R n) →ₐ[Deg0 R n] ChartRing R n i :=
  MvPolynomial.aeval (fun j => ratio R i (i.succAbove j))

/-- The ratio `X i / X i` is `1`. -/
theorem ratio_self {n : ℕ} (i : Fin (n + 1)) : ratio R i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one]
  simp only [ratio, HomogeneousLocalization.Away.isLocalizationElem,
    pow_one, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk']
  exact IsLocalization.mk'_self' (M := Submonoid.powers
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
    (S := Localization.Away (MvPolynomial.X i))
    (x := ⟨MvPolynomial.X i, ⟨1, pow_one _⟩⟩)

/-- The ratio `X k / X i` is `1` when `k = i`, and otherwise `chartHom R i (X j)` for the affine
coordinate `j` with `k = i.succAbove j`. -/
theorem ratio_eq {n : ℕ} (i k : Fin (n + 1)) :
    ratio R i k =
      (finSuccEquiv' i k).elim 1 (fun j => chartHom R i (MvPolynomial.X j)) := by
  cases h : finSuccEquiv' i k with
  | none =>
      have hk : k = i := ((finSuccEquiv'_eq_none).mp h).symm
      subst k
      simp [ratio_self]
  | some j =>
      have hk : k = i.succAbove j := by
        apply (finSuccEquiv'_eq_some).mp
        simp [h]
      subst k
      simp [chartHom]


/-- Dehomogenization on polynomials: set the `i`-th variable to `1`. -/
noncomputable def dehomPolynomial {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) R →+* MvPolynomial (Fin n) (Deg0 R n) :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : Deg0 R n →+* MvPolynomial (Fin n) (Deg0 R n)).comp
      (degreeZeroEquiv R n).symm.toRingHom)
    (fun k => (finSuccEquiv' i k).elim 1 MvPolynomial.X)

/-- Dehomogenization at `i` sends the `i`-th variable to a unit. -/
theorem dehomPolynomial_X_self {n : ℕ} (i : Fin (n + 1)) :
    IsUnit (dehomPolynomial R i (MvPolynomial.X i)) := by
  simp [dehomPolynomial, finSuccEquiv']

/-- Dehomogenization on the chart ring, inverse to `chartHom`. -/
noncomputable def dehom {n : ℕ} (i : Fin (n + 1)) :
    ChartRing R n i →+* MvPolynomial (Fin n) (Deg0 R n) :=
  (IsLocalization.Away.lift
    (R := MvPolynomial (Fin (n + 1)) R)
    (S := Localization.Away (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
    (P := MvPolynomial (Fin n) (Deg0 R n))
    (x := (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R))
    (g := dehomPolynomial R i) (dehomPolynomial_X_self R i)).comp
    (algebraMap (ChartRing R n i) (Localization.Away
      (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R)))

/-- The chart ring is generated by the ratios `X k / X i`, so `chartHom` is surjective. -/
theorem chartHom_surjective {n : ℕ} (i : Fin (n + 1)) :
    Function.Surjective (chartHom R i) := by
  classical
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (X_mem_degree_one R i) (Fin (n + 1))
    (MvPolynomial.X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top R n) (fun _ => 1)
    (X_mem_degree_one R)]
  apply Algebra.adjoin_le_iff.mpr
  rintro z ⟨a, ai, hai, hle, rfl⟩
  refine ⟨∏ k : Fin (n + 1), ((finSuccEquiv' i k).elim 1 MvPolynomial.X) ^ ai k, ?_⟩
  have hp : chartHom R i (∏ k : Fin (n + 1),
      ((finSuccEquiv' i k).elim 1 MvPolynomial.X) ^ ai k)
      = ∏ k : Fin (n + 1), ratio R i k ^ ai k := by
    simp only [map_prod, map_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ratio_eq R i k]
    rcases finSuccEquiv' i k with _ | j <;> simp
  show chartHom R i _ = _
  rw [hp]
  have hai' : ∑ k : Fin (n + 1), ai k = a := by simpa using hai
  apply HomogeneousLocalization.val_injective
  rw [← HomogeneousLocalization.algebraMap_apply]
  rw [map_prod (algebraMap (ChartRing R n i)
      (Localization.Away (MvPolynomial.X i)))
    (fun k => ratio R i k ^ ai k) Finset.univ]
  simp only [map_pow, HomogeneousLocalization.algebraMap_apply, ratio,
    HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, Localization.mk_pow, Localization.mk_prod]
  congr 1
  · simp
  · apply Subtype.ext
    simp [Finset.prod_pow_eq_pow_sum, hai']


/-- Dehomogenization is a left inverse of `chartHom`. -/
theorem dehom_comp_chartHom {n : ℕ} (i : Fin (n + 1)) :
    (dehom R i).comp (chartHom R i).toRingHom = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    show dehom R i (chartHom R i (MvPolynomial.C r)) = MvPolynomial.C r
    rw [show (chartHom R i) (MvPolynomial.C r)
        = algebraMap (Deg0 R n) (ChartRing R n i) r from MvPolynomial.aeval_C _ _]
    dsimp only [dehom, RingHom.coe_comp, Function.comp_apply]
    rw [HomogeneousLocalization.algebraMap_eq]
    show (IsLocalization.Away.lift (x := MvPolynomial.X i)
      (g := dehomPolynomial R i) (dehomPolynomial_X_self R i))
      (Localization.mk r.1 (1 : Submonoid.powers (MvPolynomial.X i)))
      = MvPolynomial.C r
    rw [Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]
    show dehomPolynomial R i r.1 = MvPolynomial.C r
    rw [coe_eq_C_degreeZeroEquiv R r]
    simp only [dehomPolynomial, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
      RingEquiv.symm_apply_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  · intro j
    show dehom R i (chartHom R i (MvPolynomial.X j)) = MvPolynomial.X j
    rw [show (chartHom R i) (MvPolynomial.X j) = ratio R i (i.succAbove j) from
      MvPolynomial.aeval_X _ _]
    simp [dehom, dehomPolynomial, ratio, HomogeneousLocalization.algebraMap_apply,
      IsLocalization.Away.lift, IsLocalization.lift_mk', IsUnit.liftRight_apply,
      Localization.mk_eq_mk']

/-- `chartHom` is injective, since dehomogenization is a left inverse. -/
theorem chartHom_injective {n : ℕ} (i : Fin (n + 1)) :
    Function.Injective (chartHom R i) := by
  refine Function.LeftInverse.injective (g := dehom R i) fun x => ?_
  exact DFunLike.congr_fun (dehom_comp_chartHom R i) x

/-- `chartHom` is bijective. -/
theorem chartHom_bijective {n : ℕ} (i : Fin (n + 1)) :
    Function.Bijective (chartHom R i) :=
  ⟨chartHom_injective R i, chartHom_surjective R i⟩

/-- The `i`-th chart ring of projective `n`-space over `R`, as a polynomial ring over the
degree-zero part. -/
noncomputable def chartRingEquivDeg0 {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin n) (Deg0 R n) ≃+* ChartRing R n i :=
  RingEquiv.ofBijective (chartHom R i).toRingHom (chartHom_bijective R i)

/-- **The `i`-th standard chart of projective `n`-space over `R` is a polynomial ring in `n`
variables over `R`.** -/
noncomputable def chartRingEquiv {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin n) R ≃+* ChartRing R n i :=
  (MvPolynomial.mapEquiv (Fin n) (degreeZeroEquiv R n).symm).trans
    (chartRingEquivDeg0 R i)


section Transfer

variable {R}

/-- The chart ring over a domain is a domain. -/
theorem isDomain_chartRing [IsDomain R] {n : ℕ} (i : Fin (n + 1)) :
    IsDomain (ChartRing R n i) :=
  MulEquiv.isDomain (MvPolynomial (Fin n) R) (chartRingEquiv R i).symm.toMulEquiv

/-- The chart ring over a Noetherian ring is Noetherian. -/
theorem isNoetherianRing_chartRing [IsNoetherianRing R] {n : ℕ} (i : Fin (n + 1)) :
    IsNoetherianRing (ChartRing R n i) :=
  isNoetherianRing_of_ringEquiv _ (chartRingEquiv R i)

/-- The chart ring over a unique factorization domain is a unique factorization domain. -/
theorem uniqueFactorizationMonoid_chartRing [IsDomain R] [UniqueFactorizationMonoid R]
    {n : ℕ} (i : Fin (n + 1)) : UniqueFactorizationMonoid (ChartRing R n i) :=
  have : IsDomain (ChartRing R n i) := isDomain_chartRing i
  (chartRingEquiv R i).toMulEquiv.uniqueFactorizationMonoid
    (MvPolynomial.uniqueFactorizationMonoid (Fin n))

/-- The sections of projective space over the `i`-th standard open, as a polynomial ring. -/
noncomputable def sectionsChartEquiv (R : Type u) [CommRing R] {n : ℕ} (i : Fin (n + 1)) :
    MvPolynomial (Fin n) R ≃+*
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X i)) :=
  (chartRingEquiv R i).trans
    (Proj.basicOpenIsoAway (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i) (X_mem_degree_one R i)
      (by omega)).commRingCatIsoToRingEquiv

/-- The sections of projective space over a standard open are a domain when `R` is. -/
theorem isDomain_sections [IsDomain R] {n : ℕ} (i : Fin (n + 1)) :
    IsDomain Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i)) :=
  MulEquiv.isDomain (MvPolynomial (Fin n) R) (sectionsChartEquiv R i).symm.toMulEquiv

/-- The sections of projective space over a standard open are Noetherian when `R` is. -/
theorem isNoetherianRing_sections [IsNoetherianRing R] {n : ℕ} (i : Fin (n + 1)) :
    IsNoetherianRing Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i)) :=
  isNoetherianRing_of_ringEquiv _ (sectionsChartEquiv R i)

/-- The sections of projective space over a standard open are a unique factorization domain
when `R` is. -/
theorem uniqueFactorizationMonoid_sections [IsDomain R] [UniqueFactorizationMonoid R]
    {n : ℕ} (i : Fin (n + 1)) :
    UniqueFactorizationMonoid
      Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.X i)) :=
  have : IsDomain (MvPolynomial (Fin n) R) := inferInstance
  (sectionsChartEquiv R i).toMulEquiv.uniqueFactorizationMonoid
    (MvPolynomial.uniqueFactorizationMonoid (Fin n))

end Transfer

section Tags

/-- The homogeneous coordinate standard opens cover projective space. -/
@[stacks 01NG "standard-open covering"]
theorem iSup_basicOpen_X_eq_top (n : ℕ) :
    (⨆ i : Fin (n + 1),
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X i)) = ⊤ := by
  classical
  exact Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, MvPolynomial.isHomogeneous_X R i⟩)
    (Stacks.AlgebraicGeometry.ProjPolyChart.adjoin_range_X_eq_top R n)

/-- The standard open at a homogeneous coordinate is affine `n`-space over `R`, for any
index type equivalent to `Fin n`. -/
noncomputable def chartIsoAffineSpace (n : ℕ) (i : Fin (n + 1)) {ι : Type u}
    (e : ι ≃ Fin n) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.X i)).toScheme ≅ AffineSpace ι (Spec (.of R)) :=
  (Proj.basicOpenIsoSpec
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X i)
      (X_mem_degree_one R i) (by omega)).trans
    ((Scheme.Spec.mapIso
        ((MvPolynomial.renameEquiv R e).toRingEquiv.trans
          (chartRingEquiv R i)).toCommRingCatIso.op).trans
      (AffineSpace.SpecIso ι (.of R)).symm)

/-- The standard open at a homogeneous coordinate is affine `n`-space. -/
@[stacks 01NG "affine-space charts"]
noncomputable def basicOpen_X_iso_affineSpace (A : Type) [CommRing A] (n : ℕ)
    (i : Fin (n + 1)) :
    (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)
      (MvPolynomial.X i)).toScheme ≅ AffineSpace (Fin n) (Spec (.of A)) :=
  chartIsoAffineSpace A n i (Equiv.refl _)

end Tags

end Stacks.ProjectiveChart



end
