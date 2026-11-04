module

public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Scheme.ProjectiveGeneralLinearTwo
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroupSmooth
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeOverField

/-!
# `PGL₂` has dimension three

Let `k` be a field. The coordinate ring of `PGL₂` is a domain of finite type over `k`, so by
[Stacks, Tag 00P0] its Krull dimension is the transcendence degree of its fraction field, and the
same holds for every localization at a nonzero element. The chart `D(g_{(0,0)})` is the ring
`k[β, γ, δ, 1/(δ - β γ)]` of invertible matrices with upper left entry `1`: the chart matrix
`N^{(0,0)}` and the matrix `(1 β; γ δ)` give mutually inverse ring maps. That ring is a
localization of the polynomial ring in three variables, of dimension three.

## Main results

* `AlgebraicGeometry.ringKrullDim_localization_away_eq`: for a finite type domain over a field,
  inverting a nonzero element does not change the Krull dimension.
* `AlgebraicGeometry.projectiveGeneralLinearTwoChartEquiv`: the chart `D(g_{(0,0)})` is
  `k[β, γ, δ, 1/(δ - β γ)]`.
* `AlgebraicGeometry.ringKrullDim_projectiveGeneralLinearTwoRing`: the coordinate ring of `PGL₂`
  has Krull dimension three.
* `AlgebraicGeometry.topologicalKrullDim_projectiveGeneralLinearTwoScheme`: **`PGL₂` has
  dimension three.**

## References

* [Stacks Project, Tag 00P0](https://stacks.math.columbia.edu/tag/00P0)
* [Stacks Project, Tag 0DSV](https://stacks.math.columbia.edu/tag/0DSV)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- **Inverting a nonzero element of a finite type domain over a field does not change its Krull
dimension**: by [Stacks, Tag 00P0] both dimensions are the transcendence degree of the common
fraction field. -/
theorem ringKrullDim_localization_away_eq (S : Type u) [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] {g : S} (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim S := by
  have hle : Submonoid.powers g ≤ nonZeroDivisors S :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg
  have : IsDomain (Localization.Away g) := IsLocalization.isDomain_localization hle
  let : Algebra (Localization.Away g) (FractionRing S) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ (Submonoid.powers g) (nonZeroDivisors S) hle
  have : IsScalarTower S (Localization.Away g) (FractionRing S) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  have : IsFractionRing (Localization.Away g) (FractionRing S) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers g) _ _
  have : IsScalarTower k (Localization.Away g) (FractionRing S) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply k S (Localization.Away g),
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [(ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, u} k S
    (FractionRing S)).1,
    (ringKrullDim_eq_trdeg_and_ringKrullDim_localization_eq_trdeg.{u, u, u, u} k
        (Localization.Away g)
      (FractionRing S)).1]

/-! ### The chart `D(g_{(0,0)})` -/

/-- The determinant `δ - β γ` of the matrix `(1 β; γ δ)`, in `k[β, γ, δ]`. -/
abbrev projectiveGeneralLinearTwoChartDet : MvPolynomial (Fin 3) k := X 2 - X 0 * X 1

/-- The ring `k[β, γ, δ, 1/(δ - β γ)]` of invertible matrices with upper left entry `1`. -/
abbrev projectiveGeneralLinearTwoChartModel := Localization.Away
    (projectiveGeneralLinearTwoChartDet k)

/-- The matrix `(1 β; γ δ)` over `k[β, γ, δ, 1/(δ - β γ)]`. -/
def projectiveGeneralLinearTwoModelMatrix :
    Matrix (Fin 2) (Fin 2) (projectiveGeneralLinearTwoChartModel k) :=
  let ι := algebraMap (MvPolynomial (Fin 3) k) (projectiveGeneralLinearTwoChartModel k)
  !![1, ι (X 0); ι (X 1), ι (X 2)]

/-- The determinant of the matrix `(1 β; γ δ)` is the image of `δ - β γ`. -/
theorem projectiveGeneralLinearTwoModelMatrix_det :
    (projectiveGeneralLinearTwoModelMatrix k).det =
      algebraMap _ (projectiveGeneralLinearTwoChartModel k)
          (projectiveGeneralLinearTwoChartDet k) := by
  simp [projectiveGeneralLinearTwoModelMatrix, Matrix.det_fin_two_of]

/-- The matrix `(1 β; γ δ)` is invertible over `k[β, γ, δ, 1/(δ - β γ)]`. -/
theorem isUnit_projectiveGeneralLinearTwoModelMatrix_det :
    IsUnit (projectiveGeneralLinearTwoModelMatrix k).det := by
  rw [projectiveGeneralLinearTwoModelMatrix_det]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The ring map `ev_{(1 β; γ δ)}` out of the coordinate ring of `PGL₂`. -/
abbrev projectiveGeneralLinearTwoToModel :
    projectiveGeneralLinearTwoRing k →+* projectiveGeneralLinearTwoChartModel k :=
  projectiveGeneralLinearTwoEval (algebraMap k _) (projectiveGeneralLinearTwoModelMatrix k)
    (isUnit_projectiveGeneralLinearTwoModelMatrix_det k)

/-- The image of the chart element `g_{(0,0)}` under `ev_{(1 β; γ δ)}`, times the determinant of
`(1 β; γ δ)`, is `1`. -/
theorem projectiveGeneralLinearTwoToModel_chartElement_mul_det :
    projectiveGeneralLinearTwoToModel k (projectiveGeneralLinearTwoChartElement k (0, 0)) *
      (projectiveGeneralLinearTwoModelMatrix k).det = 1 := by
  rw [projectiveGeneralLinearTwoEval_element_mul_det]
  simp [projectiveGeneralLinearTwoModelMatrix]

/-- The image of the chart element `g_{(0,0)}` under `ev_{(1 β; γ δ)}` is a unit. -/
theorem isUnit_projectiveGeneralLinearTwoToModel_chartElement :
    IsUnit (projectiveGeneralLinearTwoToModel k
        (projectiveGeneralLinearTwoChartElement k (0, 0))) :=
  IsUnit.of_mul_eq_one _ (projectiveGeneralLinearTwoToModel_chartElement_mul_det k)

/-- The chart map `D(g_{(0,0)}) ⟶ k[β, γ, δ, 1/(δ - β γ)]`. -/
def projectiveGeneralLinearTwoChartToModel :
    projectiveGeneralLinearTwoChartRing k (0, 0) →+* projectiveGeneralLinearTwoChartModel k :=
  IsLocalization.Away.lift _ (isUnit_projectiveGeneralLinearTwoToModel_chartElement k)

/-- The map `k[β, γ, δ] ⟶ D(g_{(0,0)})` sending `(β, γ, δ)` to the entries of `N^{(0,0)}`. -/
def projectiveGeneralLinearTwoPolynomialToChart :
    MvPolynomial (Fin 3) k →+* projectiveGeneralLinearTwoChartRing k (0, 0) :=
  eval₂Hom (projectiveGeneralLinearTwoChartStructure k (0, 0))
    ![projectiveGeneralLinearTwoChartMatrix k (0, 0) 0 1,
      projectiveGeneralLinearTwoChartMatrix k (0, 0) 1 0,
      projectiveGeneralLinearTwoChartMatrix k (0, 0) 1 1]

/-- The map `k[β, γ, δ] ⟶ D(g_{(0,0)})` sends `δ - β γ` to the determinant of the chart matrix
`N^{(0,0)}`. -/
theorem projectiveGeneralLinearTwoPolynomialToChart_det :
    projectiveGeneralLinearTwoPolynomialToChart k (projectiveGeneralLinearTwoChartDet k) =
      (projectiveGeneralLinearTwoChartMatrix k (0, 0)).det := by
  have h1 := projectiveGeneralLinearTwoChartMatrix_self k (0, 0)
  simp only [projectiveGeneralLinearTwoPolynomialToChart, projectiveGeneralLinearTwoChartDet,
    map_sub, map_mul, eval₂Hom_X', Matrix.cons_val, Matrix.det_fin_two]
  rw [show projectiveGeneralLinearTwoChartMatrix k (0, 0) 0 0 = 1 from h1]
  simp

/-- The model map `k[β, γ, δ, 1/(δ - β γ)] ⟶ D(g_{(0,0)})`. -/
def projectiveGeneralLinearTwoModelToChart :
    projectiveGeneralLinearTwoChartModel k →+* projectiveGeneralLinearTwoChartRing k (0, 0) :=
  IsLocalization.Away.lift (projectiveGeneralLinearTwoChartDet k)
    (g := projectiveGeneralLinearTwoPolynomialToChart k) (by
      rw [projectiveGeneralLinearTwoPolynomialToChart_det]
      exact isUnit_projectiveGeneralLinearTwoChartMatrix_det k (0, 0))

/-- The model map `k[β, γ, δ, 1/(δ - β γ)] ⟶ D(g_{(0,0)})` is compatible with the structure maps
from `k`. -/
theorem projectiveGeneralLinearTwoModelToChart_algebraMap (r : k) :
    projectiveGeneralLinearTwoModelToChart k (algebraMap k _ r) =
      projectiveGeneralLinearTwoChartStructure k (0, 0) r := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 3) k),
    projectiveGeneralLinearTwoModelToChart,
    IsLocalization.Away.lift_eq, projectiveGeneralLinearTwoPolynomialToChart, algebraMap_eq,
    eval₂Hom_C]

/-- The model map sends `β`, `γ`, `δ` to the entries `N^{(0,0)}_{01}`, `N^{(0,0)}_{10}`,
`N^{(0,0)}_{11}` of the chart matrix. -/
theorem projectiveGeneralLinearTwoModelToChart_X (i : Fin 3) :
    projectiveGeneralLinearTwoModelToChart k
        (algebraMap (MvPolynomial (Fin 3) k) (projectiveGeneralLinearTwoChartModel k) (X i)) =
      ![projectiveGeneralLinearTwoChartMatrix k (0, 0) 0 1,
        projectiveGeneralLinearTwoChartMatrix k (0, 0) 1 0,
        projectiveGeneralLinearTwoChartMatrix k (0, 0) 1 1] i := by
  rw [projectiveGeneralLinearTwoModelToChart, IsLocalization.Away.lift_eq,
    projectiveGeneralLinearTwoPolynomialToChart, eval₂Hom_X']

/-- The chart map followed by the model map is the identity of `D(g_{(0,0)})`. -/
theorem projectiveGeneralLinearTwoModelToChart_comp_toChart :
    (projectiveGeneralLinearTwoModelToChart k).comp (projectiveGeneralLinearTwoChartToModel k) =
      RingHom.id _ := by
  refine IsLocalization.ringHom_ext
      (Submonoid.powers (projectiveGeneralLinearTwoChartElement k (0, 0)))
    ?_
  rw [RingHom.id_comp, RingHom.comp_assoc, projectiveGeneralLinearTwoChartToModel,
    IsLocalization.Away.lift_comp, projectiveGeneralLinearTwoEval_naturality _ _ _ _
      (by
        have e : ((projectiveGeneralLinearTwoModelMatrix k).map
            (projectiveGeneralLinearTwoModelToChart k)).det =
            projectiveGeneralLinearTwoModelToChart k
                (projectiveGeneralLinearTwoModelMatrix k).det :=
          (RingHom.map_det _ _).symm
        rw [e]
        exact (isUnit_projectiveGeneralLinearTwoModelMatrix_det k).map _),
    ← projectiveGeneralLinearTwoEval_chartMatrix k (0, 0)]
  have hσ : (projectiveGeneralLinearTwoModelToChart k).comp (algebraMap k _) =
      projectiveGeneralLinearTwoChartStructure k (0, 0) :=
    RingHom.ext (projectiveGeneralLinearTwoModelToChart_algebraMap k)
  have hM : (projectiveGeneralLinearTwoModelMatrix k).map
      (projectiveGeneralLinearTwoModelToChart k) =
      projectiveGeneralLinearTwoChartMatrix k (0, 0) := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [projectiveGeneralLinearTwoModelMatrix,
        show projectiveGeneralLinearTwoChartMatrix k (0, 0) 0 0 = 1 from
          projectiveGeneralLinearTwoChartMatrix_self k (0, 0)]
    · simpa [projectiveGeneralLinearTwoModelMatrix] using
        projectiveGeneralLinearTwoModelToChart_X k 0
    · simpa [projectiveGeneralLinearTwoModelMatrix] using
        projectiveGeneralLinearTwoModelToChart_X k 1
    · simpa [projectiveGeneralLinearTwoModelMatrix] using
        projectiveGeneralLinearTwoModelToChart_X k 2
  congr 1

/-- The model map followed by the chart map is the identity of `k[β, γ, δ, 1/(δ - β γ)]`. -/
theorem projectiveGeneralLinearTwoChartToModel_comp_modelToChart :
    (projectiveGeneralLinearTwoChartToModel k).comp (projectiveGeneralLinearTwoModelToChart k) =
      RingHom.id _ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (projectiveGeneralLinearTwoChartDet k)) ?_
  rw [RingHom.id_comp, RingHom.comp_assoc, projectiveGeneralLinearTwoModelToChart,
    IsLocalization.Away.lift_comp]
  refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply, projectiveGeneralLinearTwoPolynomialToChart,
      eval₂Hom_C, projectiveGeneralLinearTwoChartStructure, projectiveGeneralLinearTwoChartToModel,
      IsLocalization.Away.lift_eq]
    rw [← RingHom.comp_apply, projectiveGeneralLinearTwoEval_comp_algebraMap,
      IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 3) k), algebraMap_eq]
  · have hinv := IsLocalization.Away.mul_invSelf (S := projectiveGeneralLinearTwoChartRing k (0, 0))
      (projectiveGeneralLinearTwoChartElement k (0, 0))
    have himg := congrArg (projectiveGeneralLinearTwoChartToModel k) hinv
    rw [map_mul, map_one, projectiveGeneralLinearTwoChartToModel,
        IsLocalization.Away.lift_eq] at himg
    have hdet := projectiveGeneralLinearTwoToModel_chartElement_mul_det k
    have hq : ∀ q : Fin 2 × Fin 2, projectiveGeneralLinearTwoChartToModel k
        (projectiveGeneralLinearTwoChartMatrix k (0, 0) q.1 q.2) =
          projectiveGeneralLinearTwoModelMatrix k q.1 q.2 := fun q ↦ by
      have h := projectiveGeneralLinearTwoEval_element_mul_det (algebraMap k _)
        (projectiveGeneralLinearTwoModelMatrix k)
            (isUnit_projectiveGeneralLinearTwoModelMatrix_det k)
        (0, 0) q
      simp only [projectiveGeneralLinearTwoChartMatrix, map_mul,
        projectiveGeneralLinearTwoChartToModel, IsLocalization.Away.lift_eq]
      have h00 : projectiveGeneralLinearTwoModelMatrix k 0 0 = 1 := rfl
      rw [h00, one_mul] at h
      set ℓ := IsLocalization.Away.lift (S := projectiveGeneralLinearTwoChartRing k (0, 0))
        (projectiveGeneralLinearTwoChartElement k (0, 0))
        (isUnit_projectiveGeneralLinearTwoToModel_chartElement k)
        (IsLocalization.Away.invSelf (projectiveGeneralLinearTwoChartElement k (0, 0)))
      set a := projectiveGeneralLinearTwoToModel k (projectiveGeneralLinearTwoElement k (0, 0) q)
      set G := projectiveGeneralLinearTwoToModel k (projectiveGeneralLinearTwoChartElement k (0, 0))
      linear_combination (-(a * ℓ)) * hdet + (G * ℓ) * h +
        projectiveGeneralLinearTwoModelMatrix k q.1 q.2 * himg
    fin_cases i
    · simpa [projectiveGeneralLinearTwoPolynomialToChart, projectiveGeneralLinearTwoModelMatrix]
        using hq (0, 1)
    · simpa [projectiveGeneralLinearTwoPolynomialToChart, projectiveGeneralLinearTwoModelMatrix]
        using hq (1, 0)
    · simpa [projectiveGeneralLinearTwoPolynomialToChart, projectiveGeneralLinearTwoModelMatrix]
        using hq (1, 1)

/-- **The chart `D(g_{(0,0)})` of `PGL₂` is `k[β, γ, δ, 1/(δ - β γ)]`.** -/
def projectiveGeneralLinearTwoChartEquiv :
    projectiveGeneralLinearTwoChartRing k (0, 0) ≃+* projectiveGeneralLinearTwoChartModel k :=
  RingEquiv.ofRingHom (projectiveGeneralLinearTwoChartToModel k)
    (projectiveGeneralLinearTwoModelToChart k)
    (projectiveGeneralLinearTwoChartToModel_comp_modelToChart k)
    (projectiveGeneralLinearTwoModelToChart_comp_toChart k)

/-! ### The dimension -/

/-- The coordinate ring of `PGL₂` is of finite type over `k`. -/
instance finiteType_projectiveGeneralLinearTwoRing :
    Algebra.FiniteType k (projectiveGeneralLinearTwoRing k) :=
  (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)

/-- The chart elements `g_p` of the coordinate ring of `PGL₂` are nonzero. -/
theorem projectiveGeneralLinearTwoChartElement_ne_zero (p : Fin 2 × Fin 2) :
    projectiveGeneralLinearTwoChartElement k p ≠ 0 := by
  have := isDomain_generalLinearTwoCoordinateRing k
  intro h
  have h' := congrArg (Subtype.val) h
  simp only [coe_projectiveGeneralLinearTwoElement, ZeroMemClass.coe_zero] at h'
  have hx : generalLinearTwoEntry k p ≠ 0 := by
    rw [generalLinearTwoEntry, generalLinearTwoCoordinate, ne_eq,
      IsLocalization.to_map_eq_zero_iff _ (powers_le_nonZeroDivisors_of_noZeroDivisors
        (Matrix.det_mvPolynomialX_ne_zero (Fin 2) k))]
    exact MvPolynomial.X_ne_zero _
  have hinv : generalLinearTwoDeterminantInv k ≠ 0 := fun h0 ↦ by
    have := generalLinearTwoDeterminant_mul_inv k
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  exact mul_ne_zero (mul_ne_zero hx hx) hinv h'

/-- The polynomial `δ - β γ` in `k[β, γ, δ]` is nonzero. -/
theorem projectiveGeneralLinearTwoChartDet_ne_zero : projectiveGeneralLinearTwoChartDet k ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval ![0, 0, 1]) h
  simp at this

/-- **The coordinate ring of `PGL₂` over a field has Krull dimension three.** -/
theorem ringKrullDim_projectiveGeneralLinearTwoRing :
    ringKrullDim (projectiveGeneralLinearTwoRing k) = 3 := by
  have := isDomain_generalLinearTwoCoordinateRing k
  rw [← ringKrullDim_localization_away_eq k _
    (projectiveGeneralLinearTwoChartElement_ne_zero k (0, 0)),
    ringKrullDim_eq_of_ringEquiv (projectiveGeneralLinearTwoChartEquiv k),
    ringKrullDim_localization_away_eq k _ (projectiveGeneralLinearTwoChartDet_ne_zero k),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
  simp

/-- **`PGL₂` over a field has dimension three.** -/
theorem topologicalKrullDim_projectiveGeneralLinearTwoScheme :
    topologicalKrullDim (projectiveGeneralLinearTwoScheme k).left = 3 := by
  show topologicalKrullDim (PrimeSpectrum (projectiveGeneralLinearTwoRing k)) = 3
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
      ringKrullDim_projectiveGeneralLinearTwoRing]

end AlgebraicGeometry
