module

public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineChartMorphisms

/-!
# The glued projective line is `Proj R[T₀, T₁]`

Let `R` be a commutative ring. The projective line `ℙ¹_R` glued from two affine lines
`Spec R[x]`, `Spec R[y]` along `x y = 1` is isomorphic over `Spec R` to `Proj R[T₀, T₁]`, and
hence to the projective space `ℙ¹_{Spec R}` defined by base change from the integers. The
isomorphism identifies the chart `Spec R[x]` with the standard open `D₊(T₀)`, the coordinate `x`
corresponding to `T₁ / T₀`, and the chart `Spec R[y]` with `D₊(T₁)`, the coordinate `y`
corresponding to `T₀ / T₁`.

## Main definitions

* `AlgebraicGeometry.projectiveLineProjChartRingEquiv`: the identification `R[x] ≃ R[T]_{(Tᵢ)}`
  of the coordinate ring of a chart of `ℙ¹_R` with the degree-zero localization of
  `R[T₀, T₁]` at `Tᵢ`.
* `AlgebraicGeometry.projectiveLineIsoProj`: the isomorphism `ℙ¹_R ≅ Proj R[T₀, T₁]`.
* `AlgebraicGeometry.projectiveLineIsoProjectiveSpaceOver`: the isomorphism
  `ℙ¹_R ≅ ℙ¹_{Spec R}` with the base-change model of projective space.
* `AlgebraicGeometry.projectiveLineOverIsoProjectiveSpaceOver`: the same isomorphism as an
  isomorphism of schemes over `Spec R`.

## Main results

* `AlgebraicGeometry.projectiveLineXChart_comp_projectiveLineIsoProj_hom` and
  `AlgebraicGeometry.projectiveLineYChart_comp_projectiveLineIsoProj_hom`: the isomorphism
  carries the two charts of `ℙ¹_R` to the standard opens `D₊(T₀)` and `D₊(T₁)`.
* `AlgebraicGeometry.projectiveLineIsoProj_hom_comp_projToSpecCoeff` and
  `AlgebraicGeometry.projectiveLineIsoProjectiveSpaceOver_hom_fst`: the isomorphisms are
  isomorphisms over `Spec R`.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
* [Stacks Project, Tag 01MR](https://stacks.math.columbia.edu/tag/01MR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomogeneousLocalization
open Stacks.AlgebraicGeometry.ProjPolyChart

namespace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-! ### The charts of `Proj R[T₀, T₁]` -/

/-- The variable of the chart `D₊(Tᵢ)` of `Proj R[T₀, T₁]`: the index of the other variable. -/
def projectiveLineProjChartVar (i : Fin (1 + 1)) : {j : Fin (1 + 1) // j ≠ i} :=
  ⟨i.rev, by fin_cases i <;> decide⟩

/-- The index of the other variable is the only index different from `i`. -/
theorem eq_projectiveLineProjChartVar (i : Fin (1 + 1)) (j : {j : Fin (1 + 1) // j ≠ i}) :
    j = projectiveLineProjChartVar i := by
  obtain ⟨j, hj⟩ := j
  exact Subtype.ext (by fin_cases i <;> fin_cases j <;> first | rfl | exact absurd rfl hj)

/-- A polynomial ring in one variable is a polynomial ring on the one-element index set
`{j // j ≠ i}`. -/
def projectiveLineProjChartVarEquiv (i : Fin (1 + 1)) :
    Polynomial R ≃+* MvPolynomial {j : Fin (1 + 1) // j ≠ i} R :=
  RingEquiv.ofRingHom
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (projectiveLineProjChartVar i)))
    (MvPolynomial.eval₂Hom Polynomial.C fun _ ↦ Polynomial.X)
    (MvPolynomial.ringHom_ext (fun r ↦ by simp) fun j ↦ by
      rw [eq_projectiveLineProjChartVar i j]; simp)
    (Polynomial.ringHom_ext (fun r ↦ by simp) (by simp))

/-- **The chart `D₊(Tᵢ)` of `Proj R[T₀, T₁]` is an affine line.** The degree-zero localization
of `R[T₀, T₁]` at `Tᵢ` is the polynomial ring over `R` in the affine coordinate `T_j / Tᵢ`,
`j ≠ i`. -/
def projectiveLineProjChartRingEquiv (i : Fin (1 + 1)) :
    Polynomial R ≃+* Away (polyGrading R 1) (MvPolynomial.X i) :=
  (projectiveLineProjChartVarEquiv R i).trans (chartEquiv R 1 i)

/-- The chart identification sends a constant `r` to the coefficient `r` of `R[T]_{(Tᵢ)}`. -/
@[simp]
theorem projectiveLineProjChartRingEquiv_C (i : Fin (1 + 1)) (r : R) :
    projectiveLineProjChartRingEquiv R i (Polynomial.C r) = coeffToAway R 1 i r := by
  simp [projectiveLineProjChartRingEquiv, projectiveLineProjChartVarEquiv]

/-- The chart identification sends the coordinate to the affine coordinate `T_j / Tᵢ`, `j ≠ i`. -/
@[simp]
theorem projectiveLineProjChartRingEquiv_X (i : Fin (1 + 1)) :
    projectiveLineProjChartRingEquiv R i Polynomial.X =
      chartCoord R 1 i (projectiveLineProjChartVar i) := by
  simp [projectiveLineProjChartRingEquiv, projectiveLineProjChartVarEquiv]

/-! ### The overlap `D₊(T₀ T₁)` -/

/-- The product `T₀ T₁`, whose standard open `D₊(T₀ T₁)` is the overlap of the two charts. -/
abbrev projectiveLineProjOverlapElem : MvPolynomial (Fin (1 + 1)) R :=
  MvPolynomial.X 0 * MvPolynomial.X 1

/-- The product `T₀ T₁` is `Tᵢ` times the other variable. -/
theorem projectiveLineProjOverlapElem_eq (i : Fin (1 + 1)) :
    projectiveLineProjOverlapElem R = MvPolynomial.X i * MvPolynomial.X i.rev := by
  fin_cases i
  · rfl
  · exact mul_comm _ _

/-- The restriction `R[T]_{(Tᵢ)} → R[T]_{(T₀ T₁)}` from a chart to the overlap,
`a / Tᵢⁿ ↦ a T_jⁿ / (T₀ T₁)ⁿ`. -/
def projectiveLineProjChartToOverlap (i : Fin (1 + 1)) :
    Away (polyGrading R 1) (MvPolynomial.X i) →+*
      Away (polyGrading R 1) (projectiveLineProjOverlapElem R) :=
  awayMap (polyGrading R 1) (X_mem_one R 1 i.rev) (projectiveLineProjOverlapElem_eq R i)

/-- The dehomogenization `R[T₀, T₁] → R[T, T⁻¹]`, `T₀ ↦ 1`, `T₁ ↦ T`. -/
def projectiveLineProjDehomogenize : MvPolynomial (Fin (1 + 1)) R →+* LaurentPolynomial R :=
  MvPolynomial.eval₂Hom LaurentPolynomial.C ![1, LaurentPolynomial.T 1]

/-- The dehomogenization sends `T₀` to `1`. -/
@[simp]
theorem projectiveLineProjDehomogenize_X_zero :
    projectiveLineProjDehomogenize R (MvPolynomial.X 0) = 1 := by
  rw [projectiveLineProjDehomogenize, MvPolynomial.eval₂Hom_X']
  rfl

/-- The dehomogenization sends `T₁` to `T`. -/
@[simp]
theorem projectiveLineProjDehomogenize_X_one :
    projectiveLineProjDehomogenize R (MvPolynomial.X 1) = LaurentPolynomial.T 1 := by
  rw [projectiveLineProjDehomogenize, MvPolynomial.eval₂Hom_X']
  rfl

/-- The dehomogenization of `T₀ T₁` is the unit `T`, with inverse `T⁻¹`. -/
theorem projectiveLineProjDehomogenize_overlapElem_mul :
    projectiveLineProjDehomogenize R (projectiveLineProjOverlapElem R) *
      LaurentPolynomial.T (-1) = 1 := by
  rw [map_mul, projectiveLineProjDehomogenize_X_zero, projectiveLineProjDehomogenize_X_one,
    one_mul, ← LaurentPolynomial.T_add]
  norm_num

/-- The ring map `R[T]_{(T₀ T₁)} → R[T, T⁻¹]`, `a / (T₀ T₁)ⁿ ↦ a(1, T) T⁻ⁿ`. -/
def projectiveLineProjOverlapToLaurent :
    Away (polyGrading R 1) (projectiveLineProjOverlapElem R) →+* LaurentPolynomial R :=
  (Localization.awayLift (projectiveLineProjDehomogenize R) _
    (isUnit_iff_exists_inv.mpr ⟨_, projectiveLineProjDehomogenize_overlapElem_mul R⟩)).comp
    (algebraMap _ (Localization.Away (projectiveLineProjOverlapElem R)))

/-- The ring map `R[T]_{(T₀ T₁)} → R[T, T⁻¹]` on a fraction `a / (T₀ T₁)ⁿ`. -/
@[simp]
theorem projectiveLineProjOverlapToLaurent_mk {d : ℕ}
    (hx : projectiveLineProjOverlapElem R ∈ polyGrading R 1 d) (n : ℕ)
    (a : MvPolynomial (Fin (1 + 1)) R) (ha : a ∈ polyGrading R 1 (n • d)) :
    projectiveLineProjOverlapToLaurent R (Away.mk _ hx n a ha) =
      projectiveLineProjDehomogenize R a * LaurentPolynomial.T (-1) ^ n := by
  rw [projectiveLineProjOverlapToLaurent, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  exact Localization.awayLift_mk _ _ _ _ (projectiveLineProjDehomogenize_overlapElem_mul R) n

/-- The affine coordinate of the chart `D₊(Tᵢ)`, restricted to the overlap and sent to
`R[T, T⁻¹]`, is `T_j² T⁻¹`. -/
private theorem projectiveLineProjOverlapToLaurent_chartToOverlap_chartCoord (i : Fin (1 + 1)) :
    projectiveLineProjOverlapToLaurent R (projectiveLineProjChartToOverlap R i
      (chartCoord R 1 i (projectiveLineProjChartVar i))) =
      projectiveLineProjDehomogenize R (MvPolynomial.X i.rev) ^ 2 * LaurentPolynomial.T (-1) := by
  simp only [chartCoord, projectiveLineProjChartToOverlap, awayMap_mk,
    projectiveLineProjOverlapToLaurent_mk]
  change projectiveLineProjDehomogenize R (MvPolynomial.X i.rev * MvPolynomial.X i.rev ^ 1) *
    LaurentPolynomial.T (-1) ^ 1 = _
  rw [map_mul, map_pow, pow_one, pow_one, sq]

/-- Restricted to the first chart, the ring map `R[T]_{(T₀ T₁)} → R[T, T⁻¹]` is the inclusion
`R[x] → R[T, T⁻¹]`, `x ↦ T`. -/
theorem projectiveLineProjOverlapToLaurent_comp_zero :
    ((projectiveLineProjOverlapToLaurent R).comp (projectiveLineProjChartToOverlap R 0)).comp
      (projectiveLineProjChartRingEquiv R 0).toRingHom = Polynomial.toLaurent := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [coeffToAway_eq_mk, projectiveLineProjChartToOverlap, projectiveLineProjDehomogenize]
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      projectiveLineProjChartRingEquiv_X,
      projectiveLineProjOverlapToLaurent_chartToOverlap_chartCoord]
    change projectiveLineProjDehomogenize R (MvPolynomial.X 1) ^ 2 * _ = _
    rw [projectiveLineProjDehomogenize_X_one, Polynomial.toLaurent_X, sq, mul_assoc,
      ← LaurentPolynomial.T_add, ← LaurentPolynomial.T_add]
    norm_num

/-- Restricted to the second chart, the ring map `R[T]_{(T₀ T₁)} → R[T, T⁻¹]` is the inclusion
`R[y] → R[T, T⁻¹]`, `y ↦ T⁻¹`. -/
theorem projectiveLineProjOverlapToLaurent_comp_one :
    ((projectiveLineProjOverlapToLaurent R).comp (projectiveLineProjChartToOverlap R 1)).comp
      (projectiveLineProjChartRingEquiv R 1).toRingHom =
      (projectiveLineOverlapInverseCoordinate R).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [coeffToAway_eq_mk, projectiveLineProjChartToOverlap, projectiveLineProjDehomogenize,
      projectiveLineOverlapInverseCoordinate]
  · rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      projectiveLineProjChartRingEquiv_X,
      projectiveLineProjOverlapToLaurent_chartToOverlap_chartCoord]
    change projectiveLineProjDehomogenize R (MvPolynomial.X 0) ^ 2 * _ = _
    simp [projectiveLineOverlapInverseCoordinate]

/-- The product `T₀ T₁` is homogeneous of degree `2`. -/
theorem projectiveLineProjOverlapElem_mem : projectiveLineProjOverlapElem R ∈ polyGrading R 1 2 :=
  SetLike.mul_mem_graded (X_mem_one R 1 0) (X_mem_one R 1 1)

/-- The affine coordinate `T₁ / T₀`, restricted to the overlap. -/
theorem projectiveLineProjChartToOverlap_zero_chartCoord :
    projectiveLineProjChartToOverlap R 0 (chartCoord R 1 0 (projectiveLineProjChartVar 0)) =
      Away.mk _ (projectiveLineProjOverlapElem_mem R) 1 (MvPolynomial.X 1 * MvPolynomial.X 1 ^ 1)
        (SetLike.mul_mem_graded (X_mem_one R 1 1)
          (SetLike.pow_mem_graded 1 (X_mem_one R 1 1))) := by
  simp only [projectiveLineProjChartToOverlap, chartCoord, awayMap_mk]
  rfl

/-- The affine coordinate `T₀ / T₁`, restricted to the overlap. -/
theorem projectiveLineProjChartToOverlap_one_chartCoord :
    projectiveLineProjChartToOverlap R 1 (chartCoord R 1 1 (projectiveLineProjChartVar 1)) =
      Away.mk _ (projectiveLineProjOverlapElem_mem R) 1 (MvPolynomial.X 0 * MvPolynomial.X 0 ^ 1)
        (SetLike.mul_mem_graded (X_mem_one R 1 0)
          (SetLike.pow_mem_graded 1 (X_mem_one R 1 0))) := by
  simp only [projectiveLineProjChartToOverlap, chartCoord, awayMap_mk]
  rfl

/-- On the overlap, `(T₁ / T₀) · (T₀ / T₁) = 1`. -/
theorem projectiveLineProjOverlap_chartCoord_mul :
    projectiveLineProjChartToOverlap R 0 (chartCoord R 1 0 (projectiveLineProjChartVar 0)) *
      projectiveLineProjChartToOverlap R 1 (chartCoord R 1 1 (projectiveLineProjChartVar 1)) =
      1 := by
  rw [projectiveLineProjChartToOverlap_zero_chartCoord,
    projectiveLineProjChartToOverlap_one_chartCoord, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_mul, Away.val_mk, Away.val_mk, HomogeneousLocalization.val_one,
    Localization.mk_mul,
    show MvPolynomial.X 1 * MvPolynomial.X 1 ^ 1 * (MvPolynomial.X 0 * MvPolynomial.X 0 ^ 1) =
      projectiveLineProjOverlapElem R ^ 1 * projectiveLineProjOverlapElem R ^ 1 by ring]
  exact Localization.mk_self
    ((⟨_, 1, rfl⟩ : Submonoid.powers (projectiveLineProjOverlapElem R)) * ⟨_, 1, rfl⟩)

/-- The affine coordinate `T₁ / T₀`, a unit on the overlap `D₊(T₀ T₁)` with inverse `T₀ / T₁`. -/
def projectiveLineProjOverlapUnit :
    (Away (polyGrading R 1) (projectiveLineProjOverlapElem R))ˣ where
  val := projectiveLineProjChartToOverlap R 0 (chartCoord R 1 0 (projectiveLineProjChartVar 0))
  inv := projectiveLineProjChartToOverlap R 1 (chartCoord R 1 1 (projectiveLineProjChartVar 1))
  val_inv := projectiveLineProjOverlap_chartCoord_mul R
  inv_val := (mul_comm _ _).trans (projectiveLineProjOverlap_chartCoord_mul R)

/-- The unit `T₁ / T₀` of the overlap is the affine coordinate of the first chart. -/
@[simp]
theorem projectiveLineProjOverlapUnit_val :
    (projectiveLineProjOverlapUnit R : Away (polyGrading R 1) (projectiveLineProjOverlapElem R)) =
      projectiveLineProjChartToOverlap R 0 (chartCoord R 1 0 (projectiveLineProjChartVar 0)) :=
  rfl

/-- The inverse of the unit `T₁ / T₀` of the overlap is the affine coordinate `T₀ / T₁` of the
second chart. -/
@[simp]
theorem projectiveLineProjOverlapUnit_inv :
    ((projectiveLineProjOverlapUnit R)⁻¹ :
        (Away (polyGrading R 1) (projectiveLineProjOverlapElem R))ˣ) =
      projectiveLineProjChartToOverlap R 1 (chartCoord R 1 1 (projectiveLineProjChartVar 1)) :=
  rfl

/-- The coefficients of the overlap `D₊(T₀ T₁)`, restricted from either chart. -/
theorem projectiveLineProjChartToOverlap_coeffToAway (i : Fin (1 + 1)) (r : R) :
    projectiveLineProjChartToOverlap R i (coeffToAway R 1 i r) =
      projectiveLineProjChartToOverlap R 0 (coeffToAway R 1 0 r) := by
  simp only [coeffToAway_eq_mk, projectiveLineProjChartToOverlap, awayMap_mk]
  rw [HomogeneousLocalization.ext_iff_val, Away.val_mk, Away.val_mk]
  simp

/-- The ring map `R[T, T⁻¹] → R[T]_{(T₀ T₁)}` sending `T` to the unit `T₁ / T₀`. -/
def projectiveLineLaurentToProjOverlap :
    LaurentPolynomial R →+* Away (polyGrading R 1) (projectiveLineProjOverlapElem R) :=
  LaurentPolynomial.eval₂ ((projectiveLineProjChartToOverlap R 0).comp (coeffToAway R 1 0))
    (projectiveLineProjOverlapUnit R)

/-- Restricted to `R[x]`, the ring map `R[T, T⁻¹] → R[T]_{(T₀ T₁)}` is the first chart
identification followed by restriction to the overlap. -/
theorem projectiveLineLaurentToProjOverlap_comp_toLaurent :
    (projectiveLineLaurentToProjOverlap R).comp Polynomial.toLaurent =
      (projectiveLineProjChartToOverlap R 0).comp
        (projectiveLineProjChartRingEquiv R 0).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [projectiveLineLaurentToProjOverlap]
  · simp [projectiveLineLaurentToProjOverlap]

/-- Restricted to `R[y]` along `y ↦ T⁻¹`, the ring map `R[T, T⁻¹] → R[T]_{(T₀ T₁)}` is the second
chart identification followed by restriction to the overlap. -/
theorem projectiveLineLaurentToProjOverlap_comp_overlapInverseCoordinate :
    (projectiveLineLaurentToProjOverlap R).comp
        (projectiveLineOverlapInverseCoordinate R).toRingHom =
      (projectiveLineProjChartToOverlap R 1).comp
        (projectiveLineProjChartRingEquiv R 1).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [projectiveLineLaurentToProjOverlap, projectiveLineOverlapInverseCoordinate,
      projectiveLineProjChartToOverlap_coeffToAway, ← LaurentPolynomial.C_eq_algebraMap]
  · have h := LaurentPolynomial.eval₂_T_neg_n
      ((projectiveLineProjChartToOverlap R 0).comp (coeffToAway R 1 0))
      (projectiveLineProjOverlapUnit R) 1
    simp only [Nat.cast_one, pow_one] at h
    simp [projectiveLineLaurentToProjOverlap, projectiveLineOverlapInverseCoordinate, h]

/-! ### The morphism `ℙ¹_R ⟶ Proj R[T₀, T₁]` -/

/-- The chart `Spec R[x] ⟶ Proj R[T₀, T₁]` onto the standard open `D₊(Tᵢ)`. -/
def projectiveLineProjChart (i : Fin (1 + 1)) :
    Spec (.of (Polynomial R)) ⟶ Proj (polyGrading R 1) :=
  Spec.map (CommRingCat.ofHom (projectiveLineProjChartRingEquiv R i).symm.toRingHom) ≫
    Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos

/-- The open `D₊(T₀ T₁)` lies in `D₊(Tᵢ)` through the restriction map. -/
theorem Spec_map_projectiveLineProjChartToOverlap_comp_awayι (i : Fin (1 + 1)) :
    Spec.map (CommRingCat.ofHom (projectiveLineProjChartToOverlap R i)) ≫
        Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos =
      Proj.awayι (polyGrading R 1) (projectiveLineProjOverlapElem R)
        (projectiveLineProjOverlapElem_mem R) two_pos :=
  Proj.SpecMap_awayMap_awayι (polyGrading R 1) (X_mem_one R 1 i) Nat.one_pos
    (X_mem_one R 1 i.rev) (projectiveLineProjOverlapElem_eq R i)

/-- On the overlap `Spec R[T, T⁻¹]`, both charts factor through `D₊(T₀ T₁)`. -/
theorem projectiveLinePuncturedChart_comp_projectiveLineProjChart :
    projectiveLinePuncturedChart R ≫ projectiveLineProjChart R 0 =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫
        projectiveLineProjChart R 1 := by
  have h (i : Fin (1 + 1)) (φ : Polynomial R →+* LaurentPolynomial R)
      (hφ : ((projectiveLineProjOverlapToLaurent R).comp
        (projectiveLineProjChartToOverlap R i)).comp
          (projectiveLineProjChartRingEquiv R i).toRingHom = φ) :
      Spec.map (CommRingCat.ofHom φ) ≫ projectiveLineProjChart R i =
        Spec.map (CommRingCat.ofHom (projectiveLineProjOverlapToLaurent R)) ≫
          Proj.awayι (polyGrading R 1) (projectiveLineProjOverlapElem R)
            (projectiveLineProjOverlapElem_mem R) two_pos := by
    have hφ' : φ.comp (projectiveLineProjChartRingEquiv R i).symm.toRingHom =
        (projectiveLineProjOverlapToLaurent R).comp (projectiveLineProjChartToOverlap R i) := by
      rw [← hφ]
      ext a
      simp
    rw [projectiveLineProjChart, ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom, hφ',
      ← Spec_map_ofHom_comp_Spec_map_ofHom, Category.assoc,
      Spec_map_projectiveLineProjChartToOverlap_comp_awayι]
  rw [h 0 _ (projectiveLineProjOverlapToLaurent_comp_zero R),
    h 1 _ (projectiveLineProjOverlapToLaurent_comp_one R)]

/-- The morphism `ℙ¹_R ⟶ Proj R[T₀, T₁]` glued from the two charts. -/
def projectiveLineToProj : projectiveLine R ⟶ Proj (polyGrading R 1) :=
  projectiveLineDesc (projectiveLineProjChart R 0) (projectiveLineProjChart R 1)
    (projectiveLinePuncturedChart_comp_projectiveLineProjChart R)

/-- On the first chart, the morphism `ℙ¹_R ⟶ Proj R[T₀, T₁]` is the chart onto `D₊(T₀)`. -/
@[reassoc (attr := simp)]
theorem projectiveLineXChart_comp_projectiveLineToProj :
    projectiveLineXChart R ≫ projectiveLineToProj R = projectiveLineProjChart R 0 :=
  projectiveLineXChart_comp_desc _ _ _

/-- On the second chart, the morphism `ℙ¹_R ⟶ Proj R[T₀, T₁]` is the chart onto `D₊(T₁)`. -/
@[reassoc (attr := simp)]
theorem projectiveLineYChart_comp_projectiveLineToProj :
    projectiveLineYChart R ≫ projectiveLineToProj R = projectiveLineProjChart R 1 :=
  projectiveLineYChart_comp_desc _ _ _

/-! ### The morphism `Proj R[T₀, T₁] ⟶ ℙ¹_R` -/

/-- The chart `D₊(Tᵢ) = Spec R[T]_{(Tᵢ)} ⟶ ℙ¹_R`: the first chart of `ℙ¹_R` for `i = 0`, the
second for `i = 1`. -/
def projectiveLineFromProjChart (i : Fin (1 + 1)) :
    Spec (.of (Away (polyGrading R 1) (MvPolynomial.X i))) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (projectiveLineProjChartRingEquiv R i).toRingHom) ≫
    ![projectiveLineXChart R, projectiveLineYChart R] i

/-- On the overlap `D₊(T₀ T₁)`, both charts factor through `Spec R[T, T⁻¹]`. -/
theorem Spec_map_projectiveLineProjChartToOverlap_comp_fromProjChart :
    Spec.map (CommRingCat.ofHom (projectiveLineProjChartToOverlap R 0)) ≫
        projectiveLineFromProjChart R 0 =
      Spec.map (CommRingCat.ofHom (projectiveLineProjChartToOverlap R 1)) ≫
        projectiveLineFromProjChart R 1 := by
  simp only [projectiveLineFromProjChart, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← Category.assoc, ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
    Spec_map_ofHom_comp_Spec_map_ofHom, ← projectiveLineLaurentToProjOverlap_comp_toLaurent,
    ← projectiveLineLaurentToProjOverlap_comp_overlapInverseCoordinate,
    ← Spec_map_ofHom_comp_Spec_map_ofHom, ← Spec_map_ofHom_comp_Spec_map_ofHom, Category.assoc,
    Category.assoc]
  exact congrArg (_ ≫ ·) (isPullback_projectiveLineCharts _).w

/-- The charts `D₊(T₀) ⟶ ℙ¹_R` and `D₊(T₁) ⟶ ℙ¹_R` agree on the intersection `D₊(T₀) ∩ D₊(T₁)`. -/
theorem pullback_fst_comp_projectiveLineFromProjChart_zero :
    pullback.fst (Proj.awayι (polyGrading R 1) (MvPolynomial.X 0) (X_mem_one R 1 0) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 1) (X_mem_one R 1 1) Nat.one_pos) ≫
        projectiveLineFromProjChart R 0 =
      pullback.snd _ _ ≫ projectiveLineFromProjChart R 1 := by
  rw [← cancel_epi (Proj.pullbackAwayιIso (polyGrading R 1) (X_mem_one R 1 0) Nat.one_pos
    (X_mem_one R 1 1) Nat.one_pos (projectiveLineProjOverlapElem_eq R 0)).inv,
    Proj.pullbackAwayιIso_inv_fst_assoc, Proj.pullbackAwayιIso_inv_snd_assoc]
  exact Spec_map_projectiveLineProjChartToOverlap_comp_fromProjChart R

/-- The charts `D₊(T₁) ⟶ ℙ¹_R` and `D₊(T₀) ⟶ ℙ¹_R` agree on the intersection `D₊(T₁) ∩ D₊(T₀)`. -/
theorem pullback_fst_comp_projectiveLineFromProjChart_one :
    pullback.fst (Proj.awayι (polyGrading R 1) (MvPolynomial.X 1) (X_mem_one R 1 1) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 0) (X_mem_one R 1 0) Nat.one_pos) ≫
        projectiveLineFromProjChart R 1 =
      pullback.snd _ _ ≫ projectiveLineFromProjChart R 0 := by
  rw [← cancel_epi (pullbackSymmetry _ _).hom]
  simpa using (pullback_fst_comp_projectiveLineFromProjChart_zero R).symm

/-- The morphism `Proj R[T₀, T₁] ⟶ ℙ¹_R` glued over the standard cover. -/
def projToProjectiveLine : Proj (polyGrading R 1) ⟶ projectiveLine R :=
  (affineChartCover R 1).openCover.glueMorphisms (projectiveLineFromProjChart R) (by
    intro i j
    change Fin (1 + 1) at i j
    fin_cases i <;> fin_cases j
    · exact congrArg (· ≫ projectiveLineFromProjChart R 0) ((cancel_mono
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 0) (X_mem_one R 1 0) Nat.one_pos)).1
          pullback.condition)
    · exact pullback_fst_comp_projectiveLineFromProjChart_zero R
    · exact pullback_fst_comp_projectiveLineFromProjChart_one R
    · exact congrArg (· ≫ projectiveLineFromProjChart R 1) ((cancel_mono
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 1) (X_mem_one R 1 1) Nat.one_pos)).1
          pullback.condition))

/-- On `D₊(Tᵢ)`, the morphism `Proj R[T₀, T₁] ⟶ ℙ¹_R` is the chart `D₊(Tᵢ) ⟶ ℙ¹_R`. -/
@[reassoc (attr := simp)]
theorem awayι_comp_projToProjectiveLine (i : Fin (1 + 1)) :
    Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos ≫
        projToProjectiveLine R = projectiveLineFromProjChart R i :=
  (affineChartCover R 1).openCover.ι_glueMorphisms _ _ i

/-! ### The isomorphism -/

/-- The chart onto `D₊(Tᵢ)` followed by `Proj R[T₀, T₁] ⟶ ℙ¹_R` is the corresponding chart of
`ℙ¹_R`. -/
theorem projectiveLineProjChart_comp_projToProjectiveLine (i : Fin (1 + 1)) :
    projectiveLineProjChart R i ≫ projToProjectiveLine R =
      ![projectiveLineXChart R, projectiveLineYChart R] i := by
  rw [projectiveLineProjChart, Category.assoc, awayι_comp_projToProjectiveLine,
    projectiveLineFromProjChart, ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
    RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

/-- The chart `D₊(Tᵢ) ⟶ ℙ¹_R` followed by `ℙ¹_R ⟶ Proj R[T₀, T₁]` is the inclusion of `D₊(Tᵢ)`. -/
theorem projectiveLineFromProjChart_comp_projectiveLineToProj (i : Fin (1 + 1)) :
    projectiveLineFromProjChart R i ≫ projectiveLineToProj R =
      Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos := by
  have h : ![projectiveLineXChart R, projectiveLineYChart R] i ≫ projectiveLineToProj R =
      projectiveLineProjChart R i := by
    fin_cases i
    · exact projectiveLineXChart_comp_projectiveLineToProj R
    · exact projectiveLineYChart_comp_projectiveLineToProj R
  rw [projectiveLineFromProjChart, Category.assoc, h, projectiveLineProjChart,
    ← Category.assoc, Spec_map_ofHom_comp_Spec_map_ofHom,
    RingEquiv.toRingHom_comp_symm_toRingHom, CommRingCat.ofHom_id, Spec.map_id,
    Category.id_comp]

/-- **The glued projective line is `Proj R[T₀, T₁]`.** The chart `Spec R[x]` is carried onto
`D₊(T₀)` with `x = T₁ / T₀`, and the chart `Spec R[y]` onto `D₊(T₁)` with `y = T₀ / T₁`. -/
def projectiveLineIsoProj : projectiveLine R ≅ Proj (polyGrading R 1) where
  hom := projectiveLineToProj R
  inv := projToProjectiveLine R
  hom_inv_id := projectiveLine_hom_ext
    (by simpa using projectiveLineProjChart_comp_projToProjectiveLine R 0)
    (by simpa using projectiveLineProjChart_comp_projToProjectiveLine R 1)
  inv_hom_id := (affineChartCover R 1).openCover.hom_ext _ _ fun i ↦ by
    change Fin (1 + 1) at i
    change Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos ≫ _ = _
    rw [awayι_comp_projToProjectiveLine_assoc,
      projectiveLineFromProjChart_comp_projectiveLineToProj, Category.comp_id]
    rfl

/-- The forward map of `ℙ¹_R ≅ Proj R[T₀, T₁]` is the morphism glued from the two charts. -/
@[simp]
theorem projectiveLineIsoProj_hom : (projectiveLineIsoProj R).hom = projectiveLineToProj R :=
  rfl

/-- The inverse of `ℙ¹_R ≅ Proj R[T₀, T₁]` is the morphism glued over the standard cover. -/
@[simp]
theorem projectiveLineIsoProj_inv : (projectiveLineIsoProj R).inv = projToProjectiveLine R :=
  rfl

/-- The isomorphism carries the first chart of `ℙ¹_R` onto `D₊(T₀)`. -/
theorem projectiveLineXChart_comp_projectiveLineIsoProj_hom :
    projectiveLineXChart R ≫ (projectiveLineIsoProj R).hom = projectiveLineProjChart R 0 :=
  projectiveLineXChart_comp_projectiveLineToProj R

/-- The isomorphism carries the second chart of `ℙ¹_R` onto `D₊(T₁)`. -/
theorem projectiveLineYChart_comp_projectiveLineIsoProj_hom :
    projectiveLineYChart R ≫ (projectiveLineIsoProj R).hom = projectiveLineProjChart R 1 :=
  projectiveLineYChart_comp_projectiveLineToProj R

/-- The chart onto `D₊(Tᵢ)` followed by `Proj R[T₀, T₁] ⟶ Spec R` is the structure morphism of the
affine line. -/
theorem projectiveLineProjChart_comp_projToSpecCoeff (i : Fin (1 + 1)) :
    projectiveLineProjChart R i ≫ projToSpecCoeff R 1 =
      projectiveLineAffineStructureMorphism R := by
  rw [projectiveLineProjChart, projToSpecCoeff, Category.assoc, Proj.awayι_toSpecZero_assoc,
    Spec_map_ofHom_comp_Spec_map_ofHom, Spec_map_ofHom_comp_Spec_map_ofHom,
    projectiveLineAffineStructureMorphism]
  congr 2
  refine RingHom.ext fun r ↦ (projectiveLineProjChartRingEquiv R i).injective ?_
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.apply_symm_apply, projectiveLineProjChartRingEquiv_C, coeffToAway,
    HomogeneousLocalization.algebraMap_eq]
  congr 1
  exact Subtype.ext (DirectSum.decompose_of_mem_same _ (C_mem_zero R 1 r))

/-- **The isomorphism `ℙ¹_R ≅ Proj R[T₀, T₁]` is an isomorphism over `Spec R`.** -/
@[reassoc (attr := simp)]
theorem projectiveLineIsoProj_hom_comp_projToSpecCoeff :
    (projectiveLineIsoProj R).hom ≫ projToSpecCoeff R 1 = projectiveLine R ↘ Spec (.of R) :=
  projectiveLine_hom_ext
    (by simp [projectiveLineProjChart_comp_projToSpecCoeff])
    (by simp [projectiveLineProjChart_comp_projToSpecCoeff])

/-! ### Comparison with the base-change model of projective space -/

/-- **The glued projective line is the projective line `ℙ¹_{Spec R}`** defined by base change of
`Proj (ULift ℤ)[T₀, T₁]` along `Spec R ⟶ Spec ℤ`. -/
def projectiveLineIsoProjectiveSpaceOver :
    projectiveLine R ≅ projectiveSpaceOver 1 (Spec (.of R)) :=
  projectiveLineIsoProj R ≪≫
    (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R 1).iso.symm

/-- **The isomorphism `ℙ¹_R ≅ ℙ¹_{Spec R}` is an isomorphism over `Spec R`.** -/
@[reassoc (attr := simp)]
theorem projectiveLineIsoProjectiveSpaceOver_hom_fst :
    (projectiveLineIsoProjectiveSpaceOver R).hom ≫
        (projectiveSpaceOver 1 (Spec (.of R)) ↘ Spec (.of R)) =
      projectiveLine R ↘ Spec (.of R) := by
  have h := (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R 1).toBase
  rw [← Iso.eq_inv_comp] at h
  change (projectiveLineIsoProj R).hom ≫
    ((Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison R 1).iso.inv ≫
      pullback.fst _ _) = _
  rw [← h]
  exact projectiveLineIsoProj_hom_comp_projToSpecCoeff R

/-- **The glued projective line and `ℙ¹_{Spec R}` are isomorphic as schemes over `Spec R`.** -/
def projectiveLineOverIsoProjectiveSpaceOver :
    Over.mk (projectiveLine R ↘ Spec (.of R)) ≅
      Over.mk (projectiveSpaceOver 1 (Spec (.of R)) ↘ Spec (.of R)) :=
  Over.isoMk (projectiveLineIsoProjectiveSpaceOver R)
    (projectiveLineIsoProjectiveSpaceOver_hom_fst R)

/-- The underlying morphism of the isomorphism over `Spec R` is `ℙ¹_R ≅ ℙ¹_{Spec R}`. -/
@[simp]
theorem projectiveLineOverIsoProjectiveSpaceOver_hom_left :
    (projectiveLineOverIsoProjectiveSpaceOver R).hom.left =
      (projectiveLineIsoProjectiveSpaceOver R).hom :=
  rfl

end AlgebraicGeometry

end
