module

public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Smooth
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The glued projective line is the projective space of a plane

The chapter on Chow homology builds `ℙ¹` by gluing two affine lines
(`AlgebraicGeometry.projectiveLine`, and over a base `S` its base change
`Stacks.Chow.relativeProjectiveLine S`), while the projections of the intersection chapter live
on `Proj` of a symmetric algebra, `𝐏(W) = AlgebraicGeometry.projectiveSpaceOfModule k W`. This
file identifies the two.

## Main definitions

* `AlgebraicGeometry.ProjectiveLineBridge.projectiveLineIsoProj`: for any commutative ring `R`,
  the glued projective line over `R` is `Proj R[T₀, T₁]`; the `x`-chart is `D₊(T₀)` with
  `x = T₁ / T₀` and the `y`-chart is `D₊(T₁)` with `y = T₀ / T₁`.
* `AlgebraicGeometry.ProjectiveLineBridge.relativeProjectiveLineIsoProjectiveSpaceOverRing`: the
  relative projective line over `Spec R` is projective `1`-space over `R`.
* `AlgebraicGeometry.ProjectiveLineBridge.relativeProjectiveLineIsoProjectiveSpaceOfModule`: for
  a field `k` and a basis of a `k`-vector space `W` indexed by `Fin 2`, the relative projective
  line over `Spec k` is `𝐏(W)`, over `Spec k`.
* `AlgebraicGeometry.ProjectiveLineBridge.zeroPoint`,
  `AlgebraicGeometry.ProjectiveLineBridge.infinityPoint`: the points `0` and `∞` of `𝐏(W)`, the
  images of the zero and infinity sections; they are closed and distinct.

## Implementation notes

The isomorphism `projectiveLine R ≅ Proj R[T₀, T₁]` is built from its two halves, each glued
from charts, and the two composites are checked to be identities chart by chart; no point of
either scheme is examined. The morphism out of the glued line is a `Multicoequalizer.desc`, whose
compatibility on the overlap `Spec R[T, T⁻¹]` is the factorisation of both charts through
`D₊(T₀T₁)`, via a ring map `R[T₀, T₁]_{(T₀T₁)} → R[T, T⁻¹]`. The morphism out of `Proj` is glued
on the standard affine cover by `Scheme.Cover.glueMorphisms`, whose compatibility is the
factorisation of both charts through the punctured line, via a ring map
`R[T, T⁻¹] → R[T₀, T₁]_{(T₀T₁)}`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomogeneousLocalization

universe u

namespace AlgebraicGeometry.ProjectiveLineBridge

open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R]

/-! ### The charts as polynomial rings in one variable -/

/-- The other variable of `R[T₀, T₁]`. -/
def otherIndex (i : Fin 2) : {j : Fin 2 // j ≠ i} :=
  ⟨1 - i, by fin_cases i <;> decide⟩

/-- `R[X] → R[Yⱼ : j ≠ i]`, `X ↦ Y_{1 - i}`. -/
def polyToMv (i : Fin 2) : Polynomial R →+* MvPolynomial {j : Fin 2 // j ≠ i} R :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X (otherIndex i))

/-- `R[Yⱼ : j ≠ i] → R[X]`, every `Yⱼ ↦ X`. -/
def mvToPoly (i : Fin 2) : MvPolynomial {j : Fin 2 // j ≠ i} R →+* Polynomial R :=
  MvPolynomial.eval₂Hom Polynomial.C fun _ => Polynomial.X

/-- Every variable of `R[T₀, T₁]` other than `Tᵢ` is `otherIndex i`. -/
theorem eq_otherIndex (i : Fin 2) (j : {j : Fin 2 // j ≠ i}) : j = otherIndex i := by
  obtain ⟨j, hj⟩ := j
  apply Subtype.ext
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hj | rfl

/-- `mvToPoly` is a left inverse of `polyToMv`. -/
theorem mvToPoly_comp_polyToMv (i : Fin 2) :
    (mvToPoly R i).comp (polyToMv R i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [mvToPoly, polyToMv]
  · simp [mvToPoly, polyToMv]

/-- `polyToMv` is a left inverse of `mvToPoly`. -/
theorem polyToMv_comp_mvToPoly (i : Fin 2) :
    (polyToMv R i).comp (mvToPoly R i) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [mvToPoly, polyToMv]
  · intro j
    simp only [RingHom.coe_comp, Function.comp_apply, mvToPoly, MvPolynomial.eval₂Hom_X',
      polyToMv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, RingHom.id_apply]
    rw [eq_otherIndex i j]

/-- **The chart `D₊(Tᵢ)` of `Proj R[T₀, T₁]` is the affine line**, with coordinate
`T_{1 - i} / Tᵢ`. -/
def chartPolyEquiv (i : Fin 2) : Polynomial R ≃+* Away (polyGrading R 1) (MvPolynomial.X i) :=
  (RingEquiv.ofRingHom (polyToMv R i) (mvToPoly R i) (polyToMv_comp_mvToPoly R i)
    (mvToPoly_comp_polyToMv R i)).trans (chartEquiv R 1 i)

/-- `chartPolyEquiv` sends a constant `r` to the image of `r` in `D₊(Tᵢ)`. -/
@[simp]
theorem chartPolyEquiv_C (i : Fin 2) (r : R) :
    chartPolyEquiv R i (Polynomial.C r) = coeffToAway R 1 i r := by
  simp [chartPolyEquiv, polyToMv]

/-- `chartPolyEquiv` sends the variable `X` to the chart coordinate `T_{1 - i} / Tᵢ`. -/
@[simp]
theorem chartPolyEquiv_X (i : Fin 2) :
    chartPolyEquiv R i Polynomial.X = chartCoord R 1 i (otherIndex i) := by
  simp [chartPolyEquiv, polyToMv]

/-! ### The overlap `D₊(T₀T₁)` -/

/-- The ring of the overlap `D₊(T₀ T₁)`. -/
abbrev overlapRing : Type u :=
  Away (polyGrading R 1) (MvPolynomial.X 0 * MvPolynomial.X 1)

/-- The restriction from `D₊(T₀)` to the overlap. -/
abbrev awayMapZero : Away (polyGrading R 1) (MvPolynomial.X 0) →+* overlapRing R :=
  awayMap (polyGrading R 1) (X_mem_one R 1 1) rfl

/-- The restriction from `D₊(T₁)` to the overlap. -/
abbrev awayMapOne : Away (polyGrading R 1) (MvPolynomial.X 1) →+* overlapRing R :=
  awayMap (polyGrading R 1) (X_mem_one R 1 0) (mul_comm _ _)

/-- The coordinate `T₁ / T₀` of the `x`-chart is the element at which the overlap localizes. -/
theorem chartCoord_zero_eq_isLocalizationElem :
    chartCoord R 1 0 (otherIndex 0) =
      Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1) := by
  ext
  simp [chartCoord, otherIndex, Away.val_mk]

/-- The restriction from `D₊(T₀)` to the overlap sends the image of `r : R` to the image of `r`. -/
theorem awayMapZero_coeffToAway (r : R) :
    awayMapZero R (coeffToAway R 1 0 r) =
      algebraMap (polyGrading R 1 0) (overlapRing R) (algebraMap R (polyGrading R 1 0) r) := by
  simp only [coeffToAway, RingHom.comp_apply, awayMapZero, algebraMap_eq]
  exact awayMap_fromZeroRingHom _ _ _ _

/-- The restriction from `D₊(T₁)` to the overlap sends the image of `r : R` to the image of `r`. -/
theorem awayMapOne_coeffToAway (r : R) :
    awayMapOne R (coeffToAway R 1 1 r) =
      algebraMap (polyGrading R 1 0) (overlapRing R) (algebraMap R (polyGrading R 1 0) r) := by
  simp only [coeffToAway, RingHom.comp_apply, awayMapOne, algebraMap_eq]
  exact awayMap_fromZeroRingHom _ _ _ _

/-- On the overlap the two chart coordinates `T₁ / T₀` and `T₀ / T₁` are inverse. -/
theorem awayMapOne_chartCoord_mul_awayMapZero_chartCoord :
    awayMapOne R (chartCoord R 1 1 (otherIndex 1)) *
      awayMapZero R (chartCoord R 1 0 (otherIndex 0)) = 1 := by
  ext
  simp only [awayMapOne, awayMapZero, chartCoord, otherIndex, awayMap_mk, val_mul, Away.val_mk,
    val_one, Localization.mk_mul]
  rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- The coordinate `T₁ / T₀` is a unit on the overlap. -/
theorem isUnit_awayMapZero_chartCoord :
    IsUnit (awayMapZero R (chartCoord R 1 0 (otherIndex 0))) :=
  .of_mul_eq_one_right _ (awayMapOne_chartCoord_mul_awayMapZero_chartCoord R)

/-- The ring map `R[T, T⁻¹] → R[T₀, T₁]_{(T₀T₁)}`, `T ↦ T₁ / T₀`. -/
def laurentToOverlap : LaurentPolynomial R →+* overlapRing R :=
  IsLocalization.Away.lift (Polynomial.X : Polynomial R)
    (g := (awayMapZero R).comp (chartPolyEquiv R 0).toRingHom)
    (by simpa using isUnit_awayMapZero_chartCoord R)

/-- On polynomials, `laurentToOverlap` is the `x`-chart `R[X] ≅ D₊(T₀)` followed by restriction to
the overlap. -/
theorem laurentToOverlap_comp_toLaurent :
    (laurentToOverlap R).comp Polynomial.toLaurent =
      (awayMapZero R).comp (chartPolyEquiv R 0).toRingHom :=
  IsLocalization.Away.lift_comp _ _

/-- `laurentToOverlap` sends `T` to `T₁ / T₀`. -/
theorem laurentToOverlap_T_one :
    laurentToOverlap R (LaurentPolynomial.T 1) =
      awayMapZero R (chartCoord R 1 0 (otherIndex 0)) := by
  simpa using congrArg (fun f => f Polynomial.X) (laurentToOverlap_comp_toLaurent R)

/-- On polynomials, `T ↦ T⁻¹` followed by `laurentToOverlap` is the `y`-chart `R[X] ≅ D₊(T₁)`
followed by restriction to the overlap. -/
theorem laurentToOverlap_comp_invert_comp_toLaurent :
    ((laurentToOverlap R).comp LaurentPolynomial.invert.toRingEquiv.toRingHom).comp
        Polynomial.toLaurent =
      (awayMapOne R).comp (chartPolyEquiv R 1).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    have h := congrArg (fun f => f (Polynomial.C r)) (laurentToOverlap_comp_toLaurent R)
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.toLaurent_C,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, chartPolyEquiv_C] at h ⊢
    rw [show LaurentPolynomial.invert.toRingEquiv (LaurentPolynomial.C r) =
      LaurentPolynomial.C r from LaurentPolynomial.invert_C r, h, awayMapZero_coeffToAway,
      awayMapOne_coeffToAway]
  · simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.toLaurent_X,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, chartPolyEquiv_X]
    rw [show LaurentPolynomial.invert.toRingEquiv (LaurentPolynomial.T 1 : LaurentPolynomial R) =
      LaurentPolynomial.T (-1) from LaurentPolynomial.invert_T 1]
    have h1 : laurentToOverlap R (LaurentPolynomial.T (-1)) *
        awayMapZero R (chartCoord R 1 0 (otherIndex 0)) = 1 := by
      rw [← laurentToOverlap_T_one, ← map_mul, ← LaurentPolynomial.T_add]
      simp
    exact (isUnit_awayMapZero_chartCoord R).mul_left_injective
      (h1.trans (awayMapOne_chartCoord_mul_awayMapZero_chartCoord R).symm)

/-- The ring map `R[T₀, T₁]_{(T₀T₁)} → R[T, T⁻¹]` through the `x`-chart. -/
def overlapToLaurent : overlapRing R →+* LaurentPolynomial R :=
  letI : Algebra (Away (polyGrading R 1) (MvPolynomial.X 0)) (overlapRing R) :=
    (awayMapZero R).toAlgebra
  haveI : IsLocalization.Away
      (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1)) (overlapRing R) :=
    Away.isLocalization_mul (X_mem_one R 1 0) (X_mem_one R 1 1) rfl one_ne_zero
  IsLocalization.Away.lift (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1))
    (g := Polynomial.toLaurent.comp (chartPolyEquiv R 0).symm.toRingHom)
    (by
      rw [← chartCoord_zero_eq_isLocalizationElem]
      have : (chartPolyEquiv R 0).symm (chartCoord R 1 0 (otherIndex 0)) = Polynomial.X := by
        rw [RingEquiv.symm_apply_eq, chartPolyEquiv_X]
      simpa [this] using LaurentPolynomial.isUnit_T (R := R) 1)

/-- On `D₊(T₀)`, `overlapToLaurent` is the inverse of the `x`-chart followed by
`R[X] → R[T, T⁻¹]`. -/
theorem overlapToLaurent_comp_awayMapZero :
    (overlapToLaurent R).comp (awayMapZero R) =
      Polynomial.toLaurent.comp (chartPolyEquiv R 0).symm.toRingHom := by
  let : Algebra (Away (polyGrading R 1) (MvPolynomial.X 0)) (overlapRing R) :=
    (awayMapZero R).toAlgebra
  have : IsLocalization.Away
      (Away.isLocalizationElem (X_mem_one R 1 0) (X_mem_one R 1 1)) (overlapRing R) :=
    Away.isLocalization_mul (X_mem_one R 1 0) (X_mem_one R 1 1) rfl one_ne_zero
  exact IsLocalization.Away.lift_comp _ _

/-- On `D₊(T₁)`, `overlapToLaurent` is the inverse of the `y`-chart followed by
`R[X] → R[T, T⁻¹]` and `T ↦ T⁻¹`. -/
theorem overlapToLaurent_comp_awayMapOne :
    (overlapToLaurent R).comp (awayMapOne R) =
      (LaurentPolynomial.invert.toRingEquiv.toRingHom.comp Polynomial.toLaurent).comp
        (chartPolyEquiv R 1).symm.toRingHom := by
  have hL : (overlapToLaurent R).comp (laurentToOverlap R) = RingHom.id _ := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R)) ?_
    change ((overlapToLaurent R).comp (laurentToOverlap R)).comp Polynomial.toLaurent =
      (RingHom.id _).comp Polynomial.toLaurent
    rw [RingHom.comp_assoc, laurentToOverlap_comp_toLaurent, ← RingHom.comp_assoc,
      overlapToLaurent_comp_awayMapZero, RingHom.comp_assoc,
      RingEquiv.symm_toRingHom_comp_toRingHom]
    rfl
  have H : ((overlapToLaurent R).comp (awayMapOne R)).comp (chartPolyEquiv R 1).toRingHom =
      LaurentPolynomial.invert.toRingEquiv.toRingHom.comp Polynomial.toLaurent := by
    rw [RingHom.comp_assoc, ← laurentToOverlap_comp_invert_comp_toLaurent, ← RingHom.comp_assoc,
      ← RingHom.comp_assoc, hL]
    rfl
  rw [← H, RingHom.comp_assoc]
  ext x
  simp

/-! ### Morphisms out of the glued projective line -/

/-- The second coordinate of the overlap, `y ↦ T⁻¹`, is inversion after the localization map. -/
theorem inverseCoordinate_eq :
    (projectiveLineOverlapInverseCoordinate R).toRingHom =
      LaurentPolynomial.invert.toRingEquiv.toRingHom.comp Polynomial.toLaurent := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [projectiveLineOverlapInverseCoordinate]
  · simp [projectiveLineOverlapInverseCoordinate]

/-- **The gluing relation of the projective line on the overlap**, from the pullback square of the
two charts: the `x`-chart on the punctured line is the `y`-chart after `y ↦ T⁻¹`. -/
theorem puncturedChart_comp_xChart :
    projectiveLinePuncturedChart R ≫ projectiveLineXChart R =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫
        projectiveLineYChart R :=
  (isPullback_projectiveLineCharts R).w

/-- The pullback of a monomorphism along itself has equal projections. -/
theorem pullback_fst_eq_snd_of_mono {X Y : Scheme.{u}} (f : X ⟶ Y) [Mono f] :
    pullback.fst f f = pullback.snd f f :=
  (cancel_mono f).1 pullback.condition

/-- Swapping the factors of a pullback swaps the sides of a compatibility of its projections. -/
private theorem pullback_snd_comp_eq_fst_comp {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z W : C} {f : X ⟶ Z} {g : Y ⟶ Z} {a b : _ ⟶ W}
    (h : pullback.fst f g ≫ a = pullback.snd f g ≫ b) :
    pullback.fst g f ≫ b = pullback.snd g f ≫ a := by
  rw [← cancel_epi (pullbackSymmetry f g).hom, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackSymmetry_hom_comp_snd_assoc]
  exact h.symm

/-- Morphisms `g₀`, `g₁` out of the two charts of the glued line that agree on the punctured line
agree on every pairwise pullback of the gluing cover. -/
theorem lineDesc_compat {Y : Scheme.{u}} (g₀ g₁ : Spec (.of (Polynomial R)) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ g₀ =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ g₁)
    (x y : (projectiveLineGluingData R).openCover.I₀) :
    pullback.fst ((projectiveLineGluingData R).openCover.f x)
        ((projectiveLineGluingData R).openCover.f y) ≫ (if x.down then g₁ else g₀) =
      pullback.snd ((projectiveLineGluingData R).openCover.f x)
        ((projectiveLineGluingData R).openCover.f y) ≫ (if y.down then g₁ else g₀) := by
  have h₀₁ : pullback.fst (projectiveLineXChart R) (projectiveLineYChart R) ≫ g₀ =
      pullback.snd (projectiveLineXChart R) (projectiveLineYChart R) ≫ g₁ := by
    rw [← (isPullback_projectiveLineCharts R).isoPullback_inv_fst,
      ← (isPullback_projectiveLineCharts R).isoPullback_inv_snd, Category.assoc, Category.assoc, h]
  rcases x with ⟨x⟩
  rcases y with ⟨y⟩
  cases x <;> cases y
  · exact congrArg (· ≫ g₀) (pullback_fst_eq_snd_of_mono (projectiveLineXChart R))
  · exact h₀₁
  · exact pullback_snd_comp_eq_fst_comp h₀₁
  · exact congrArg (· ≫ g₁) (pullback_fst_eq_snd_of_mono (projectiveLineYChart R))

/-- A morphism out of the glued projective line, from morphisms out of its two charts that agree on
the overlap. -/
def lineDesc {Y : Scheme.{u}} (g₀ g₁ : Spec (.of (Polynomial R)) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ g₀ =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ g₁) :
    projectiveLine R ⟶ Y :=
  (projectiveLineGluingData R).openCover.glueMorphisms
    (fun i => if i.down then g₁ else g₀) (lineDesc_compat R g₀ g₁ h)

/-- `lineDesc g₀ g₁ h` restricts to `g₀` on the `x`-chart. -/
@[reassoc (attr := simp)]
theorem xChart_lineDesc {Y : Scheme.{u}} (g₀ g₁ : Spec (.of (Polynomial R)) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ g₀ =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ g₁) :
    projectiveLineXChart R ≫ lineDesc R g₀ g₁ h = g₀ := by
  exact Scheme.Cover.ι_glueMorphisms (projectiveLineGluingData R).openCover
    (fun i => if i.down then g₁ else g₀) (lineDesc_compat R g₀ g₁ h) (projectiveLineXIndex R)

/-- `lineDesc g₀ g₁ h` restricts to `g₁` on the `y`-chart. -/
@[reassoc (attr := simp)]
theorem yChart_lineDesc {Y : Scheme.{u}} (g₀ g₁ : Spec (.of (Polynomial R)) ⟶ Y)
    (h : projectiveLinePuncturedChart R ≫ g₀ =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫ g₁) :
    projectiveLineYChart R ≫ lineDesc R g₀ g₁ h = g₁ := by
  exact Scheme.Cover.ι_glueMorphisms (projectiveLineGluingData R).openCover
    (fun i => if i.down then g₁ else g₀) (lineDesc_compat R g₀ g₁ h) (projectiveLineYIndex R)

/-- Two morphisms out of the glued projective line agreeing on both charts are equal. -/
theorem line_hom_ext {Y : Scheme.{u}} (f₁ f₂ : projectiveLine R ⟶ Y)
    (h₀ : projectiveLineXChart R ≫ f₁ = projectiveLineXChart R ≫ f₂)
    (h₁ : projectiveLineYChart R ≫ f₁ = projectiveLineYChart R ≫ f₂) : f₁ = f₂ := by
  refine (projectiveLineGluingData R).openCover.hom_ext _ _ fun i => ?_
  rcases i with ⟨i⟩
  cases i
  · exact h₀
  · exact h₁

/-! ### The two halves of the isomorphism -/

/-- Composition of `Spec.map` of two ring maps is `Spec.map` of their composite. -/
theorem spec_map_comp_spec_map {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (a : B →+* C) (b : A →+* B) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) =
      Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp]
  rfl

/-- The chart `Spec R[X] ≅ D₊(Tᵢ) ⊆ Proj R[T₀, T₁]`. -/
def projChart (i : Fin 2) : Spec (.of (Polynomial R)) ⟶ Proj (polyGrading R 1) :=
  Spec.map (CommRingCat.ofHom (chartPolyEquiv R i).symm.toRingHom) ≫
    Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos

/-- The two charts of `Proj R[T₀, T₁]` agree on the overlap, with the gluing of the line. -/
theorem puncturedChart_comp_projChart :
    projectiveLinePuncturedChart R ≫ projChart R 0 =
      Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate R).toRingHom) ≫
        projChart R 1 := by
  have h1 : (overlapToLaurent R).comp (awayMapOne R) =
      (projectiveLineOverlapInverseCoordinate R).toRingHom.comp
        (chartPolyEquiv R 1).symm.toRingHom := by
    rw [overlapToLaurent_comp_awayMapOne, inverseCoordinate_eq]
  simp only [projChart, projectiveLinePuncturedChart, ← Category.assoc, spec_map_comp_spec_map]
  rw [← overlapToLaurent_comp_awayMapZero, ← h1, ← spec_map_comp_spec_map,
    ← spec_map_comp_spec_map, Category.assoc, Category.assoc]
  congr 1
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

/-- **The glued projective line maps to `Proj R[T₀, T₁]`**, the `x`-chart onto `D₊(T₀)` and the
`y`-chart onto `D₊(T₁)`. -/
def lineToProj : projectiveLine R ⟶ Proj (polyGrading R 1) :=
  lineDesc R (projChart R 0) (projChart R 1) (puncturedChart_comp_projChart R)

/-- The chart of the glued line corresponding to `D₊(Tᵢ)`. -/
def lineChart (i : Fin 2) : Spec (.of (Polynomial R)) ⟶ projectiveLine R :=
  if i = 0 then projectiveLineXChart R else projectiveLineYChart R

/-- `D₊(Tᵢ) ≅ Spec R[X]` followed by the corresponding chart of the glued line. -/
def awayToLine (i : Fin 2) :
    Spec (.of (Away (polyGrading R 1) (MvPolynomial.X i))) ⟶ projectiveLine R :=
  Spec.map (CommRingCat.ofHom (chartPolyEquiv R i).toRingHom) ≫ lineChart R i

/-- The two charts of the glued line agree on `D₊(T₀) ∩ D₊(T₁)`. -/
theorem pullback_fst_awayToLine_zero :
    pullback.fst (Proj.awayι (polyGrading R 1) (MvPolynomial.X 0) (X_mem_one R 1 0) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 1) (X_mem_one R 1 1) Nat.one_pos) ≫
        awayToLine R 0 =
      pullback.snd (Proj.awayι (polyGrading R 1) (MvPolynomial.X 0) (X_mem_one R 1 0) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X 1) (X_mem_one R 1 1) Nat.one_pos) ≫
        awayToLine R 1 := by
  rw [← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_left (polyGrading R 1) (X_mem_one R 1 0)
      Nat.one_pos (X_mem_one R 1 1) Nat.one_pos rfl,
    ← Proj.pullbackAwayιIso_hom_SpecMap_awayMap_right (polyGrading R 1) (X_mem_one R 1 0)
      Nat.one_pos (X_mem_one R 1 1) Nat.one_pos rfl, Category.assoc, Category.assoc]
  congr 1
  have h0 : (awayMapZero R).comp (chartPolyEquiv R 0).toRingHom =
      (laurentToOverlap R).comp Polynomial.toLaurent :=
    (laurentToOverlap_comp_toLaurent R).symm
  have h1 : (awayMapOne R).comp (chartPolyEquiv R 1).toRingHom =
      (laurentToOverlap R).comp (projectiveLineOverlapInverseCoordinate R).toRingHom := by
    rw [inverseCoordinate_eq, ← RingHom.comp_assoc]
    exact (laurentToOverlap_comp_invert_comp_toLaurent R).symm
  simp only [awayToLine, lineChart, ← Category.assoc, spec_map_comp_spec_map]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero]
  show Spec.map (CommRingCat.ofHom ((awayMapZero R).comp (chartPolyEquiv R 0).toRingHom)) ≫
      projectiveLineXChart R =
    Spec.map (CommRingCat.ofHom ((awayMapOne R).comp (chartPolyEquiv R 1).toRingHom)) ≫
      projectiveLineYChart R
  rw [h0, h1, ← spec_map_comp_spec_map, ← spec_map_comp_spec_map, Category.assoc,
    Category.assoc]
  congr 1
  exact puncturedChart_comp_xChart R

/-- The compatibility of the charts `awayToLine` on the pairwise intersections. -/
theorem pullback_fst_awayToLine (x y : Fin 2) :
    pullback.fst (Proj.awayι (polyGrading R 1) (MvPolynomial.X x) (X_mem_one R 1 x) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X y) (X_mem_one R 1 y) Nat.one_pos) ≫
        awayToLine R x =
      pullback.snd (Proj.awayι (polyGrading R 1) (MvPolynomial.X x) (X_mem_one R 1 x) Nat.one_pos)
        (Proj.awayι (polyGrading R 1) (MvPolynomial.X y) (X_mem_one R 1 y) Nat.one_pos) ≫
        awayToLine R y := by
  rcases Fin.exists_fin_two.mp ⟨x, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨y, rfl⟩ with rfl | rfl
  · exact congrArg (· ≫ awayToLine R 0) (pullback_fst_eq_snd_of_mono _)
  · exact pullback_fst_awayToLine_zero R
  · exact pullback_snd_comp_eq_fst_comp (pullback_fst_awayToLine_zero R)
  · exact congrArg (· ≫ awayToLine R 1) (pullback_fst_eq_snd_of_mono _)

/-- The morphisms `awayToLine` agree on every pairwise pullback of the standard affine cover of
`Proj R[T₀, T₁]`. -/
theorem projToLine_compat (x y : (affineChartCover R 1).openCover.I₀) :
    pullback.fst ((affineChartCover R 1).openCover.f x) ((affineChartCover R 1).openCover.f y) ≫
        awayToLine R x =
      pullback.snd ((affineChartCover R 1).openCover.f x)
        ((affineChartCover R 1).openCover.f y) ≫ awayToLine R y :=
  pullback_fst_awayToLine R x y

/-- **`Proj R[T₀, T₁]` maps to the glued projective line**, `D₊(T₀)` onto the `x`-chart and
`D₊(T₁)` onto the `y`-chart. -/
def projToLine : Proj (polyGrading R 1) ⟶ projectiveLine R :=
  (affineChartCover R 1).openCover.glueMorphisms (fun i => awayToLine R i) (projToLine_compat R)

/-- `projToLine` restricts to `awayToLine i` on `D₊(Tᵢ)`. -/
theorem awayι_projToLine (i : Fin 2) :
    Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos ≫
      projToLine R = awayToLine R i := by
  exact Scheme.Cover.ι_glueMorphisms (affineChartCover R 1).openCover
    (fun i => awayToLine R i) (projToLine_compat R) i

/-- `projToLine` is a left inverse of `lineToProj`. -/
theorem lineToProj_projToLine : lineToProj R ≫ projToLine R = 𝟙 _ := by
  apply line_hom_ext
  · rw [lineToProj, xChart_lineDesc_assoc, projChart, Category.assoc, awayι_projToLine,
      awayToLine, ← Category.assoc, spec_map_comp_spec_map, Category.comp_id]
    simp [lineChart]
  · rw [lineToProj, yChart_lineDesc_assoc, projChart, Category.assoc, awayι_projToLine,
      awayToLine, ← Category.assoc, spec_map_comp_spec_map, Category.comp_id]
    simp [lineChart]

/-- `lineToProj` is a left inverse of `projToLine`. -/
theorem projToLine_lineToProj : projToLine R ≫ lineToProj R = 𝟙 _ := by
  refine (affineChartCover R 1).openCover.hom_ext _ _ fun i => ?_
  change Fin 2 at i
  show Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos ≫ _ =
    Proj.awayι (polyGrading R 1) (MvPolynomial.X i) (X_mem_one R 1 i) Nat.one_pos ≫ 𝟙 _
  rw [← Category.assoc, awayι_projToLine, awayToLine, Category.assoc, Category.comp_id]
  rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with rfl | rfl
  · simp only [lineChart, Fin.isValue, ↓reduceIte, lineToProj, xChart_lineDesc,
      projChart, ← Category.assoc, spec_map_comp_spec_map]
    simp
  · simp only [lineChart, Fin.isValue, one_ne_zero, ↓reduceIte, lineToProj,
      yChart_lineDesc, projChart, ← Category.assoc, spec_map_comp_spec_map]
    simp

/-- **The glued projective line over `R` is `Proj R[T₀, T₁]`.** -/
def projectiveLineIsoProj : projectiveLine R ≅ Proj (polyGrading R 1) where
  hom := lineToProj R
  inv := projToLine R
  hom_inv_id := lineToProj_projToLine R
  inv_hom_id := projToLine_lineToProj R

/-! ### The relative projective line -/

/-- **The relative projective line over `S` is projective `1`-space over `S`**: both are base
changes to `S` of an integral model, and the two integral models are identified by
`projectiveLineIsoProj`. -/
def relativeProjectiveLineIsoProjectiveSpaceOver (S : Scheme.{u}) :
    Stacks.Chow.relativeProjectiveLine S ≅ projectiveSpaceOver 1 S :=
  letI e : projectiveLine (ULift.{u} ℤ) ≅ projectiveSpaceAtUniverse.{u} 1 :=
    projectiveLineIsoProj (ULift.{u} ℤ)
  asIso (pullback.map (terminal.from S) (terminal.from (projectiveLine (ULift.{u} ℤ)))
    (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} 1))
    (𝟙 S) e.hom (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _))

/-- The identification of the relative projective line with projective `1`-space over `S` lies over
`S`. -/
@[reassoc (attr := simp)]
theorem relativeProjectiveLineIsoProjectiveSpaceOver_hom_fst (S : Scheme.{u}) :
    (relativeProjectiveLineIsoProjectiveSpaceOver S).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  rw [relativeProjectiveLineIsoProjectiveSpaceOver, asIso_hom, pullback.lift_fst,
    Category.comp_id]

variable (k W : Type u) [Field k] [AddCommGroup W] [Module k W]

/-- **The relative projective line over `Spec k` is `𝐏(W)` for a plane `W`**, through a basis of
`W` indexed by `Fin 2`. -/
def relativeProjectiveLineIsoProjectiveSpaceOfModule (b : Module.Basis (Fin 2) k W) :
    Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ≅ projectiveSpaceOfModule k W :=
  relativeProjectiveLineIsoProjectiveSpaceOver (Spec (.of k)) ≪≫ basisProjectiveSpaceIso b

/-- The identification of the relative projective line with `𝐏(W)` lies over `Spec k`. -/
@[reassoc (attr := simp)]
theorem relativeProjectiveLineIsoProjectiveSpaceOfModule_hom_comp_toSpec
    (b : Module.Basis (Fin 2) k W) :
    (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom ≫
        projectiveSpaceOfModuleToSpec k W =
      Stacks.Chow.relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k) := by
  rw [relativeProjectiveLineIsoProjectiveSpaceOfModule, Iso.trans_hom, Category.assoc,
    basisProjectiveSpaceIso_hom_comp_toSpec, relativeProjectiveLineIsoProjectiveSpaceOver_hom_fst]
  rfl

/-! ### The points `0` and `∞` of `𝐏(W)` -/

variable (b : Module.Basis (Fin 2) k W)

/-- **The point `0` of `𝐏(W)`**, the image of the zero section of the relative projective line. -/
def zeroPoint : projectiveSpaceOfModule k W :=
  (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom
    (Stacks.Chow.lineZeroSection (Spec (.of k)) (IsLocalRing.closedPoint k))

/-- **The point `∞` of `𝐏(W)`**, the image of the infinity section of the relative projective
line. -/
@[ega "II 7.4.14"]
def infinityPoint : projectiveSpaceOfModule k W :=
  (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom
    (Stacks.Chow.lineInfinitySection (Spec (.of k)) (IsLocalRing.closedPoint k))

/-- The image of a closed immersion out of `Spec k` is the closed point it hits. -/
theorem isClosed_singleton_of_isClosedImmersion {Y : Scheme.{u}}
    (σ : Spec (.of k) ⟶ Y) [IsClosedImmersion σ] :
    IsClosed ({σ (IsLocalRing.closedPoint k)} : Set Y) := by
  have h : Set.range σ.base = {σ (IsLocalRing.closedPoint k)} := by
    ext y
    refine ⟨?_, ?_⟩
    · rintro ⟨x, rfl⟩
      rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
      rfl
    · rintro rfl
      exact ⟨_, rfl⟩
  rw [← h]
  exact σ.isClosedEmbedding.isClosed_range

/-- The point `0` of `𝐏(W)` is closed. -/
theorem isClosed_zeroPoint : IsClosed ({zeroPoint k W b} : Set (projectiveSpaceOfModule k W)) := by
  have := isClosed_singleton_of_isClosedImmersion k
    (Stacks.Chow.lineZeroSection (Spec (.of k)) ≫
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom)
  exact this

/-- The point `∞` of `𝐏(W)` is closed. -/
@[ega "II 7.4.14" "partial"]
theorem isClosed_infinityPoint :
    IsClosed ({infinityPoint k W b} : Set (projectiveSpaceOfModule k W)) := by
  have := isClosed_singleton_of_isClosedImmersion k
    (Stacks.Chow.lineInfinitySection (Spec (.of k)) ≫
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom)
  exact this

/-- The points `0` and `∞` of `𝐏(W)` are distinct. -/
theorem zeroPoint_ne_infinityPoint : zeroPoint k W b ≠ infinityPoint k W b := by
  intro h
  have hinj : Function.Injective
      (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom.base :=
    (Scheme.homeoOfIso (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b)).injective
  exact Set.disjoint_iff.mp
    (Stacks.Chow.disjoint_range_lineZeroSection_lineInfinitySection (Spec (.of k)))
    ⟨⟨_, rfl⟩, ⟨IsLocalRing.closedPoint k, (hinj h).symm⟩⟩

/-- The zero section of the relative projective line, read in `𝐏(W)`, hits `0`. -/
@[simp]
theorem lineZeroSection_comp_hom_apply :
    (Stacks.Chow.lineZeroSection (Spec (.of k)) ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom)
        (IsLocalRing.closedPoint k) = zeroPoint k W b :=
  rfl

/-- The infinity section of the relative projective line, read in `𝐏(W)`, hits `∞`. -/
@[simp]
theorem lineInfinitySection_comp_hom_apply :
    (Stacks.Chow.lineInfinitySection (Spec (.of k)) ≫
        (relativeProjectiveLineIsoProjectiveSpaceOfModule k W b).hom)
        (IsLocalRing.closedPoint k) = infinityPoint k W b :=
  rfl

end AlgebraicGeometry.ProjectiveLineBridge

end
