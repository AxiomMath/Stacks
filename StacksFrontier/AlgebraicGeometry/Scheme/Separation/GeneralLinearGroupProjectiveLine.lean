module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLinePoints
public import StacksFrontier.AlgebraicGeometry.Scheme.Separation.GeneralLinearGroup

/-!
# The general linear scheme surjects onto the projective line

The first row `(a, b)` of the generic invertible two-by-two matrix is nowhere zero, so it defines
the morphism `[a : b] : GL₂ → ℙ¹`. It is surjective, which is the second half of the example: an
affine scheme can surject onto a scheme that admits no immersion into any affine scheme.

## Main definitions

* `AlgebraicGeometry.generalLinearTwoFirstRowCover`: the cover of `GL₂` by the two standard opens
  `D(a)` and `D(b)`.
* `AlgebraicGeometry.generalLinearTwoChartToProjectiveLine`: on `D(a)` the point `b/a` of the
  first chart, on `D(b)` the point `a/b` of the second.
* `AlgebraicGeometry.generalLinearTwoToProjectiveLine`: the morphism `[a : b]`.

## Main results

* `AlgebraicGeometry.surjective_generalLinearTwoToProjectiveLine`: `[a : b]` is surjective.

## Implementation notes

`ℙ¹` is the gluing of two affine lines, so a morphism *into* it is not given by a ring map and
has to be glued from an open cover of the source. The cover used is the two standard opens of the
first-row entries, which cover `GL₂` because those entries generate the unit ideal
(`AlgebraicGeometry.span_firstRow_eq_top`). Over `D(a)` the morphism is `b/a` read in the first
chart and over `D(b)` it is `a/b` read in the second.

The agreement of the two on the overlap is where the gluing of `ℙ¹` enters. Both restrictions
factor through `Spec k[T, T⁻¹]`: the ring map `k[T, T⁻¹] → k[a, b, c, d, 1/(ad - bc)][1/a][1/b]`
sending `T` to `b/a` carries the first chart's coordinate to `b/a` and the second chart's
coordinate to `a/b`, because the two coordinates correspond to `T` and `T⁻¹`. The two
restrictions are therefore the two sides of the pullback square
`AlgebraicGeometry.isPullback_projectiveLineCharts` that defines `ℙ¹`, precomposed with that one
morphism, hence equal. The overlap is identified with that double localization by
`CommRingCat.isPushout_of_isLocalization`, which is what turns the categorical pullback of the
two members of the cover into a ring.

Surjectivity is proved by exhibiting a section over each chart of `ℙ¹`: the matrices
`!![1, X; 0, 1]` and `!![X, 1; -1, 0]`, both of determinant `1`, split the morphism over the
first and the second chart respectively. Since every point of `ℙ¹` lies in the first chart or is
the point at infinity, which lies in the second, this covers `ℙ¹`.

## References

* [Stacks Project, Tag 01KX](https://stacks.math.columbia.edu/tag/01KX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The localization of the coordinate ring of `GL₂` inverting the first-row entry `(0, j)`. -/
abbrev generalLinearTwoAway (j : Fin 2) :=
  Localization.Away (generalLinearTwoCoordinate k 0 j)

/-- A two-by-two matrix over a `k`-algebra whose determinant is a unit induces a ring map out of
the coordinate ring of `GL₂`, by the universal property of inverting the determinant. -/
noncomputable def generalLinearTwoHom {A : Type u} [CommRing A] [Algebra k A]
    (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) :
    generalLinearTwoCoordinateRing k →+* A :=
  IsLocalization.Away.lift
    (g := MvPolynomial.eval₂Hom (algebraMap k A) (fun p : Fin 2 × Fin 2 => M p.1 p.2))
    (generalLinearTwoDeterminant k) (by
      have hdet : MvPolynomial.eval₂Hom (algebraMap k A)
          (fun p : Fin 2 × Fin 2 => M p.1 p.2) (generalLinearTwoDeterminant k) = M.det := by
        change MvPolynomial.eval₂Hom _ _ ((Matrix.mvPolynomialX (Fin 2) (Fin 2) k).det) = _
        rw [Matrix.det_fin_two, Matrix.det_fin_two]
        simp
      rw [hdet]
      exact hM)

/-- The ring map induced by a matrix `M` sends the coordinate `(i, j)` to the entry `M i j`. -/
@[simp]
lemma generalLinearTwoHom_coordinate {A : Type u} [CommRing A] [Algebra k A]
    (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) (i j : Fin 2) :
    generalLinearTwoHom k M hM (generalLinearTwoCoordinate k i j) = M i j := by
  rw [generalLinearTwoCoordinate, generalLinearTwoHom, IsLocalization.Away.lift_eq]
  simp

/-- The two-member affine open cover of `GL₂` by the standard opens of the two first-row entries,
which cover because those entries generate the unit ideal. -/
noncomputable abbrev generalLinearTwoFirstRowCover : (generalLinearTwoScheme k).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of (generalLinearTwoCoordinateRing k))
    (fun j : Fin 2 => generalLinearTwoCoordinate k 0 j) (span_firstRow_eq_top k)).openCover

/-- The `j`-th member of the first-row cover is the spectrum of the localization inverting the
`(0, j)` entry. -/
@[simp]
lemma generalLinearTwoFirstRowCover_f (j : Fin 2) :
    (generalLinearTwoFirstRowCover k).f j =
      Spec.map (CommRingCat.ofHom
        (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k j))) :=
  rfl

/-- The open immersion of the standard open of the `(0, j)` entry into `GL₂`. -/
noncomputable abbrev generalLinearTwoFirstRowOpen (j : Fin 2) :
    Spec (CommRingCat.of (generalLinearTwoAway k j)) ⟶ generalLinearTwoScheme k :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k j)))

/-- The other first-row index: `b` for `a` and `a` for `b`. -/
abbrev generalLinearTwoOther (j : Fin 2) : Fin 2 := 1 - j

/-- The other first-row index of `0` is `1`. -/
@[simp]
lemma generalLinearTwoOther_zero : generalLinearTwoOther 0 = 1 := by decide

/-- The other first-row index of `1` is `0`. -/
@[simp]
lemma generalLinearTwoOther_one : generalLinearTwoOther 1 = 0 := by decide

/-- Over `D(a)` this is the ratio `b / a`, and over `D(b)` the ratio `a / b`. -/
noncomputable def generalLinearTwoRatio (j : Fin 2) : generalLinearTwoAway k j :=
  algebraMap _ _ (generalLinearTwoCoordinate k 0 (generalLinearTwoOther j)) *
    IsLocalization.Away.invSelf (generalLinearTwoCoordinate k 0 j)

/-- The chart of `ℙ¹` in which the morphism is read over the standard open of the `(0, j)` entry:
the first chart over `D(a)` and the second over `D(b)`. -/
noncomputable def generalLinearTwoProjectiveChart (j : Fin 2) :
    Spec (.of (Polynomial k)) ⟶ projectiveLine k :=
  if j = 0 then projectiveLineXChart k else projectiveLineYChart k

/-- Over `D(a)` the chart is the first chart of `ℙ¹`. -/
@[simp]
lemma generalLinearTwoProjectiveChart_zero :
    generalLinearTwoProjectiveChart k 0 = projectiveLineXChart k := by
  rw [generalLinearTwoProjectiveChart]
  simp

/-- Over `D(b)` the chart is the second chart of `ℙ¹`. -/
@[simp]
lemma generalLinearTwoProjectiveChart_one :
    generalLinearTwoProjectiveChart k 1 = projectiveLineYChart k := by
  rw [generalLinearTwoProjectiveChart]
  norm_num

/-- The morphism `[a : b]` restricted to the standard open of the `(0, j)` entry: the point
`b/a` of the first chart over `D(a)`, and the point `a/b` of the second chart over `D(b)`. -/
noncomputable def generalLinearTwoChartToProjectiveLine (j : Fin 2) :
    Spec (CommRingCat.of (generalLinearTwoAway k j)) ⟶ projectiveLine k :=
  Spec.map (CommRingCat.ofHom (Polynomial.aeval (generalLinearTwoRatio k j)).toRingHom) ≫
    generalLinearTwoProjectiveChart k j

/-- Clearing denominators in the ratio: on the standard open of the `(0, j)` entry, that entry
times the ratio is the other entry. -/
lemma generalLinearTwoRatio_mul_coordinate (j : Fin 2) :
    generalLinearTwoRatio k j *
        algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k j)
          (generalLinearTwoCoordinate k 0 j) =
      algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k j)
        (generalLinearTwoCoordinate k 0 (generalLinearTwoOther j)) := by
  rw [generalLinearTwoRatio, mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, mul_one]

section Overlap

/-- The ring of the overlap `D(a) ∩ D(b)`: the coordinate ring of `GL₂` with `a` inverted and
then with `b` inverted. -/
abbrev generalLinearTwoOverlapRing :=
  Localization.Away (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0)
    (generalLinearTwoCoordinate k 0 1))

/-- The structure map of the overlap over the coordinate ring of `GL₂`. -/
noncomputable abbrev generalLinearTwoToOverlap :
    generalLinearTwoCoordinateRing k →+* generalLinearTwoOverlapRing k :=
  (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)).comp
    (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0))

/-- The structure map of the overlap is the composite of the two localization maps. -/
@[simp]
lemma generalLinearTwoToOverlap_apply (x : generalLinearTwoCoordinateRing k) :
    generalLinearTwoToOverlap k x =
      algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)
        (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0) x) :=
  rfl

/-- The entry `b` is invertible in the ring of the overlap, by construction. -/
lemma isUnit_overlap_b :
    IsUnit (generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 1)) :=
  IsLocalization.Away.algebraMap_isUnit
    (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0)
      (generalLinearTwoCoordinate k 0 1))

/-- The entry `a` is invertible in the ring of the overlap, being already invertible on `D(a)`. -/
lemma isUnit_overlap_a :
    IsUnit (generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 0)) := by
  rw [generalLinearTwoToOverlap_apply]
  exact (IsLocalization.Away.algebraMap_isUnit (S := generalLinearTwoAway k 0)
    (generalLinearTwoCoordinate k 0 0)).map _

/-- The ratio `b / a` is invertible in the ring of the overlap, where both entries are. -/
lemma isUnit_overlap_ratio :
    IsUnit (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)
      (generalLinearTwoRatio k 0)) := by
  rw [generalLinearTwoRatio, map_mul]
  refine (isUnit_overlap_b k).mul (IsUnit.map _ ?_)
  exact IsUnit.of_mul_eq_one _
    (by rw [mul_comm]; exact IsLocalization.Away.mul_invSelf _)

/-- The ratio `b / a` as a unit of the ring of the overlap. -/
noncomputable def generalLinearTwoOverlapUnit : (generalLinearTwoOverlapRing k)ˣ :=
  (isUnit_overlap_ratio k).unit

/-- The underlying element of the unit `b / a` of the overlap is the image of the ratio on
`D(a)`. -/
@[simp]
lemma coe_generalLinearTwoOverlapUnit :
    (generalLinearTwoOverlapUnit k : generalLinearTwoOverlapRing k) =
      algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)
        (generalLinearTwoRatio k 0) :=
  (isUnit_overlap_ratio k).unit_spec

/-- The structure map exhibiting the ring of the overlap as a localization of the ring of `D(b)`:
both `a` and `b` are inverted there, so inverting `b` factors through it. -/
noncomputable def generalLinearTwoOverlapFromB :
    generalLinearTwoAway k 1 →+* generalLinearTwoOverlapRing k :=
  IsLocalization.Away.lift (generalLinearTwoCoordinate k 0 1)
    (g := generalLinearTwoToOverlap k) (isUnit_overlap_b k)

/-- The map from the ring of `D(b)` to the ring of the overlap is compatible with the structure
maps from the coordinate ring of `GL₂`. -/
@[simp]
lemma generalLinearTwoOverlapFromB_algebraMap (x : generalLinearTwoCoordinateRing k) :
    generalLinearTwoOverlapFromB k
        (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 1) x) =
      generalLinearTwoToOverlap k x :=
  IsLocalization.Away.lift_eq _ (isUnit_overlap_b k) x

/-- The map from the ring of `D(b)` to the ring of the overlap commutes with the structure maps
from `k`. -/
@[simp]
lemma generalLinearTwoOverlapFromB_algebraMap_base (r : k) :
    generalLinearTwoOverlapFromB k (algebraMap k (generalLinearTwoAway k 1) r) =
      algebraMap k (generalLinearTwoOverlapRing k) r := by
  rw [IsScalarTower.algebraMap_apply k (generalLinearTwoCoordinateRing k)
      (generalLinearTwoAway k 1), generalLinearTwoOverlapFromB_algebraMap,
    generalLinearTwoToOverlap_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- The overlap really is the fibre product of the two members of the cover: inverting `b` on
`D(a)` is the same as inverting `a` on `D(b)`. -/
lemma isPushout_generalLinearTwoOverlap :
    IsPushout
      (CommRingCat.ofHom
        (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0)))
      (CommRingCat.ofHom
        (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 1)))
      (CommRingCat.ofHom
        (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)))
      (CommRingCat.ofHom (generalLinearTwoOverlapFromB k)) := by
  have : IsLocalization ((Submonoid.powers (generalLinearTwoCoordinate k 0 1)).map
      (algebraMap (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k 0)))
      (generalLinearTwoOverlapRing k) := by
    rw [Submonoid.map_powers]
    infer_instance
  exact CommRingCat.isPushout_of_isLocalization _ _
    (IsLocalization.Away.lift_comp _ (isUnit_overlap_b k))
    (Submonoid.powers (generalLinearTwoCoordinate k 0 1))

/-- The categorical fibre product of the two members of the cover is the spectrum of the ring of
the overlap. -/
lemma isPullback_generalLinearTwoOverlap :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k))))
      (Spec.map (CommRingCat.ofHom (generalLinearTwoOverlapFromB k)))
      (generalLinearTwoFirstRowOpen k 0) (generalLinearTwoFirstRowOpen k 1) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_generalLinearTwoOverlap k)

/-- On the overlap the ratio `a / b` of the second chart is inverse to the ratio `b / a` of the
first. -/
lemma generalLinearTwoOverlapFromB_ratio :
    generalLinearTwoOverlapFromB k (generalLinearTwoRatio k 1) =
      ((generalLinearTwoOverlapUnit k)⁻¹ : (generalLinearTwoOverlapRing k)ˣ) := by
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  refine (isUnit_overlap_b k).mul_left_cancel ?_
  have h1 := congrArg (generalLinearTwoOverlapFromB k) (generalLinearTwoRatio_mul_coordinate k 1)
  rw [map_mul, generalLinearTwoOverlapFromB_algebraMap, generalLinearTwoOther_one,
    generalLinearTwoOverlapFromB_algebraMap] at h1
  have h0 : (generalLinearTwoOverlapUnit k : generalLinearTwoOverlapRing k) *
      generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 0) =
      generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 1) := by
    rw [coe_generalLinearTwoOverlapUnit, generalLinearTwoToOverlap_apply,
      generalLinearTwoToOverlap_apply, ← map_mul, generalLinearTwoRatio_mul_coordinate,
      generalLinearTwoOther_zero]
  calc generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 1) *
        ((generalLinearTwoOverlapUnit k : generalLinearTwoOverlapRing k) *
          generalLinearTwoOverlapFromB k (generalLinearTwoRatio k 1))
      = (generalLinearTwoOverlapUnit k : generalLinearTwoOverlapRing k) *
          (generalLinearTwoOverlapFromB k (generalLinearTwoRatio k 1) *
            generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 1)) := by ring
    _ = generalLinearTwoToOverlap k (generalLinearTwoCoordinate k 0 1) * 1 := by
        rw [h1, h0, mul_one]
    _ = _ := by rw [mul_one]

/-- The morphism from the overlap to `Spec k[T, T⁻¹]` sending `T` to `b/a`. Both chart
coordinates of `ℙ¹` pull back through it, one to `T` and one to `T⁻¹`. -/
noncomputable def generalLinearTwoOverlapLaurent :
    LaurentPolynomial k →+* generalLinearTwoOverlapRing k :=
  LaurentPolynomial.eval₂ (algebraMap k (generalLinearTwoOverlapRing k))
    (generalLinearTwoOverlapUnit k)

/-- The coordinate of the first chart of `ℙ¹` pulls back to `b/a` on the overlap. -/
lemma generalLinearTwoOverlapLaurent_comp_toLaurent :
    (generalLinearTwoOverlapLaurent k).comp (Polynomial.toLaurent (R := k)) =
      (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k)).comp
        (Polynomial.aeval (generalLinearTwoRatio k 0)).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [generalLinearTwoOverlapLaurent, ← IsScalarTower.algebraMap_apply]
  · simp [generalLinearTwoOverlapLaurent]

/-- The coordinate of the second chart of `ℙ¹` pulls back to `a/b` on the overlap: it is the
inverse of the first chart's coordinate. -/
lemma generalLinearTwoOverlapLaurent_comp_overlapInverse :
    (generalLinearTwoOverlapLaurent k).comp
        (projectiveLineOverlapInverseCoordinate k).toRingHom =
      (generalLinearTwoOverlapFromB k).comp
        (Polynomial.aeval (generalLinearTwoRatio k 1)).toRingHom := by
  refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
  · simp [generalLinearTwoOverlapLaurent, projectiveLineOverlapInverseCoordinate]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      projectiveLineOverlapInverseCoordinate, Polynomial.aeval_X, generalLinearTwoOverlapLaurent,
      LaurentPolynomial.eval₂_T, generalLinearTwoOverlapFromB_ratio, zpow_neg, zpow_one]

/-- On the overlap the two chart descriptions of `[a : b]` agree: both are obtained from the
morphism `T ↦ b/a` into `Spec k[T, T⁻¹]` followed by one of the two sides of the pullback square
that glues `ℙ¹`. -/
lemma generalLinearTwoChartToProjectiveLine_agree :
    Spec.map (CommRingCat.ofHom
        (algebraMap (generalLinearTwoAway k 0) (generalLinearTwoOverlapRing k))) ≫
        generalLinearTwoChartToProjectiveLine k 0 =
      Spec.map (CommRingCat.ofHom (generalLinearTwoOverlapFromB k)) ≫
        generalLinearTwoChartToProjectiveLine k 1 := by
  have hA := congrArg CommRingCat.ofHom (generalLinearTwoOverlapLaurent_comp_toLaurent k)
  have hB := congrArg CommRingCat.ofHom (generalLinearTwoOverlapLaurent_comp_overlapInverse k)
  simp only [CommRingCat.ofHom_comp] at hA hB
  rw [generalLinearTwoChartToProjectiveLine, generalLinearTwoChartToProjectiveLine,
    generalLinearTwoProjectiveChart_zero, generalLinearTwoProjectiveChart_one,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← hA, ← hB, Spec.map_comp_assoc,
    Spec.map_comp_assoc]
  exact congrArg _ (isPullback_projectiveLineCharts k).w

/-- The two chart descriptions are compatible on every fibre product of two members of the
cover, which is what lets them be glued. -/
lemma generalLinearTwoChartToProjectiveLine_compat (x y : Fin 2) :
    pullback.fst (generalLinearTwoFirstRowOpen k x) (generalLinearTwoFirstRowOpen k y) ≫
        generalLinearTwoChartToProjectiveLine k x =
      pullback.snd (generalLinearTwoFirstRowOpen k x) (generalLinearTwoFirstRowOpen k y) ≫
        generalLinearTwoChartToProjectiveLine k y := by
  have hdiag : ∀ j : Fin 2, pullback.fst (generalLinearTwoFirstRowOpen k j)
      (generalLinearTwoFirstRowOpen k j) ≫ generalLinearTwoChartToProjectiveLine k j =
      pullback.snd (generalLinearTwoFirstRowOpen k j)
          (generalLinearTwoFirstRowOpen k j) ≫
        generalLinearTwoChartToProjectiveLine k j := fun j ↦ by
    rw [fst_eq_snd_of_mono_eq]
  have hpb := isPullback_generalLinearTwoOverlap k
  fin_cases x <;> fin_cases y
  · exact hdiag 0
  · rw [← cancel_epi hpb.isoPullback.hom, hpb.isoPullback_hom_fst_assoc,
      hpb.isoPullback_hom_snd_assoc]
    exact generalLinearTwoChartToProjectiveLine_agree k
  · rw [← cancel_epi hpb.flip.isoPullback.hom, hpb.flip.isoPullback_hom_fst_assoc,
      hpb.flip.isoPullback_hom_snd_assoc]
    exact (generalLinearTwoChartToProjectiveLine_agree k).symm
  · exact hdiag 1

end Overlap

/-- **Stacks Project, Tag 01KX (gl2_to_projective_line).** The morphism `[a : b]` from `GL₂` to
the projective line, glued from `b/a` on `D(a)` and `a/b` on `D(b)`. -/
@[stacks 01KX "gl2_to_projective_line"]
noncomputable def generalLinearTwoToProjectiveLine :
    generalLinearTwoScheme k ⟶ projectiveLine k :=
  (generalLinearTwoFirstRowCover k).glueMorphisms (generalLinearTwoChartToProjectiveLine k)
    (generalLinearTwoChartToProjectiveLine_compat k)

/-- The restriction of `[a : b]` to the standard open of the `(0, j)` entry is the chart
description `generalLinearTwoChartToProjectiveLine`. -/
@[simp]
lemma generalLinearTwoFirstRowOpen_comp_toProjectiveLine (j : Fin 2) :
    generalLinearTwoFirstRowOpen k j ≫ generalLinearTwoToProjectiveLine k =
      generalLinearTwoChartToProjectiveLine k j :=
  (generalLinearTwoFirstRowCover k).ι_glueMorphisms _ _ j

/-- The ring map induced by a matrix is a `k`-algebra map: it sends scalars of `k` to their
images in `A`. -/
@[simp]
lemma generalLinearTwoHom_algebraMap {A : Type u} [CommRing A] [Algebra k A]
    (M : Matrix (Fin 2) (Fin 2) A) (hM : IsUnit M.det) (r : k) :
    generalLinearTwoHom k M hM (algebraMap k (generalLinearTwoCoordinateRing k) r) =
      algebraMap k A r := by
  rw [IsScalarTower.algebraMap_apply k (MvPolynomial (Fin 2 × Fin 2) k),
    generalLinearTwoHom, IsLocalization.Away.lift_eq]
  simp

/-- A matrix over `k[X]` of unit determinant whose first row is `(1, X)` in the order given by
`j` splits `[a : b]` over the `j`-th chart of `ℙ¹`: the chart is in the image. -/
lemma range_generalLinearTwoProjectiveChart_subset (j : Fin 2)
    (M : Matrix (Fin 2) (Fin 2) (Polynomial k)) (hM : IsUnit M.det)
    (hone : M 0 j = 1) (hX : M 0 (generalLinearTwoOther j) = Polynomial.X) :
    Set.range (generalLinearTwoProjectiveChart k j).base ⊆
      Set.range (generalLinearTwoToProjectiveLine k).base := by
  have hunit : IsUnit (generalLinearTwoHom k M hM (generalLinearTwoCoordinate k 0 j)) := by
    rw [generalLinearTwoHom_coordinate, hone]
    exact isUnit_one
  set τ := IsLocalization.Away.lift (S := generalLinearTwoAway k j)
    (generalLinearTwoCoordinate k 0 j) (g := generalLinearTwoHom k M hM) hunit with hτ
  have hτalg : ∀ x, τ (algebraMap (generalLinearTwoCoordinateRing k)
      (generalLinearTwoAway k j) x) = generalLinearTwoHom k M hM x :=
    fun x ↦ IsLocalization.Away.lift_eq _ hunit x
  have hratio : τ (generalLinearTwoRatio k j) = Polynomial.X := by
    have h := congrArg τ (generalLinearTwoRatio_mul_coordinate k j)
    rw [map_mul, hτalg, hτalg, generalLinearTwoHom_coordinate,
      generalLinearTwoHom_coordinate, hone, hX, mul_one] at h
    exact h
  have hid : τ.comp (Polynomial.aeval (generalLinearTwoRatio k j)).toRingHom =
      RingHom.id (Polynomial k) := by
    refine Polynomial.ringHom_ext (fun r ↦ ?_) ?_
    · change τ (Polynomial.aeval (generalLinearTwoRatio k j) (Polynomial.C r)) = _
      rw [Polynomial.aeval_C, IsScalarTower.algebraMap_apply k
          (generalLinearTwoCoordinateRing k) (generalLinearTwoAway k j), hτalg,
        generalLinearTwoHom_algebraMap]
      simp
    · change τ (Polynomial.aeval (generalLinearTwoRatio k j) Polynomial.X) = _
      rw [Polynomial.aeval_X, hratio]
      simp
  have hfac : (Spec.map (CommRingCat.ofHom τ) ≫ generalLinearTwoFirstRowOpen k j) ≫
      generalLinearTwoToProjectiveLine k = generalLinearTwoProjectiveChart k j := by
    rw [Category.assoc, generalLinearTwoFirstRowOpen_comp_toProjectiveLine,
      generalLinearTwoChartToProjectiveLine, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      hid, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  rw [← hfac]
  rintro _ ⟨z, rfl⟩
  exact ⟨_, rfl⟩

/-- **Stacks Project, Tag 01KX (gl2_to_projective_line_surjective).** The morphism `[a : b]` from
`GL₂` to the projective line is surjective: over the first chart the matrix `!![1, X; 0, 1]` is a
section, and over the second the matrix `!![X, 1; -1, 0]`. -/
@[stacks 01KX "gl2_to_projective_line_surjective"]
instance surjective_generalLinearTwoToProjectiveLine (k : Type u) [Field k] :
    Surjective (generalLinearTwoToProjectiveLine k) := by
  have hX : Set.range (projectiveLineXChart k).base ⊆
      Set.range (generalLinearTwoToProjectiveLine k).base := by
    have := range_generalLinearTwoProjectiveChart_subset k 0
      !![1, Polynomial.X; 0, 1] (by rw [Matrix.det_fin_two]; simp)
      (by simp) (by simp)
    rwa [generalLinearTwoProjectiveChart_zero] at this
  have hY : Set.range (projectiveLineYChart k).base ⊆
      Set.range (generalLinearTwoToProjectiveLine k).base := by
    have := range_generalLinearTwoProjectiveChart_subset k 1
      !![Polynomial.X, 1; -1, 0] (by rw [Matrix.det_fin_two]; simp)
      (by simp) (by simp)
    rwa [generalLinearTwoProjectiveChart_one] at this
  constructor
  intro x
  rcases mem_range_projectiveLineXChart_or_eq_infinity x with h | h
  · exact hX h
  · exact hY (h ▸ ⟨affineLineOrigin k, rfl⟩)

end AlgebraicGeometry

end
