module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.RingHom.Locally
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothAlgebra
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.CubicSurface.Flat
public import StacksFrontier.Examples.Spaces.CurveFamilyNotScheme.FermatCurveProperties

/-!
# Smoothness of the cubic surface

Let `k` be a field of characteristic different from three. This file proves that the surface
`Y : T₀³ + T₁³ + T₂³ - t T₀T₁T₂ = 0` of Stacks 0D5E is smooth of relative dimension two over `k`,
hence regular of dimension two, and that `Y ⟶ A¹_k` is smooth of relative dimension one in a
neighbourhood of every point of `Y` lying over a point where `t³ ≠ 27`, in particular at every
point of the fibre over the origin `t = 0`.

Everything is computed on the standard chart `k[t][x, y]/(f)`, `f = 1 + x³ + y³ - t x y`, which is
the same for the three coordinates. Over `k`, with `t` as a third variable, the three partial
derivatives `∂f/∂t = -xy`, `∂f/∂x = 3x² - ty`, `∂f/∂y = 3y² - tx` generate the unit ideal modulo
`f` by Euler's formula, `3 = 3f - t ∂f/∂t - x ∂f/∂x - y ∂f/∂y`. Over `k[t]` only `∂f/∂x` and
`∂f/∂y` count, and they generate an ideal containing `3 (27 - t³)` modulo `f`:

```
  3 (27 - t³) = (27 - t³ + 9 t x y) (3 f - x ∂f/∂x - y ∂f/∂y) + t² (3 x² ∂f/∂y + t x ∂f/∂x).
```

The Jacobian criterion is used in the form of an explicit submersive presentation of
`R[x₀, …, xₘ]/(f)` localized at a multiple of one partial derivative.

## Main results

* `Stacks.Examples.CurveFamilyNotScheme.isStandardSmoothOfRelativeDimension_hypersurfaceAway`:
  the Jacobian criterion for a hypersurface `R[x₀, …, xₘ]/(f)` localized at a multiple of
  `∂f/∂xᵢ`.
* `Stacks.Examples.CurveFamilyNotScheme.smoothOfRelativeDimension_cubicSurfaceToSpec`: `Y` is
  smooth of relative dimension two over `k`.
* `Stacks.Examples.CurveFamilyNotScheme.isRegular_cubicSurface`: `Y` is a regular scheme, and
  `Stacks.Examples.CurveFamilyNotScheme.topologicalKrullDimAt_cubicSurface`,
  `Stacks.Examples.CurveFamilyNotScheme.topologicalKrullDim_cubicSurface`,
  `Stacks.Examples.CurveFamilyNotScheme.ringKrullDim_stalk_cubicSurface`: it has dimension two at
  every point, and its local rings at closed points have dimension two.
* `Stacks.Examples.CurveFamilyNotScheme.exists_smoothOfRelativeDimension_cubicSurfaceToLine`:
  `Y ⟶ A¹_k` is smooth of relative dimension one near every point over `t³ ≠ 27`, and
  `Stacks.Examples.CurveFamilyNotScheme.exists_smoothOfRelativeDimension_of_mem_originFibre`
  near every point of the fibre over the origin.

## References

* [Stacks Project, Tag 0D5E](https://stacks.math.columbia.edu/tag/0D5E)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace Stacks.Examples.CurveFamilyNotScheme

/-! ### The Jacobian criterion for a hypersurface -/

section Hypersurface

variable {R : Type u} [CommRing R] {m : ℕ} (f : MvPolynomial (Fin (m + 1)) R) (i : Fin (m + 1))

/-- The presentation of `R[x₀, …, xₘ]/(f)` by its variables and the single relation `f`, with
the relation matched to the variable `xᵢ`. -/
def hypersurfacePresentation :
    Algebra.PreSubmersivePresentation R (MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {f})
      (Fin (m + 1)) (Fin 1) :=
  (Algebra.PreSubmersivePresentation.naive (v := fun _ : Fin 1 => f) (fun _ => i)
    (Function.injective_of_subsingleton _)).ofAlgEquiv
    (Ideal.quotientEquivAlgOfEq R (by rw [Set.range_const]))

/-- The Jacobian of `hypersurfacePresentation f i` is the class of `∂f/∂xᵢ`. -/
theorem hypersurfacePresentation_jacobian :
    (hypersurfacePresentation f i).jacobian = Ideal.Quotient.mk _ (pderiv i f) := by
  rw [hypersurfacePresentation, Algebra.PreSubmersivePresentation.jacobian_ofAlgEquiv,
    Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  rfl

variable {f i} {u : MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {f}}
  (T : Type*) [CommRing T] [Algebra (MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {f}) T]
  [Algebra R T] [IsScalarTower R (MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {f}) T]
  [IsLocalization.Away u T]

/-- The submersive presentation of `(R[x₀, …, xₘ]/(f))[1/u]` over `R`, for `u` a multiple of
`∂f/∂xᵢ`: the presentation `hypersurfacePresentation f i` followed by that of the
localization. -/
def hypersurfaceAwayPresentation
    (hu : Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f) ∣ u) :
    Algebra.SubmersivePresentation R T (Unit ⊕ Fin (m + 1)) (Unit ⊕ Fin 1) where
  __ := (Algebra.PreSubmersivePresentation.localizationAway T u).comp
    (hypersurfacePresentation f i)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian,
      hypersurfacePresentation_jacobian, Algebra.smul_def]
    have h₁ : IsUnit (algebraMap _ T u) := IsLocalization.Away.algebraMap_isUnit u
    have h₂ : IsUnit (algebraMap _ T (Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f))) :=
      isUnit_of_dvd_unit (map_dvd _ hu) h₁
    exact h₂.mul h₁

/-- The presentation `hypersurfaceAwayPresentation T hu` has dimension `m`. -/
theorem hypersurfaceAwayPresentation_dimension
    (hu : Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f) ∣ u) :
    (hypersurfaceAwayPresentation T hu).dimension = m := by
  simp [Algebra.Presentation.dimension]
  omega

/-- **The Jacobian criterion for a hypersurface.** The localization of `R[x₀, …, xₘ]/(f)` at a
multiple of `∂f/∂xᵢ` is standard smooth of relative dimension `m` over `R`. -/
theorem isStandardSmoothOfRelativeDimension_hypersurfaceAway
    (hu : Ideal.Quotient.mk (Ideal.span {f}) (pderiv i f) ∣ u) :
    Algebra.IsStandardSmoothOfRelativeDimension m R T :=
  (hypersurfaceAwayPresentation T hu).isStandardSmoothOfRelativeDimension
    (hypersurfaceAwayPresentation_dimension T hu)

/-- **A hypersurface whose partial derivatives generate the unit ideal is locally standard smooth
of relative dimension `m`.** -/
theorem locally_isStandardSmoothOfRelativeDimension_hypersurface
    (h : Ideal.span (Set.range fun j => Ideal.Quotient.mk (Ideal.span {f}) (pderiv j f)) = ⊤) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension m)
      (algebraMap R (MvPolynomial (Fin (m + 1)) R ⧸ Ideal.span {f})) := by
  refine ⟨_, h, fun t ht => ?_⟩
  obtain ⟨j, rfl⟩ := ht
  rw [← IsScalarTower.algebraMap_eq]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := m)).mpr
    (isStandardSmoothOfRelativeDimension_hypersurfaceAway _ (f := f) (i := j) dvd_rfl)

end Hypersurface

variable (k : Type u) [Field k]

/-! ### The chart over `k` -/

/-- The equation `1 + x³ + y³ - t x y` of the chart with `t` as a third variable: `X 0 = t`,
`X 1 = x`, `X 2 = y`. -/
def cubicChartEquation₃ : MvPolynomial (Fin 3) k :=
  1 + X 1 ^ 3 + X 2 ^ 3 - X 0 * X 1 * X 2

/-- The identification `k[t, x, y] ≃ k[t][x, y]`, `X 0 ↦ t`, `X 1 ↦ x`, `X 2 ↦ y`. -/
def chartVariablesEquiv : MvPolynomial (Fin 3) k ≃ₐ[k] MvPolynomial (Fin 2) (Polynomial k) :=
  (finSuccEquiv k 2).trans (polynomialCoeffEquiv k (Fin 2)).symm

/-- The identification `k[t, x, y] ≃ k[t][x, y]` sends `X 0` to `t`. -/
theorem chartVariablesEquiv_X_zero :
    chartVariablesEquiv k (X 0) = C Polynomial.X := by
  rw [chartVariablesEquiv, AlgEquiv.trans_apply, finSuccEquiv_X_zero, AlgEquiv.symm_apply_eq,
    polynomialCoeffEquiv_C_X]

/-- The identification `k[t, x, y] ≃ k[t][x, y]` sends `X (j + 1)` to `X j`. -/
theorem chartVariablesEquiv_X_succ (j : Fin 2) :
    chartVariablesEquiv k (X j.succ) = X j := by
  rw [chartVariablesEquiv, AlgEquiv.trans_apply, finSuccEquiv_X_succ, AlgEquiv.symm_apply_eq,
    polynomialCoeffEquiv_X]

/-- The identification `k[t, x, y] ≃ k[t][x, y]` sends `X 1` to `x`. -/
theorem chartVariablesEquiv_X_one : chartVariablesEquiv k (X 1) = X 0 :=
  chartVariablesEquiv_X_succ k 0

/-- The identification `k[t, x, y] ≃ k[t][x, y]` sends `X 2` to `y`. -/
theorem chartVariablesEquiv_X_two : chartVariablesEquiv k (X 2) = X 1 :=
  chartVariablesEquiv_X_succ k 1

/-- The identification `k[t, x, y] ≃ k[t][x, y]` carries the equation of the chart to itself. -/
theorem chartVariablesEquiv_cubicChartEquation₃ :
    chartVariablesEquiv k (cubicChartEquation₃ k) = cubicChartEquation k := by
  rw [cubicChartEquation₃]
  simp only [map_add, map_sub, map_mul, map_pow, map_one]
  rw [chartVariablesEquiv_X_zero, chartVariablesEquiv_X_one, chartVariablesEquiv_X_two,
    cubicChartEquation]
  ring

/-- **The chart ring as a `k`-algebra**: `k[t, x, y]/(1 + x³ + y³ - t x y)`. -/
def chartAlgEquiv :
    (MvPolynomial (Fin 3) k ⧸ Ideal.span {cubicChartEquation₃ k}) ≃ₐ[k] CubicChartRing k :=
  Ideal.quotientEquivAlg (I := Ideal.span {cubicChartEquation₃ k})
    (J := Ideal.span {cubicChartEquation k}) (chartVariablesEquiv k) <| by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p => Ideal.span {p}) (chartVariablesEquiv_cubicChartEquation₃ k).symm

/-- **Euler's formula on the chart over `k`**: `3 = -(t ∂f/∂t + x ∂f/∂x + y ∂f/∂y)` modulo `f`. -/
theorem three_eq_euler_cubicChartEquation₃ :
    (3 : MvPolynomial (Fin 3) k ⧸ Ideal.span {cubicChartEquation₃ k}) =
      -∑ j : Fin 3, Ideal.Quotient.mk _ (X j) *
        Ideal.Quotient.mk _ (pderiv j (cubicChartEquation₃ k)) := by
  simp only [← map_mul, ← map_sum, ← map_neg, ← map_ofNat (Ideal.Quotient.mk _) 3]
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨3, ?_⟩
  simp [Fin.sum_univ_three, cubicChartEquation₃, Derivation.leibniz, Derivation.leibniz_pow,
    pderiv_X, Pi.single_apply]
  ring

/-- Over a field of characteristic different from three, the partial derivatives of the chart
equation over `k` generate the unit ideal modulo the equation. -/
theorem span_pderiv_cubicChartEquation₃ (hk : ringChar k ≠ 3) :
    Ideal.span (Set.range fun j => Ideal.Quotient.mk (Ideal.span {cubicChartEquation₃ k})
      (pderiv j (cubicChartEquation₃ k))) = ⊤ := by
  have h3 : IsUnit (3 : MvPolynomial (Fin 3) k ⧸ Ideal.span {cubicChartEquation₃ k}) := by
    have e : (3 : MvPolynomial (Fin 3) k ⧸ Ideal.span {cubicChartEquation₃ k}) =
        algebraMap k _ 3 := (map_ofNat _ 3).symm
    rw [e]
    exact (isUnit_iff_ne_zero.mpr (three_ne_zero_of_ringChar_ne_three hk)).map _
  refine Ideal.eq_top_of_isUnit_mem _ ?_ h3
  rw [three_eq_euler_cubicChartEquation₃]
  exact neg_mem (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩))

/-- **The chart is smooth of relative dimension two over `k`.** -/
theorem locally_isStandardSmoothOfRelativeDimension_cubicChartRing (hk : ringChar k ≠ 3) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2)
      (algebraMap k (CubicChartRing k)) := by
  have h := locally_isStandardSmoothOfRelativeDimension_hypersurface
    (span_pderiv_cubicChartEquation₃ k hk)
  have e : algebraMap k (CubicChartRing k) =
      (chartAlgEquiv k).toRingEquiv.toRingHom.comp
        (algebraMap k (MvPolynomial (Fin 3) k ⧸ Ideal.span {cubicChartEquation₃ k})) :=
    RingHom.ext fun a => ((chartAlgEquiv k).commutes a).symm
  rw [e]
  exact (RingHom.locally_respectsIso
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso).1 _ _ h

/-! ### The cubic surface over `k` -/

/-- The structure morphism `Y ⟶ Spec k`, through the affine line. -/
abbrev cubicSurfaceToSpec : cubicSurface k ⟶ Spec (CommRingCat.of k) :=
  cubicSurfaceToLine k ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k)))

/-- Each chart, followed by the structure morphism to `Spec k`. -/
theorem cubicChart_comp_cubicSurfaceToSpec (j : Fin 3) :
    cubicChart k j ≫ cubicSurfaceToSpec k =
      Spec.map (CommRingCat.ofHom (algebraMap k (CubicChartRing k))) := by
  rw [cubicSurfaceToSpec, cubicChart_comp_cubicSurfaceToLine_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- A property of morphisms local on the source holds for a morphism out of `Y` as soon as it
holds on each standard chart. -/
theorem of_cubicChart {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P]
    {Z : Scheme.{u}} (g : cubicSurface k ⟶ Z) (h : ∀ j, P (cubicChart k j ≫ g)) : P g := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ (iSup_opensRange_cubicChart k) fun j => ?_
  rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr (h j)

/-- **The cubic surface is smooth of relative dimension two over `k`** when the characteristic
of `k` is not three. -/
theorem smoothOfRelativeDimension_cubicSurfaceToSpec (hk : ringChar k ≠ 3) :
    SmoothOfRelativeDimension 2 (cubicSurfaceToSpec k) := by
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension 2)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 2))
  refine of_cubicChart k (P := @SmoothOfRelativeDimension 2) _ fun j => ?_
  rw [cubicChart_comp_cubicSurfaceToSpec]
  exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 2)).mpr
    (locally_isStandardSmoothOfRelativeDimension_cubicChartRing k hk)

/-- The chart ring is a smooth `k`-algebra. -/
theorem smooth_cubicChartRing (hk : ringChar k ≠ 3) : Algebra.Smooth k (CubicChartRing k) := by
  have : SmoothOfRelativeDimension 2
      (Spec.map (CommRingCat.ofHom (algebraMap k (CubicChartRing k)))) :=
    HasRingHomProperty.Spec_iff.mpr
      (locally_isStandardSmoothOfRelativeDimension_cubicChartRing k hk)
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k (CubicChartRing k)))) :=
    SmoothOfRelativeDimension.smooth 2 _
  have h := HasRingHomProperty.Spec_iff (P := @Smooth) |>.mp this
  exact RingHom.smooth_algebraMap.mp h

/-- **The cubic surface is regular.** Each chart ring is smooth over `k`, hence regular. -/
theorem isRegular_cubicSurface (hk : ringChar k ≠ 3) : IsRegular (cubicSurface k) := by
  intro y
  have hy : y ∈ ⨆ j : Fin 3, (cubicChart k j).opensRange := by
    rw [iSup_opensRange_cubicChart]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  refine ⟨⟨(cubicChart k j) ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩, ?_, ?_⟩
  · change y ∈ (cubicChart k j) ''ᵁ ⊤
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact hj
  · have := smooth_cubicChartRing k hk
    have : IsRegularRing (CubicChartRing k) :=
      Stacks.RingTheory.SmoothDescent.isRegularRing_of_smooth k _
    exact IsRegularRing.of_ringEquiv
      (((cubicChart k j).appIso ⊤).trans (Scheme.ΓSpecIso _)).commRingCatIsoToRingEquiv.symm

/-- The local rings of the cubic surface are regular local rings. -/
theorem isRegularLocalRing_stalk_cubicSurface (hk : ringChar k ≠ 3) (y : cubicSurface k) :
    IsRegularLocalRing ((cubicSurface k).presheaf.stalk y) :=
  (isRegular_cubicSurface k hk).isRegularLocalRing_stalk y

/-- **The cubic surface has dimension two at every point.** -/
theorem topologicalKrullDimAt_cubicSurface (hk : ringChar k ≠ 3) (y : cubicSurface k) :
    topologicalKrullDimAt (cubicSurface k) y = 2 := by
  have := smoothOfRelativeDimension_cubicSurfaceToSpec k hk
  set f := cubicSurfaceToSpec k
  have hpre : f ⁻¹' {f y} = Set.univ := Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _
  have hdim := topologicalKrullDimAt_eq_of_homeomorph
    ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ (cubicSurface k))) ⟨y, rfl⟩
  have hfib := localKrullDim_fiber_eq_of_smoothOfRelativeDimension 2 f (f y) (f.asFiber y)
  rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim] at hfib
  have hpoint : (f.fiberHomeo (f y)) (f.asFiber y) = ⟨y, rfl⟩ := by
    apply Subtype.ext
    simp [Scheme.Hom.asFiber]
  have hh := topologicalKrullDimAt_eq_of_homeomorph (f.fiberHomeo (f y)) (f.asFiber y)
  rw [hpoint] at hh
  have hy : ((Homeomorph.setCongr hpre).trans (Homeomorph.Set.univ (cubicSurface k)))
      ⟨y, rfl⟩ = y := rfl
  rw [hy] at hdim
  rw [← hdim, ← hh, hfib]
  rfl

/-- **The cubic surface has dimension two.** -/
theorem topologicalKrullDim_cubicSurface (hk : ringChar k ≠ 3) :
    topologicalKrullDim (cubicSurface k) = 2 := by
  have h (y : cubicSurface k) : TopologicalSpace.localKrullDim (cubicSurface k) y = 2 := by
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
    exact topologicalKrullDimAt_cubicSurface k hk y
  rw [TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
  exact (iSup_congr h).trans iSup_const

/-- **The local ring of the cubic surface at a closed point has dimension two.** -/
theorem ringKrullDim_stalk_cubicSurface (hk : ringChar k ≠ 3) (y : cubicSurface k)
    (hy : IsClosed ({y} : Set (cubicSurface k))) :
    ringKrullDim ((cubicSurface k).presheaf.stalk y) = 2 := by
  have := smoothOfRelativeDimension_cubicSurfaceToSpec k hk
  have := SmoothOfRelativeDimension.smooth 2 (cubicSurfaceToSpec k)
  rw [← topologicalKrullDimAt_eq_ringKrullDim_stalk_of_closed_point (cubicSurfaceToSpec k) y hy,
    topologicalKrullDimAt_cubicSurface k hk]

/-! ### Smoothness over the affine line away from `t³ = 27` -/

/-- **The Jacobian ideal of the chart over `k[t]` contains `3 (27 - t³)`.** -/
theorem algebraMap_mul_eq_jacobian :
    algebraMap (Polynomial k) (CubicChartRing k) (3 * (27 - Polynomial.X ^ 3)) =
      Ideal.Quotient.mk _ (-(27 - C (Polynomial.X ^ 3) + 9 * C Polynomial.X * X 0 * X 1) * X 0 +
          C (Polynomial.X ^ 3) * X 0) *
        Ideal.Quotient.mk _ (pderiv 0 (cubicChartEquation k)) +
      Ideal.Quotient.mk _ (-(27 - C (Polynomial.X ^ 3) + 9 * C Polynomial.X * X 0 * X 1) * X 1 +
          3 * C (Polynomial.X ^ 2) * X 0 ^ 2) *
        Ideal.Quotient.mk _ (pderiv 1 (cubicChartEquation k)) := by
  rw [← Ideal.Quotient.mk_algebraMap, ← map_mul, ← map_mul, ← map_add, Ideal.Quotient.eq,
    Ideal.mem_span_singleton]
  refine ⟨3 * (27 - C (Polynomial.X ^ 3) + 9 * C Polynomial.X * X 0 * X 1), ?_⟩
  simp [MvPolynomial.algebraMap_eq, cubicChartEquation, Derivation.leibniz,
    Derivation.leibniz_pow, pderiv_X, map_ofNat]
  ring

/-- If `t³ ≠ 27` at a point of the chart, one of the two partial derivatives `∂f/∂x`, `∂f/∂y`
does not vanish there. -/
theorem exists_pderiv_notMem (hk : ringChar k ≠ 3) (p : Ideal (CubicChartRing k)) [p.IsPrime]
    (hp : algebraMap (Polynomial k) (CubicChartRing k) (Polynomial.X ^ 3 - 27) ∉ p) :
    ∃ i : Fin 2, Ideal.Quotient.mk _ (pderiv i (cubicChartEquation k)) ∉ p := by
  by_contra! h
  apply hp
  have h3 : IsUnit (algebraMap (Polynomial k) (CubicChartRing k) (-3)) := by
    have e : (3 : CubicChartRing k) = algebraMap k (CubicChartRing k) 3 := (map_ofNat _ 3).symm
    rw [map_neg, map_ofNat, IsUnit.neg_iff, e]
    exact (isUnit_iff_ne_zero.mpr (three_ne_zero_of_ringChar_ne_three hk)).map _
  have hmem : algebraMap (Polynomial k) (CubicChartRing k) (3 * (27 - Polynomial.X ^ 3)) ∈ p := by
    rw [algebraMap_mul_eq_jacobian]
    exact p.add_mem (p.mul_mem_left _ (h 0)) (p.mul_mem_left _ (h 1))
  rw [show (3 : Polynomial k) * (27 - Polynomial.X ^ 3) = (-3) * (Polynomial.X ^ 3 - 27) by ring,
    map_mul] at hmem
  exact (‹p.IsPrime›.mem_or_mem hmem).resolve_left
    (fun h' => ‹p.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ h' h3))

/-- The open immersion `Spec (k[t][x, y]/(f))[1/u] ⟶ Y` of a basic open of the chart `j`. -/
def cubicChartAway (j : Fin 3) (u : CubicChartRing k) :
    Spec (CommRingCat.of (Localization.Away u)) ⟶ cubicSurface k :=
  Spec.map (CommRingCat.ofHom (algebraMap (CubicChartRing k) (Localization.Away u))) ≫
    cubicChart k j

/-- A basic open of a chart is an open immersion into `Y`. -/
instance (j : Fin 3) (u : CubicChartRing k) : IsOpenImmersion (cubicChartAway k j u) := by
  unfold cubicChartAway
  infer_instance

/-- **`Y ⟶ A¹_k` is smooth of relative dimension one near every point over `t³ ≠ 27`.** -/
theorem exists_smoothOfRelativeDimension_cubicSurfaceToLine (hk : ringChar k ≠ 3)
    (y : cubicSurface k) (hy : Polynomial.X ^ 3 - 27 ∉ (cubicSurfaceToLine k y).asIdeal) :
    ∃ U : (cubicSurface k).Opens, y ∈ U ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ cubicSurfaceToLine k) := by
  have hy' : y ∈ ⨆ j : Fin 3, (cubicChart k j).opensRange := by
    rw [iSup_opensRange_cubicChart]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hy'
  obtain ⟨z, rfl⟩ := Scheme.Hom.mem_opensRange.mp hj
  have hz : algebraMap (Polynomial k) (CubicChartRing k) (Polynomial.X ^ 3 - 27) ∉ z.asIdeal := by
    rw [← Scheme.Hom.comp_apply, cubicChart_comp_cubicSurfaceToLine] at hy
    exact hy
  have := z.isPrime
  obtain ⟨i, hi⟩ := exists_pderiv_notMem k hk z.asIdeal hz
  set u : CubicChartRing k := Ideal.Quotient.mk _ (pderiv i (cubicChartEquation k)) *
    algebraMap (Polynomial k) (CubicChartRing k) (Polynomial.X ^ 3 - 27)
  have hu : u ∉ z.asIdeal := fun h => (z.isPrime.mem_or_mem h).elim hi hz
  refine ⟨(cubicChartAway k j u).opensRange, ?_, ?_⟩
  · have hrange := PrimeSpectrum.localization_away_comap_range (Localization.Away u) u
    obtain ⟨w, hw⟩ : z ∈ Set.range (PrimeSpectrum.comap
        (algebraMap (CubicChartRing k) (Localization.Away u))) := by
      rw [hrange]; exact hu
    refine Scheme.Hom.mem_opensRange.mpr ⟨w, ?_⟩
    rw [cubicChartAway]
    exact congrArg (cubicChart k j) hw
  · have : SmoothOfRelativeDimension 1 (cubicChartAway k j u ≫ cubicSurfaceToLine k) := by
      rw [cubicChartAway, Category.assoc, cubicChart_comp_cubicSurfaceToLine, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
      refine (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr ?_
      refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
      exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mpr
        (isStandardSmoothOfRelativeDimension_hypersurfaceAway _ (f := cubicChartEquation k)
          (i := i) (u := u) (dvd_mul_right _ _))
    rw [← Scheme.Hom.isoOpensRange_inv_comp, Category.assoc]
    exact smoothOfRelativeDimension_comp 0 1 _ _

/-- The polynomial `t³ - 27` does not vanish at the origin of the affine line, in characteristic
different from three. -/
theorem X_pow_three_sub_notMem_originPoint (hk : ringChar k ≠ 3) :
    Polynomial.X ^ 3 - 27 ∉ (originPoint k).asIdeal := by
  intro h
  change Polynomial.X ^ 3 - 27 ∈ Ideal.span {Polynomial.X} at h
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at h
  have h27 : (27 : k) = 0 := by simpa using h
  apply three_ne_zero_of_ringChar_ne_three hk
  rw [show (27 : k) = 3 ^ 3 by norm_num] at h27
  exact (pow_eq_zero_iff (by norm_num)).mp h27

/-- **`Y ⟶ A¹_k` is smooth of relative dimension one at every point of the fibre over the
origin**: every such point has an open neighbourhood on which `Y ⟶ A¹_k` is smooth of relative
dimension one. -/
theorem exists_smoothOfRelativeDimension_of_mem_originFibre (hk : ringChar k ≠ 3)
    (y : cubicSurface k) (hy : cubicSurfaceToLine k y = originPoint k) :
    ∃ U : (cubicSurface k).Opens, y ∈ U ∧
      SmoothOfRelativeDimension 1 (U.ι ≫ cubicSurfaceToLine k) :=
  exists_smoothOfRelativeDimension_cubicSurfaceToLine k hk y
    (hy ▸ X_pow_three_sub_notMem_originPoint k hk)

end Stacks.Examples.CurveFamilyNotScheme

end
