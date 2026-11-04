module

public import StacksFrontier.AlgebraicGeometry.ProjectiveLineCube.Triquadratic
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.FiniteDominant
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeFactorization
import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Sum
import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication

/-!
# Triquadratic surfaces in a product of three projective lines

Let `R` be a commutative ring and `P = Spec R × ℙ¹ × ℙ¹ × ℙ¹`. An integer array
`coef : Fin 3 → Fin 3 → Fin 3 → ℤ` defines three biquadratic forms
`A_l = ∑ coef i j l · mᵢ ⊗ mⱼ` and the triquadratic form `F = A₀ z₀² + A₁ z₀ z₁ + A₂ z₁²`
(`AlgebraicGeometry.projectiveLineCube.triquadraticSection`), a global section of
`𝒪(2, 2, 2)`. Its zero scheme `X = Z(F) ⊆ P` ([Stacks, Tag 01X0], [Stacks, Tag 02OQ]) is the
*triquadratic surface* of `coef`.

* `X` is proper over `Spec R`, being closed in `P`.
* `𝒪(1, 1, 1)|_X` is ample, being the restriction of an ample module along a closed
  immersion.
* On the chart `V_c` of `P`, `X ∩ V_c` is the affine hypersurface
  `Spec R[x₀, x₁, x₂] / (f_c)` cut out by the dehomogenization `f_c` of `F`.
* If `coef` is invariant under the cyclic permutation of its three indices, the cyclic
  permutation `ρ` of the factors of `P` restricts to an automorphism of `X` over `Spec R`: its
  local equations are permuted by `xᵢ ↦ x_{i+1}`, so it preserves the ideal of `X`
  (`Scheme.IdealSheafData.le_of_iSup_eq_top`).

## Main definitions

* `AlgebraicGeometry.projectiveLineCube.triquadraticSurface`: the zero scheme `X`, with its closed
  immersion `triquadraticSurfaceι` into `P` and its structure morphism `triquadraticSurfaceToBase`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticChartPolynomial`: the dehomogenization `f_c`.
* `AlgebraicGeometry.projectiveLineCube.surfaceChart`: the open `X ∩ V_c` of `X`.
* `AlgebraicGeometry.projectiveLineCube.surfaceChartEquiv`:
  `R[x₀, x₁, x₂] / (f_c) ≃ Γ(X, X ∩ V_c)`.
* `AlgebraicGeometry.projectiveLineCube.surfaceRotation`: the automorphism of `X` induced by `ρ`.

## Main results

* `AlgebraicGeometry.projectiveLineCube.isProper_triquadraticSurfaceToBase`.
* `AlgebraicGeometry.projectiveLineCube.isAmple_pullback_twist_one_one_one`.
* `AlgebraicGeometry.projectiveLineCube.triquadraticIdeal_chartOpen`: the ideal of `X` on `V_c` is
  `(f_c)`.
* `AlgebraicGeometry.projectiveLineCube.surfaceRotation_hom_ι`: `ρ_X` is the restriction of `ρ`.
* `AlgebraicGeometry.projectiveLineCube.exists_mem_nonvanishingOpen_triquadraticCoefficient`: the
  coefficients `A₀, A₁, A₂` have no common zero when their dehomogenizations generate the unit
  ideal on every chart.

## References

* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace projectiveLineCube

open cubeProduct Stacks.SheafOfModules

variable (R : Type u) [CommRing R] (coef : Fin 3 → Fin 3 → Fin 3 → ℤ)

/-- The biquadratic coefficient `A_l = ∑ coef i j l · mᵢ ⊗ mⱼ` of `z_0^{2-l} z_1^l` in the
triquadratic form of `coef`. -/
abbrev triquadraticCoefficient (S : Scheme.{u}) (l : Fin 3) : Γ(biquadraticModule S, ⊤) :=
  biquadraticSection S fun i j => coef i j l

/-- The triquadratic form `A₀ z₀² + A₁ z₀ z₁ + A₂ z₁²` of the coefficient array `coef`. -/
abbrev triquadraticForm (S : Scheme.{u}) : Γ(triquadraticModule S, ⊤) :=
  triquadraticSection S (triquadraticCoefficient coef S 0) (triquadraticCoefficient coef S 1)
    (triquadraticCoefficient coef S 2)

/-- The ideal sheaf of the zero scheme of the triquadratic form of `coef`. -/
abbrev triquadraticIdeal (S : Scheme.{u}) : (projectiveLineCube S).IdealSheafData :=
  Stacks.Divisors.zeroScheme _ (triquadraticModule S) (triquadraticForm coef S)

/-- **The triquadratic surface** of `coef` over `S`: the zero scheme of its triquadratic form in
`S × ℙ¹ × ℙ¹ × ℙ¹`. -/
abbrev triquadraticSurface (S : Scheme.{u}) : Scheme.{u} := (triquadraticIdeal coef S).subscheme

/-- The closed immersion of the triquadratic surface into `S × ℙ¹ × ℙ¹ × ℙ¹`. -/
abbrev triquadraticSurfaceι (S : Scheme.{u}) : triquadraticSurface coef S ⟶ projectiveLineCube S :=
  (triquadraticIdeal coef S).subschemeι

/-- The structure morphism of the triquadratic surface. -/
abbrev triquadraticSurfaceToBase (S : Scheme.{u}) : triquadraticSurface coef S ⟶ S :=
  triquadraticSurfaceι coef S ≫ toBase S _

/-- **A triquadratic surface is proper over the base.** -/
instance isProper_triquadraticSurfaceToBase (S : Scheme.{u}) :
    IsProper (triquadraticSurfaceToBase coef S) := by
  dsimp only [triquadraticSurfaceToBase]
  infer_instance

/-- **`𝒪(1, 1, 1)` restricted to a triquadratic surface over an affine base is ample.** -/
theorem isAmple_pullback_twist_one_one_one (S : Scheme.{u}) [IsAffine S] :
    Scheme.Modules.IsAmple (triquadraticSurface coef S)
      ((Scheme.Modules.pullback (triquadraticSurfaceι coef S)).obj (twist S 1 1 1)) :=
  isAmple_pullback_of_isFinite _ _ (isAmple_twist_one_one_one S)

/-! ### The charts -/

/-- **The dehomogenization of the triquadratic form of `coef` on the chart `V_c`**:
`f_c = ∑_l a_l x₂^{e(c₂, l)}` with `a_l` the dehomogenization of `A_l`. -/
def triquadraticChartPolynomial (c : Fin 3 → Fin 2) : MvPolynomial (Fin 3) ℤ :=
  ∑ l, biquadraticChartPolynomial (fun i j => coef i j l) c *
    MvPolynomial.X 2 ^ dehomExponent (c 2) l

/-- The chart `V_c`, as an affine open of `Spec R × ℙ¹ × ℙ¹ × ℙ¹`. -/
abbrev chartAffineOpen (c : Fin 3 → Fin 2) : (projectiveLineCube (Spec (.of R))).affineOpens :=
  ⟨chartOpen _ c, isAffineOpen_chartOpen _ c⟩

/-- **The local equation of the triquadratic surface on a chart**: its ideal on `V_c` is
generated by the dehomogenization `f_c`. -/
theorem triquadraticIdeal_chartOpen (c : Fin 3 → Fin 2) :
    (triquadraticIdeal coef (Spec (.of R))).ideal (chartAffineOpen R c) =
      Ideal.span {chartRingHom R c (MvPolynomial.map (Int.castRingHom R)
        (triquadraticChartPolynomial coef c))} := by
  refine (zeroScheme_ideal_eq_span_divBySection _ _ (chartFrame _ c) (chartAffineOpen R c)
    (chartOpen_le_nonvanishingOpen_chartFrame _ c)).trans ?_
  congr 2
  refine (divBySection_triquadraticSection _ _ _ _ c).trans ?_
  rw [divBySection_biquadraticSection, divBySection_biquadraticSection,
    divBySection_biquadraticSection, chartRingHom_map_intCast, triquadraticChartPolynomial,
    Fin.sum_univ_three]
  simp [MvPolynomial.eval₂_add, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow,
    MvPolynomial.eval₂_X]

/-- The chart `X ∩ V_c` of the triquadratic surface. -/
abbrev surfaceChart (c : Fin 3 → Fin 2) : (triquadraticSurface coef (Spec (.of R))).Opens :=
  triquadraticSurfaceι coef _ ⁻¹ᵁ chartOpen _ c

/-- The chart `X ∩ V_c` of the triquadratic surface is an affine open. -/
theorem isAffineOpen_surfaceChart (c : Fin 3 → Fin 2) :
    IsAffineOpen (surfaceChart R coef c) :=
  (isAffineOpen_chartOpen _ c).preimage _

/-- The charts `X ∩ V_c` cover the triquadratic surface. -/
theorem iSup_surfaceChart : ⨆ c, surfaceChart R coef c = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, iSup_chartOpen, Scheme.Hom.preimage_top]

/-- **A chart of the triquadratic surface is an affine hypersurface**:
`Γ(X, X ∩ V_c) ≅ R[x₀, x₁, x₂] / (f_c)`. -/
def surfaceChartEquiv (c : Fin 3 → Fin 2) :
    (MvPolynomial (Fin 3) R ⧸ Ideal.span {MvPolynomial.map (Int.castRingHom R)
      (triquadraticChartPolynomial coef c)}) ≃+*
      Γ(triquadraticSurface coef (Spec (.of R)), surfaceChart R coef c) :=
  (Ideal.quotientEquiv _ _ (chartRingEquiv R c) (by
    rw [triquadraticIdeal_chartOpen, Ideal.map_span, Set.image_singleton]
    rfl)).trans
    ((triquadraticIdeal coef (Spec (.of R))).subschemeObjIso
      (chartAffineOpen R c)).symm.commRingCatIsoToRingEquiv

/-- The identification `R[x] / (f_c) ≃ Γ(X, X ∩ V_c)` sends the class of a polynomial to the
restriction to `X` of the corresponding function on `V_c`. -/
theorem surfaceChartEquiv_mk (c : Fin 3 → Fin 2) (p : MvPolynomial (Fin 3) R) :
    surfaceChartEquiv R coef c (Ideal.Quotient.mk _ p) =
      ((triquadraticSurfaceι coef _).app (chartOpen _ c)).hom (chartRingHom R c p) := by
  rw [show (triquadraticSurfaceι coef (Spec (.of R))).app (chartOpen _ c) =
      (triquadraticIdeal coef (Spec (.of R))).subschemeι.app (chartAffineOpen R c) from rfl,
    Scheme.IdealSheafData.subschemeι_app]
  rfl

/-! ### The coefficients have no common zero -/

/-- **The biquadratic coefficients have no common zero** as soon as, on every chart, their
dehomogenizations generate the unit ideal: every point lies in the nonvanishing locus of one of
`A₀, A₁, A₂`. -/
theorem exists_mem_nonvanishingOpen_triquadraticCoefficient
    (h : ∀ c : Fin 3 → Fin 2, Ideal.span (Set.range fun l : Fin 3 =>
      MvPolynomial.map (Int.castRingHom R) (biquadraticChartPolynomial (fun i j => coef i j l) c)) =
        ⊤)
    (x : projectiveLineCube (Spec (.of R))) :
    ∃ l, x ∈ nonvanishingOpen (X := (projectiveLineCube (Spec (.of R))).toRingedSpace)
      (biquadraticModule _) (sectionsOfTop (biquadraticModule _)
        (triquadraticCoefficient coef (Spec (.of R)) l)) := by
  obtain ⟨c, hc⟩ : ∃ c, x ∈ chartOpen (Spec (.of R)) c := by
    have hx : x ∈ ⨆ c, chartOpen (Spec (.of R)) c := by rw [iSup_chartOpen]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  let ratio : Fin 3 → Γ(projectiveLineCube (Spec (.of R)), chartOpen _ c) := fun l =>
    divBySection (X := (projectiveLineCube (Spec (.of R))).toRingedSpace) (biquadraticModule _)
      (biquadraticFrame _ c) (chartOpen_le_nonvanishingOpen_biquadraticFrame _ c)
      ((biquadraticModule _).presheaf.map (homOfLE le_top).op
        (triquadraticCoefficient coef (Spec (.of R)) l))
  have hratio : ∀ l, ratio l = chartRingHom R c (MvPolynomial.map (Int.castRingHom R)
      (biquadraticChartPolynomial (fun i j => coef i j l) c)) := fun l =>
    (divBySection_biquadraticSection _ _ c).trans (chartRingHom_map_intCast R c _).symm
  have hspan : Ideal.span (Set.range ratio) = ⊤ := by
    have := congrArg (Ideal.map (chartRingHom R c)) (h c)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
    convert this using 3
    exact funext hratio
  have hcov := ((isAffineOpen_chartOpen _ c).self_le_iSup_basicOpen_iff).mpr hspan hc
  obtain ⟨⟨_, l, rfl⟩, hl⟩ := TopologicalSpace.Opens.mem_iSup.mp hcov
  refine ⟨l, ?_⟩
  have hframe := Stacks.SheafOfModules.Invertible.sectionsOfTop_eval_top_self
    (X := (projectiveLineCube (Spec (.of R))).toRingedSpace) (biquadraticModule _)
    (biquadraticFrame _ c)
  have hT : chartOpen (Spec (.of R)) c ≤ nonvanishingOpen
      (X := (projectiveLineCube (Spec (.of R))).toRingedSpace) (biquadraticModule _)
      (sectionsOfTop (biquadraticModule _) ((biquadraticFrame _ c).eval (op ⊤))) := by
    rw [hframe]
    exact chartOpen_le_nonvanishingOpen_biquadraticFrame _ c
  have hh : ratio l • (sectionsOfTop (biquadraticModule _)
      ((biquadraticFrame _ c).eval (op ⊤))).eval (op (chartOpen _ c)) =
      (sectionsOfTop (biquadraticModule _)
        (triquadraticCoefficient coef (Spec (.of R)) l)).eval (op (chartOpen _ c)) := by
    rw [hframe]
    exact smul_divBySection (X := (projectiveLineCube (Spec (.of R))).toRingedSpace) _ _ _ _
  have hb := Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq (biquadraticModule _)
    (chartOpen _ c) _ _ hT (ratio l) hh
  rw [hb] at hl
  exact hl.1

/-! ### The cyclic permutation of the factors -/

/-- The coefficient array `coef` is invariant under the cyclic permutation of its three
indices. -/
def IsCyclicCoefficients : Prop := ∀ i j l, coef j l i = coef i j l

/-- The dehomogenization `f_c` expanded as the sum over `l, i, j` of
`coef i j l · x₀^{e(c₀, i)} x₁^{e(c₁, j)} x₂^{e(c₂, l)}`. -/
theorem triquadraticChartPolynomial_eq_sum (c : Fin 3 → Fin 2) :
    triquadraticChartPolynomial coef c =
      ∑ l, ∑ i, ∑ j, MvPolynomial.C (coef i j l) * (MvPolynomial.X 0 ^ dehomExponent (c 0) i *
        MvPolynomial.X 1 ^ dehomExponent (c 1) j * MvPolynomial.X 2 ^ dehomExponent (c 2) l) := by
  simp only [triquadraticChartPolynomial, biquadraticChartPolynomial, Finset.sum_mul, mul_assoc]

/-- **Cyclic symmetry of the dehomogenizations**: for cyclically invariant coefficients, the
substitution `xᵢ ↦ x_{i+1}` carries the dehomogenization on `V_c` to the one on
`ρ⁻¹ V_c`. -/
theorem rename_triquadraticChartPolynomial (h : IsCyclicCoefficients coef) (c : Fin 3 → Fin 2) :
    MvPolynomial.rename (· + 1) (triquadraticChartPolynomial coef c) =
      triquadraticChartPolynomial coef (rotateChart c) := by
  rw [triquadraticChartPolynomial_eq_sum, triquadraticChartPolynomial_eq_sum]
  simp only [map_sum, map_mul, MvPolynomial.rename_C, map_pow, MvPolynomial.rename_X]
  have h0 : rotateChart c 0 = c 2 := rfl
  have h1 : rotateChart c 1 = c 0 := rfl
  have h2 : rotateChart c 2 = c 1 := rfl
  rw [h0, h1, h2]
  trans ∑ l, ∑ i, ∑ j, MvPolynomial.C (coef l i j) * (MvPolynomial.X 0 ^ dehomExponent (c 2) l *
    MvPolynomial.X 1 ^ dehomExponent (c 0) i * MvPolynomial.X 2 ^ dehomExponent (c 1) j)
  · refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => ?_
    rw [← h l i j]
    simp only [show (0 : Fin 3) + 1 = 1 from rfl, show (1 : Fin 3) + 1 = 2 from rfl,
      show (2 : Fin 3) + 1 = 0 from rfl]
    ring
  · conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_rhs => rw [Finset.sum_comm]

variable {coef}

/-- For cyclically invariant coefficients, the ideal of the triquadratic surface lies in the
kernel of `X ⟶ P ⟶ P`, the second map being the cyclic permutation of the factors. -/
theorem triquadraticIdeal_le_ker_rotation (h : IsCyclicCoefficients coef) :
    triquadraticIdeal coef (Spec (.of R)) ≤
      (triquadraticSurfaceι coef _ ≫ (rotation _ (projectiveSpaceAtUniverse.{u} 1)).hom).ker := by
  refine Scheme.IdealSheafData.le_of_iSup_eq_top (chartAffineOpen R) (iSup_chartOpen _)
    fun c => ?_
  rw [triquadraticIdeal_chartOpen, Scheme.Hom.ker_apply, Ideal.span_le,
    Set.singleton_subset_iff]
  refine RingHom.mem_ker.mpr ?_
  have hpre := rotation_preimage_chartOpen (Spec (.of R)) c
  have e : chartOpen _ (rotateChart c) ≤
      (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom ⁻¹ᵁ chartOpen _ c :=
    hpre.ge
  have e₂ : (triquadraticSurfaceι coef _ ≫
      (rotation (Spec (.of R)) (projectiveSpaceAtUniverse.{u} 1)).hom) ⁻¹ᵁ chartOpen _ c ≤
      triquadraticSurfaceι coef _ ⁻¹ᵁ chartOpen (Spec (.of R)) (rotateChart c) := by
    rw [Scheme.Hom.comp_preimage, hpre]
  rw [Scheme.Hom.app_eq_appLE, ← Scheme.Hom.appLE_comp_appLE _ _ _ _ _ e e₂,
    CommRingCat.comp_apply, rotation_appLE_chartRingHom, ← MvPolynomial.map_rename,
    rename_triquadraticChartPolynomial coef h]
  have hmem : chartRingHom R (rotateChart c) (MvPolynomial.map (Int.castRingHom R)
      (triquadraticChartPolynomial coef (rotateChart c))) ∈
      RingHom.ker ((triquadraticSurfaceι coef _).app (chartOpen _ (rotateChart c))).hom := by
    rw [← Scheme.Hom.ker_apply _ (chartAffineOpen R (rotateChart c)),
      Scheme.IdealSheafData.ker_subschemeι, triquadraticIdeal_chartOpen]
    exact Ideal.subset_span rfl
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, RingHom.mem_ker.mp hmem, map_zero]

/-- The endomorphism of the triquadratic surface induced by the cyclic permutation of the
factors. -/
def surfaceRotationHom (h : IsCyclicCoefficients coef) :
    triquadraticSurface coef (Spec (.of R)) ⟶ triquadraticSurface coef (Spec (.of R)) :=
  (triquadraticSurfaceι coef _ ≫ (rotation _ (projectiveSpaceAtUniverse.{u} 1)).hom).toImage ≫
    Scheme.IdealSheafData.inclusion (triquadraticIdeal_le_ker_rotation R h)

/-- The endomorphism induced by the cyclic permutation `ρ` is the restriction of `ρ`:
`ρ_X ≫ ι = ι ≫ ρ`. -/
@[reassoc (attr := simp)]
theorem surfaceRotationHom_ι (h : IsCyclicCoefficients coef) :
    surfaceRotationHom R h ≫ triquadraticSurfaceι coef _ =
      triquadraticSurfaceι coef _ ≫ (rotation _ (projectiveSpaceAtUniverse.{u} 1)).hom := by
  simp [surfaceRotationHom]

/-- The cube of the endomorphism induced by the cyclic permutation of the factors is the
identity. -/
theorem surfaceRotationHom_pow_three (h : IsCyclicCoefficients coef) :
    surfaceRotationHom R h ≫ surfaceRotationHom R h ≫ surfaceRotationHom R h = 𝟙 _ := by
  rw [← cancel_mono (triquadraticSurfaceι coef _)]
  simp only [Category.assoc, surfaceRotationHom_ι, surfaceRotationHom_ι_assoc, Category.id_comp]
  rw [permutationIso_hom, permutation_comp, permutation_comp,
    show finRotate 3 * (finRotate 3 * finRotate 3) = 1 by decide, permutation_one,
    Category.comp_id]

/-- **The cyclic permutation of the factors restricts to an automorphism of a cyclically
symmetric triquadratic surface.** -/
def surfaceRotation (h : IsCyclicCoefficients coef) :
    triquadraticSurface coef (Spec (.of R)) ≅ triquadraticSurface coef (Spec (.of R)) where
  hom := surfaceRotationHom R h
  inv := surfaceRotationHom R h ≫ surfaceRotationHom R h
  hom_inv_id := surfaceRotationHom_pow_three R h
  inv_hom_id := by rw [Category.assoc, surfaceRotationHom_pow_three]

/-- The automorphism `ρ_X` is the restriction of the cyclic permutation `ρ`:
`ρ_X ≫ ι = ι ≫ ρ`. -/
@[reassoc (attr := simp)]
theorem surfaceRotation_hom_ι (h : IsCyclicCoefficients coef) :
    (surfaceRotation R h).hom ≫ triquadraticSurfaceι coef _ =
      triquadraticSurfaceι coef _ ≫ (rotation _ (projectiveSpaceAtUniverse.{u} 1)).hom :=
  surfaceRotationHom_ι R h

/-- The automorphism `ρ_X` is an automorphism over the base. -/
@[reassoc (attr := simp)]
theorem surfaceRotation_hom_toBase (h : IsCyclicCoefficients coef) :
    (surfaceRotation R h).hom ≫ triquadraticSurfaceToBase coef _ =
      triquadraticSurfaceToBase coef _ := by
  rw [triquadraticSurfaceToBase, surfaceRotation_hom_ι_assoc, permutationIso_hom,
    permutation_toBase]

end projectiveLineCube

end AlgebraicGeometry
