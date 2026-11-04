module
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjGlobalSectionsAppTop.Consumers
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

public import StacksFrontier.AlgebraicGeometry.Limits.BinaryFormMultiplication
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.VietaEvaluation
public import StacksFrontier.AlgebraicGeometry.Segre.Basic

/-!
# The multiplication of binary forms is surjective

`AlgebraicGeometry.ProjectiveSpace.binaryFormMul n : ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ` multiplies a
binary form of degree `n` by a linear form. This file proves that it is **surjective**.

The source is proper over `Spec ℤ` and the target separated, so the multiplication is proper and
its image is closed. A closed subset of `ℙⁿ⁺¹` that meets every nonempty standard open `D₊(G)` is
everything (`surjective_of_isClosedMap_of_basicOpen`), since the `D₊(G)` form a basis. To meet
`D₊(G)` one point suffices, and it is produced as a ring-valued point: over
`B = ℤ[r₀, …, rₙ]` take `((r₀ : 1) ⋯ (r_{n-1} : 1)) ↦` the coefficients of `∏_{i<n} (T + rᵢ)` in
`ℙⁿ` and `(rₙ : 1)` in `ℙ¹`. Its image in `ℙⁿ⁺¹` has the coefficients of `∏_{i ≤ n} (T + rᵢ)` as
homogeneous coordinates, and a nonzero homogeneous `G` does not vanish there
(`Stacks.ProjectiveChart.aeval_coeff_prod_X_add_C_ne_zero`, the fundamental theorem of symmetric
polynomials), so the generic point of `Spec B` lands in `D₊(G)`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpace.chartPoint`: the ring homomorphism out of the last chart
  ring of `ℙᴺ` sending `Xₖ / X_N` to a prescribed `wₖ`, and
  `AlgebraicGeometry.ProjectiveSpace.chartPointHom` the resulting ring-valued point of `ℙᴺ`.
* `AlgebraicGeometry.ProjectiveSpace.testPoint`: the point of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` over
  `ℤ[r₀, …, rₙ]` given by the coefficients of `∏_{i<n} (T + rᵢ)` and of `T + rₙ`.

## Main results

* `AlgebraicGeometry.ProjectiveSpace.surjective_of_isClosedMap_of_basicOpen`: a closed morphism
  to `ℙᴺ_ℤ` whose image meets every nonempty standard open is surjective.
* `AlgebraicGeometry.ProjectiveSpace.testPoint_binaryFormMul`: the image of the test point has
  the coefficients of `∏_{i ≤ n} (T + rᵢ)` as homogeneous coordinates.
* `AlgebraicGeometry.ProjectiveSpace.exists_mem_basicOpen_binaryFormMul`: the image of the
  multiplication meets every nonempty standard open.
* `AlgebraicGeometry.ProjectiveSpace.surjective_binaryFormMul`: **the multiplication of binary
  forms is surjective.**
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open Stacks.SectionsToProjectiveSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **A closed morphism to `ℙᴺ_ℤ` whose image meets every nonempty standard open is
surjective.** -/
theorem surjective_of_isClosedMap_of_basicOpen {N : ℕ} {Y : Scheme.{u}}
    (f : Y ⟶ Proj (coordGrading.{u} N)) (hf : IsClosedMap f)
    (h : ∀ (G : coordRing.{u} N) (d : ℕ), 0 < d → G ∈ coordGrading.{u} N d → G ≠ 0 →
      ∃ y, f y ∈ Proj.basicOpen (coordGrading.{u} N) G) :
    Surjective f := by
  refine ⟨fun x => ?_⟩
  by_contra hx
  let V : (Proj (coordGrading.{u} N)).Opens := ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩
  obtain ⟨_, ⟨F, rfl⟩, hxF, hFV⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Proj.isBasis_basicOpen (coordGrading.{u} N)))
      (show x ∈ V from hx)
  rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup] at hxF
  obtain ⟨i, hi⟩ := hxF
  have hcov := Stacks.ProjectiveChart.iSup_basicOpen_X_eq_top (ULift.{u} ℤ) N
  have hxtop : x ∈ (⊤ : (Proj (coordGrading.{u} N)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hxtop
  obtain ⟨k, hk⟩ := hxtop
  set G := GradedRing.proj (coordGrading.{u} N) i F * MvPolynomial.X k with hG
  have hxG : x ∈ Proj.basicOpen (coordGrading.{u} N) G := by
    rw [hG, Proj.basicOpen_mul]
    exact ⟨hi, hk⟩
  have hGdeg : G ∈ coordGrading.{u} N (i + 1) := by
    rw [hG, GradedRing.proj_apply]
    exact SetLike.mul_mem_graded (SetLike.coe_mem _) (X_mem_coordGrading_one k)
  have hG0 : G ≠ 0 := by
    intro h0
    rwa [h0, Proj.basicOpen_zero] at hxG
  obtain ⟨y, hy⟩ := h G (i + 1) (Nat.succ_pos i) hGdeg hG0
  have hyF : f y ∈ V := by
    refine hFV ?_
    rw [Proj.basicOpen_eq_iSup_proj, TopologicalSpace.Opens.mem_iSup]
    refine ⟨i, ?_⟩
    rw [hG, Proj.basicOpen_mul] at hy
    exact hy.1
  exact hyF ⟨y, rfl⟩

section Point

/-- **The ring homomorphism out of the last chart ring of `ℙᴺ_ℤ` with prescribed ratios.** The
last chart ring is a polynomial ring in the ratios `Xₖ / X_N`, `k < N`
(`Stacks.ProjectiveChart.chartRingEquiv`), and this sends `Xₖ / X_N` to `wₖ`. -/
def chartPoint {B : Type u} [CommRing B] [Algebra (ULift.{u} ℤ) B] (N : ℕ) (w : Fin (N + 1) → B) :
    Away (coordGrading.{u} N) (MvPolynomial.X (Fin.last N)) →+* B :=
  (MvPolynomial.aeval (fun j : Fin N => w j.castSucc)).toRingHom.comp
    (Stacks.ProjectiveChart.chartRingEquiv (ULift.{u} ℤ) (Fin.last N)).symm.toRingHom

/-- `chartPoint` sends the ratio `Xₖ / X_N` to `wₖ`, provided `w_N = 1`. -/
theorem chartPoint_ratio {B : Type u} [CommRing B] [Algebra (ULift.{u} ℤ) B] {N : ℕ}
    (w : Fin (N + 1) → B) (hw : w (Fin.last N) = 1) (k : Fin (N + 1)) :
    chartPoint N w (Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) (Fin.last N) k) = w k := by
  induction k using Fin.lastCases with
  | last => rw [Stacks.ProjectiveChart.ratio_self, map_one, hw]
  | cast j =>
      have hX : Stacks.ProjectiveChart.chartRingEquiv (ULift.{u} ℤ) (Fin.last N)
          (MvPolynomial.X j) =
          Stacks.ProjectiveChart.ratio (ULift.{u} ℤ) (Fin.last N) j.castSucc := by
        rw [← Fin.succAbove_last]
        simp [Stacks.ProjectiveChart.chartRingEquiv, Stacks.ProjectiveChart.chartRingEquivDeg0,
          Stacks.ProjectiveChart.chartHom]
      rw [← hX, chartPoint, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
      simp

/-- The morphism `Spec B ⟶ ℙᴺ_ℤ` through the last chart, with ratios `w`. -/
def chartPointHom {B : Type u} [CommRing B] [Algebra (ULift.{u} ℤ) B] (N : ℕ)
    (w : Fin (N + 1) → B) : Spec (CommRingCat.of B) ⟶ Proj (coordGrading.{u} N) :=
  Spec.map (CommRingCat.ofHom (chartPoint N w)) ≫
    Proj.awayι (coordGrading.{u} N) (MvPolynomial.X (Fin.last N)) (X_mem_coordGrading_one _)
      Nat.one_pos

/-- `chartPointHom` lands in the last standard open. -/
theorem top_le_chartPointHom_preimage {B : Type u} [CommRing B] [Algebra (ULift.{u} ℤ) B]
    (N : ℕ) (w : Fin (N + 1) → B) :
    ⊤ ≤ chartPointHom N w ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} N) (MvPolynomial.X (Fin.last N)) :=
  fun _ _ => (Proj.opensRange_awayι (coordGrading.{u} N) (MvPolynomial.X (Fin.last N))
    (X_mem_coordGrading_one _) Nat.one_pos).le ⟨_, rfl⟩

/-- Along `chartPointHom`, the ratio `Xₖ / X_N` pulls back to `wₖ`. -/
theorem pullRatio_chartPointHom {B : Type u} [CommRing B] [Algebra (ULift.{u} ℤ) B] {N : ℕ}
    (w : Fin (N + 1) → B) (hw : w (Fin.last N) = 1) (k : Fin (N + 1))
    (h : ⊤ ≤ chartPointHom N w ⁻¹ᵁ
      Proj.basicOpen (coordGrading.{u} N) (MvPolynomial.X (Fin.last N))) :
    pullRatio (chartPointHom N w) (Fin.last N) k h =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (w k) :=
  (pullRatio_SpecMap_awayι (Fin.last N) k (CommRingCat.ofHom (chartPoint N w)) h).trans
    (by rw [CommRingCat.hom_ofHom, chartPoint_ratio w hw])

end Point

section Surjective

variable (n : ℕ)

/-- The split polynomial `∏_{i<n} (T + rᵢ)` over `ℤ[r₀, …, rₙ]`. -/
abbrev splitFst : Polynomial (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :=
  ∏ i : Fin n, (Polynomial.X + Polynomial.C (MvPolynomial.X i.castSucc))

/-- The linear polynomial `T + rₙ` over `ℤ[r₀, …, rₙ]`. -/
abbrev splitSnd : Polynomial (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) :=
  Polynomial.X + Polynomial.C (MvPolynomial.X (Fin.last n))

open Polynomial in
/-- `∏_{i<n} (T + rᵢ)` has degree `n`. -/
theorem natDegree_splitFst : (splitFst.{u} n).natDegree = n := by
  rw [splitFst, natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp

open Polynomial in
/-- `∏_{i<n} (T + rᵢ)` is monic. -/
theorem monic_splitFst : (splitFst.{u} n).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

open Polynomial in
/-- The ring-valued point of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` over `ℤ[r₀, …, rₙ]`: the coefficients of
`∏_{i<n} (T + rᵢ)` in `ℙⁿ` and those of `T + rₙ` in `ℙ¹`. -/
def testPoint :
    Spec (CommRingCat.of (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) ⟶ mulSource.{u} n :=
  pullback.lift (chartPointHom n (fun i => (splitFst.{u} n).coeff i))
    (chartPointHom 1 (fun j => (splitSnd.{u} n).coeff j)) (terminal.hom_ext _ _)

/-- The chart of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` the test point lands in: the last coordinate is `1` on
both factors. -/
abbrev lastChart : Fin (n + 1) × Fin (1 + 1) := (Fin.last n, Fin.last 1)

/-- The coefficients of `∏_{i ≤ n} (T + rᵢ)`, the homogeneous coordinates of the image of the
test point. -/
abbrev splitCoeffs (k : Fin (n + 1 + 1)) : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) :=
  (∏ i : Fin (n + 1), (Polynomial.X +
    Polynomial.C (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)))).coeff k

/-- The coefficient of `Tⁿ` in `∏_{i<n} (T + rᵢ)` is `1`. -/
theorem splitFst_coeff_last : (splitFst.{u} n).coeff (Fin.last n) = 1 := by
  have h := (monic_splitFst.{u} n).coeff_natDegree
  rwa [natDegree_splitFst] at h

/-- The coefficient of `T` in `T + rₙ` is `1`. -/
theorem splitSnd_coeff_last : (splitSnd.{u} n).coeff (Fin.last 1) = 1 := by
  simp [splitSnd]

/-- The test point lands in the last chart. -/
theorem range_testPoint_subset :
    Set.range (testPoint.{u} n) ⊆ Set.range (mulChart.{u} n (lastChart n)).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have h1 : testPoint.{u} n ≫ mulFst n = chartPointHom n (fun i => (splitFst.{u} n).coeff i) :=
    pullback.lift_fst _ _ _
  have h2 : testPoint.{u} n ≫ mulSnd n = chartPointHom 1 (fun j => (splitSnd.{u} n).coeff j) :=
    pullback.lift_snd _ _ _
  refine ⟨?_, ?_⟩
  · have := top_le_chartPointHom_preimage n (fun i => (splitFst.{u} n).coeff i)
      (show x ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [← h1] at this
  · have := top_le_chartPointHom_preimage 1 (fun j => (splitSnd.{u} n).coeff j)
      (show x ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [← h2] at this

/-- The test point, factored through the chart it lands in. -/
def testPointChart : Spec (CommRingCat.of (MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ))) ⟶
    (mulChart.{u} n (lastChart n)).toScheme :=
  IsOpenImmersion.lift (mulChart.{u} n (lastChart n)).ι (testPoint n) (range_testPoint_subset n)

/-- The factored test point composed with the inclusion of the chart is the test point. -/
theorem testPointChart_ι :
    testPointChart.{u} n ≫ (mulChart.{u} n (lastChart n)).ι = testPoint n :=
  IsOpenImmersion.lift_fac _ _ _

/-- Pulling back the ratio `Xᵢ / X_N` along a map `g` into `Spec B` whose composite with `ψ` is
`chartPointHom N w` gives `wᵢ`. -/
private theorem appTop_pullRatio_chartPointHom {B : Type u} [CommRing B]
    [Algebra (ULift.{u} ℤ) B] {N : ℕ} {Z : Scheme.{u}} (w : Fin (N + 1) → B)
    (hw : w (Fin.last N) = 1) (g : Spec (CommRingCat.of B) ⟶ Z)
    (ψ : Z ⟶ Proj (coordGrading.{u} N)) (hg : g ≫ ψ = chartPointHom N w) (i : Fin (N + 1))
    (h : ⊤ ≤ ψ ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} N) (MvPolynomial.X (Fin.last N))) :
    g.appTop.hom (pullRatio ψ (Fin.last N) i h) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (w i) := by
  rw [appTop_pullRatio _ _ _ _ _ (by rw [hg]; exact top_le_chartPointHom_preimage N w),
    pullRatio_congr hg _ _ _ (top_le_chartPointHom_preimage N w)]
  exact pullRatio_chartPointHom _ hw i _

/-- The coordinates of the product, pulled back to the test point, are the coefficients of
`∏_{i ≤ n} (T + rᵢ)`. -/
theorem appTop_testPointChart_mulChartCoeffs (k : Fin (n + 1 + 1)) :
    (testPointChart.{u} n).appTop.hom (mulChartCoeffs (lastChart n) k) =
      (Scheme.ΓSpecIso _).inv.hom (splitCoeffs n k) := by
  classical
  have hfst : ∀ i h, (testPointChart.{u} n).appTop.hom (fstRatio (lastChart n).1 i h) =
      (Scheme.ΓSpecIso _).inv.hom ((splitFst.{u} n).coeff i) := fun i h =>
    appTop_pullRatio_chartPointHom _ (splitFst_coeff_last n) _
      ((mulChart.{u} n (lastChart n)).ι ≫ mulFst n) (by
      rw [← Category.assoc, testPointChart_ι, testPoint, mulFst, pullback.lift_fst]) i _
  have hsnd : ∀ j h, (testPointChart.{u} n).appTop.hom (sndRatio (lastChart n).2 j h) =
      (Scheme.ΓSpecIso _).inv.hom ((splitSnd.{u} n).coeff j) := fun j h =>
    appTop_pullRatio_chartPointHom _ (splitSnd_coeff_last n) _
      ((mulChart.{u} n (lastChart n)).ι ≫ mulSnd n) (by
      rw [← Category.assoc, testPointChart_ι, testPoint, mulSnd, pullback.lift_snd]) j _
  rw [mulChartCoeffs, map_mulCoeffs]
  simp only [hfst, hsnd]
  rw [← map_mulCoeffs, mulCoeffs_coeff (natDegree_splitFst n).le
    (Polynomial.natDegree_X_add_C _).le, splitCoeffs, Fin.prod_univ_castSucc]

/-- **The image of the test point** has the coefficients of `∏_{i ≤ n} (T + rᵢ)` as homogeneous
coordinates. -/
theorem testPoint_binaryFormMul :
    testPoint.{u} n ≫ binaryFormMul n =
      toProjectiveSpaceAtUniverse (fun k => (Scheme.ΓSpecIso _).inv.hom (splitCoeffs.{u} n k))
        (by
          rw [← funext (appTop_testPointChart_mulChartCoeffs.{u} n)]
          exact span_range_comp _ _ (span_range_mulChartCoeffs _)) := by
  rw [← testPointChart_ι, Category.assoc, mulChart_ι_binaryFormMul,
    Stacks.ProjGlobalSectionsAppTop.hasPullbackNaturality _ _ _
      (span_range_comp _ _ (span_range_mulChartCoeffs _))]
  exact toProjectiveSpaceAtUniverse_congr
    (funext (appTop_testPointChart_mulChartCoeffs.{u} n)) _ _

/-- The unique ring homomorphism out of `ULift ℤ` is the algebra map. -/
theorem coeffHom_eq_algebraMap (B : Type u) [CommRing B] [Algebra (ULift.{u} ℤ) B] :
    coeffHom B = algebraMap (ULift.{u} ℤ) B := by
  ext ⟨m⟩
  rw [show (ULift.up m : ULift.{u} ℤ) = (m : ULift.{u} ℤ) from ULift.up_intCast m,
    map_intCast, map_intCast]

/-- **The image of the multiplication meets every nonempty standard open of `ℙⁿ⁺¹_ℤ`**: for
every nonzero homogeneous `G` of positive degree, some point of `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ` maps into
`D₊(G)`. -/
theorem exists_mem_basicOpen_binaryFormMul (G : coordRing.{u} (n + 1)) (d : ℕ) (hd : 0 < d)
    (hG : G ∈ coordGrading.{u} (n + 1) d) (hG0 : G ≠ 0) :
    ∃ y, binaryFormMul n y ∈ Proj.basicOpen (coordGrading.{u} (n + 1)) G := by
  let : IsDomain (ULift.{u} ℤ) := MulEquiv.isDomain ℤ (ULift.ringEquiv (R := ℤ)).toMulEquiv
  set B := MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)
  let η : Spec (CommRingCat.of B) := (⊥ : PrimeSpectrum B)
  refine ⟨testPoint n η, ?_⟩
  show η ∈ (testPoint.{u} n ≫ binaryFormMul n) ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} (n + 1)) G
  have hpre := (congrArg (fun f : Spec (CommRingCat.of B) ⟶ Proj (coordGrading.{u} (n + 1)) =>
      f ⁻¹ᵁ Proj.basicOpen (coordGrading.{u} (n + 1)) G) (testPoint_binaryFormMul.{u} n)).trans
    (Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ hd hG)
  refine hpre.ge ?_
  have hsec : sectionsHom (fun k => (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
      (splitCoeffs.{u} n k)) G =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
        (MvPolynomial.aeval (splitCoeffs.{u} n) G) := by
    rw [sectionsHom, ← Stacks.ProjGlobalSectionsAppTop.coeffHom_comp
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom, ← MvPolynomial.comp_eval₂Hom,
      RingHom.comp_apply, coeffHom_eq_algebraMap, MvPolynomial.coe_eval₂Hom,
      MvPolynomial.aeval_def]
  rw [hsec, basicOpen_eq_of_affine]
  show MvPolynomial.aeval (splitCoeffs.{u} n) G ∉ (⊥ : Ideal B)
  rw [Ideal.mem_bot]
  exact Stacks.ProjectiveChart.aeval_coeff_prod_X_add_C_ne_zero hG hG0

/-- **The multiplication of binary forms `ℙⁿ_ℤ ×_{Spec ℤ} ℙ¹_ℤ ⟶ ℙⁿ⁺¹_ℤ` is surjective.** -/
theorem surjective_binaryFormMul : Surjective (binaryFormMul.{u} n) := by
  have hsrc : IsProper (terminal.from (mulSource.{u} n)) := isProper_terminal_from_pullback.{u} n 1
  have htgt : IsProper (terminal.from (projectiveSpaceAtUniverse.{u} (n + 1))) :=
    ProjectiveSpace.isProper_terminal_from.{u} (n + 1)
  have hcomp : IsProper (binaryFormMul.{u} n ≫ terminal.from _) := by
    rwa [terminal.comp_from]
  have := IsProper.of_comp (binaryFormMul.{u} n) (terminal.from _)
  exact surjective_of_isClosedMap_of_basicOpen (binaryFormMul.{u} n)
    (binaryFormMul.{u} n).isClosedMap (exists_mem_basicOpen_binaryFormMul n)

end Surjective

end AlgebraicGeometry.ProjectiveSpace

end
