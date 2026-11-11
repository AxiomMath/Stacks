module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaConicChart
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# The involution of `ℙ³` in Hironaka's non-scheme example

Hironaka's example of a proper algebraic space that is not a scheme (Stacks Tag 08KF) is the
quotient of his non-projective threefold by a free involution lifting the involution
`σ : [x : y : z : w] ↦ [y : x : w : z]` of `Y = ℙ³_k`. This file constructs `σ` and records how it
interacts with the data of Hironaka's construction
(`StacksFrontier/AlgebraicGeometry/Examples/HironakaConicIdealSheaf.lean`,
`StacksFrontier/AlgebraicGeometry/Examples/HironakaConicChart.lean`): it exchanges the conics
`C = {xy = z², w = 0}` and `D = {xy = w², z = 0}`, the points `P = [1 : 0 : 0 : 0]` and
`Q = [0 : 1 : 0 : 0]`, and the charts at `P` and `Q`.

The fixed locus of `σ` is the union of the lines `L₁ = {[a : a : b : b]}` and
`L₂ = {[a : -a : b : -b]}`; its complement is covered by the four basic opens `D₊(ℓ m)` with
`ℓ ∈ {x - y, z - w}` and `m ∈ {x + y, z + w}`. On `D₊(ℓ m)` the regular function `ℓ / m` is a
unit which `σ` negates, so when `2 ≠ 0` in `k` no `T`-valued point of the complement is fixed
unless `T` is empty: `σ` acts freely there in the scheme-theoretic sense.

## Main definitions

* `Stacks.Examples.HironakaInvolution.involutionHom`: the graded ring automorphism
  `x ↔ y`, `z ↔ w` of `k[x, y, z, w]`.
* `Stacks.Examples.HironakaInvolution.involution`: the involution `σ` of `ℙ³_k`, the induced map
  `AlgebraicGeometry.Proj.map`.
* `Stacks.Examples.HironakaInvolution.freeLocus`: the open `ℙ³ - (L₁ ∪ L₂)`.
* `Stacks.Examples.HironakaInvolution.freeInvolution`: the restriction of `σ` to it.

## Main results

* `Stacks.Examples.HironakaInvolution.involution_comp_involution`: `σ ∘ σ = id`.
* `Stacks.Examples.HironakaInvolution.chartP_comp_involution`,
  `Stacks.Examples.HironakaInvolution.chartQ_comp_involution`: `σ` exchanges the two charts.
* `Stacks.Examples.HironakaInvolution.comap_idealSheafC_involution`,
  `Stacks.Examples.HironakaInvolution.comap_idealSheafD_involution`: `σ* 𝒥_C = 𝒥_D` and
  `σ* 𝒥_D = 𝒥_C`.
* `Stacks.Examples.HironakaInvolution.involution_pointP`,
  `Stacks.Examples.HironakaInvolution.involution_pointQ`: `σ(P) = Q`, `σ(Q) = P`.
* `Stacks.Examples.HironakaInvolution.isEmpty_of_comp_freeInvolution_eq`: the involution of the
  free locus is free.
* `Stacks.Examples.HironakaInvolution.supportSet_idealSheafC_subset_freeLocus`,
  `Stacks.Examples.HironakaInvolution.supportSet_idealSheafD_subset_freeLocus`: the conics lie in
  the free locus.

## Implementation notes

The comparison of `σ` with the standard charts uses a variant of
`AlgebraicGeometry.Proj.awayι_comp_map` for a graded map `g` and elements with `g s = t`, so that
`D₊(g s)` can be written in its simplest form. Freeness is proved on `D₊((ℓ m)²) = D₊(ℓ m)`, an
open on which `σ` restricts to itself on the nose, with the unit `ℓ³ m / (ℓ m)² = ℓ / m`.

## References

* [Stacks Project, Tag 08KF](https://stacks.math.columbia.edu/tag/08KF)
* [H, Example B.3.4.1]
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial AlgebraicGeometry HomogeneousLocalization
open scoped HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj (homogeneousIdealSheaf
  mem_supportSet_homogeneousIdealSheaf_iff)
open Stacks.Examples.HironakaConicIntersection Stacks.Examples.HironakaConicIdealSheaf
  Stacks.Examples.HironakaConicChart

universe u

namespace Stacks.Examples.HironakaInvolution

/-! ### Graded ring maps and `Proj` -/

section General

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
  [GradedRing 𝒜] [GradedRing ℬ]

/-- The map `A_{(s)} → B_{(t)}` induced by a graded ring map `g` with `g s = t`. -/
def awayMapOfEq (g : 𝒜 →+*ᵍ ℬ) {s : A} {t : B} (h : g s = t) : Away 𝒜 s →+* Away ℬ t :=
  HomogeneousLocalization.map g (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp [h]⟩)

/-- `awayMapOfEq g h` sends `x / s ^ n` to `g x / t ^ n`. -/
theorem awayMapOfEq_mk (g : 𝒜 →+*ᵍ ℬ) {s : A} {t : B} (h : g s = t) {d : ℕ} (hs : s ∈ 𝒜 d)
    (ht : t ∈ ℬ d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    awayMapOfEq g h (Away.mk 𝒜 hs n x hx) = Away.mk ℬ ht n (g x) (g.map_mem hx) := by
  subst h
  exact Away.map_mk g s hs n x hx

/-- **The chart square of `Proj.map`, for `g s = t`.** -/
theorem awayι_comp_map_of_eq (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g) {s : A} {t : B}
    (h : g s = t) {d : ℕ} (hs : s ∈ 𝒜 d) (ht : t ∈ ℬ d) (hd : 0 < d) :
    Proj.awayι ℬ t ht hd ≫ Proj.map g hg =
      Spec.map (CommRingCat.ofHom (awayMapOfEq g h)) ≫ Proj.awayι 𝒜 s hs hd := by
  subst h
  exact Proj.awayι_comp_map g hg hd s hs

/-- **The sections square of `Proj.map`, for `g s = t`.** -/
theorem awayToSection_comp_appLE_of_eq (g : 𝒜 →+*ᵍ ℬ) (hg : ℬ₊ ≤ 𝒜₊.map g) {s : A} {t : B}
    (h : g s = t) {d : ℕ} (hs : s ∈ 𝒜 d) (e) :
    Proj.awayToSection 𝒜 s ≫ (Proj.map g hg).appLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ t) e =
      CommRingCat.ofHom (awayMapOfEq g h) ≫ Proj.awayToSection ℬ t := by
  subst h
  exact Proj.awayToSection_comp_appLE g hg hs

/-- `Proj.map` only depends on the graded ring map. -/
theorem map_congr {g g' : 𝒜 →+*ᵍ ℬ} (h : g = g') (hg : ℬ₊ ≤ 𝒜₊.map g)
    (hg' : ℬ₊ ≤ 𝒜₊.map g') : Proj.map g hg = Proj.map g' hg' := by
  subst h
  rfl

end General

/-! ### The involution -/

variable (k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The permutation `0 ↔ 1`, `2 ↔ 3` of the coordinates of `ℙ³`. -/
def swapIndex : Fin 4 → Fin 4 := ![1, 0, 3, 2]

/-- `swapIndex` is an involution. -/
theorem swapIndex_swapIndex (i : Fin 4) : swapIndex (swapIndex i) = i := by
  fin_cases i <;> rfl

/-- The renaming `x ↔ y`, `z ↔ w` of `k[x, y, z, w]`, as a graded ring map. -/
def involutionHom : homogeneousSubmodule (Fin 4) k →+*ᵍ homogeneousSubmodule (Fin 4) k where
  toRingHom := (rename swapIndex).toRingHom
  map_mem hp := (mem_homogeneousSubmodule _ _).mpr
    (((mem_homogeneousSubmodule _ _).mp hp).rename_isHomogeneous)

/-- `involutionHom` is `rename swapIndex`. -/
theorem involutionHom_apply (p : MvPolynomial (Fin 4) k) :
    involutionHom k p = rename swapIndex p :=
  rfl

/-- `involutionHom` on a variable. -/
@[simp]
theorem involutionHom_X (i : Fin 4) : involutionHom k (X i) = X (swapIndex i) :=
  rename_X _ _

/-- `involutionHom` is an involution. -/
theorem involutionHom_involutionHom (p : MvPolynomial (Fin 4) k) :
    involutionHom k (involutionHom k p) = p := by
  rw [involutionHom_apply, involutionHom_apply, rename_rename,
    show swapIndex ∘ swapIndex = id from funext swapIndex_swapIndex, rename_id_apply]

/-- `involutionHom ∘ involutionHom` is the identity graded ring map. -/
theorem involutionHom_comp_involutionHom :
    (involutionHom k).comp (involutionHom k) = GradedRingHom.id _ :=
  GradedRingHom.ext fun p => involutionHom_involutionHom k p

/-- `involutionHom` maps the irrelevant ideal onto the irrelevant ideal. -/
theorem irrelevant_le_map_involutionHom :
    (homogeneousSubmodule (Fin 4) k)₊ ≤
      (homogeneousSubmodule (Fin 4) k)₊.map (involutionHom k) := by
  refine (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr fun i hi p hp => ?_
  rw [← involutionHom_involutionHom k p]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hi ((involutionHom k).map_mem hp))

/-- **The involution `[x : y : z : w] ↦ [y : x : w : z]` of `ℙ³_k`.** -/
def involution : projectiveThreeSpace k ⟶ projectiveThreeSpace k :=
  Proj.map (involutionHom k) (irrelevant_le_map_involutionHom k)

/-- **The involution squares to the identity.** -/
@[reassoc (attr := simp)]
theorem involution_comp_involution : involution k ≫ involution k = 𝟙 _ := by
  rw [involution, ← Proj.map_comp, map_congr (involutionHom_comp_involutionHom k) _ (by simp),
    Proj.map_id]

/-- The involution is an isomorphism. -/
instance : IsIso (involution k) :=
  ⟨⟨involution k, involution_comp_involution k, involution_comp_involution k⟩⟩

/-- The involution on the standard chart `D₊(X i)`. -/
theorem awayι_comp_involution (i : Fin 4) :
    Proj.awayι _ (X i) (X_mem_one k i) one_pos ≫ involution k =
      Spec.map (CommRingCat.ofHom (awayMapOfEq (involutionHom k)
        (by rw [involutionHom_X, swapIndex_swapIndex] :
          involutionHom k (X (swapIndex i)) = X i))) ≫
        Proj.awayι _ (X (swapIndex i)) (X_mem_one k _) one_pos :=
  awayι_comp_map_of_eq _ _ _ _ _ _

/-- On the charts, the involution is `(a, b, c) ↦ (a, b, c)` read from `D₊(X₀)` to `D₊(X₁)`. -/
theorem ofChartP_setOneHom_involutionHom (p : MvPolynomial (Fin 4) k) :
    ofChartP k (Stacks.AlgebraicGeometry.ProjPolyChart.setOneHom k 3 0 (involutionHom k p)) =
      ofChartQ k (Stacks.AlgebraicGeometry.ProjPolyChart.setOneHom k 3 1 p) := by
  have h : ((ofChartP k).toRingHom.comp
      (Stacks.AlgebraicGeometry.ProjPolyChart.setOneHom k 3 0)).comp (involutionHom k).toRingHom =
      (ofChartQ k).toRingHom.comp (Stacks.AlgebraicGeometry.ProjPolyChart.setOneHom k 3 1) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp [involutionHom_apply, ofChartP, ofChartQ]
    · fin_cases i <;> simp [ofChartP, ofChartQ, swapIndex,
        Stacks.AlgebraicGeometry.ProjPolyChart.setOneHom]
  exact congrArg (fun φ : MvPolynomial (Fin 4) k →+* ModelRing k => φ p) h

/-- **The involution carries the chart at `P` to the chart at `Q`.** -/
theorem chartP_comp_involution : chartP k ≫ involution k = chartQ k := by
  rw [chartP, chartQ, Category.assoc, involution,
    awayι_comp_map_of_eq (involutionHom k) _ (s := X 1) (t := X 0)
      (by rw [involutionHom_X]; rfl) (X_mem_one k 1) (X_mem_one k 0) one_pos,
    ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  refine congrArg (fun φ : Away (homogeneousSubmodule (Fin 4) k) (X 1) →+* ModelRing k =>
    Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (homogeneousSubmodule (Fin 4) k) (X 1) (X_mem_one k 1) one_pos) ?_
  refine RingHom.ext fun x => ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem_one k 1) x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  rw [awayMapOfEq_mk _ _ _ (X_mem_one k 0), chartRingEquivP_symm_mk, chartRingEquivQ_symm_mk,
    ofChartP_setOneHom_involutionHom]

/-- **The involution carries the chart at `Q` to the chart at `P`.** -/
theorem chartQ_comp_involution : chartQ k ≫ involution k = chartP k := by
  rw [← chartP_comp_involution, Category.assoc, involution_comp_involution, Category.comp_id]

/-! ### The conics are exchanged -/

/-- **An ideal sheaf is determined by its pullbacks along an affine open cover.** -/
theorem idealSheafData_ext_of_comap {Z : Scheme.{u}} {I J : Z.IdealSheafData} {ι : Type*}
    {Y : ι → Scheme.{u}} [∀ i, IsAffine (Y i)] (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) (h : ∀ i, I.comap (f i) = J.comap (f i)) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun i => ⟨f i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion (f i)⟩) ?_ fun i => ?_
  · simpa only [Scheme.Hom.image_top_eq_opensRange] using hf
  · have h1 : (I.comap (f i)).ideal ⟨⊤, isAffineOpen_top _⟩ =
        (J.comap (f i)).ideal ⟨⊤, isAffineOpen_top _⟩ := by rw [h i]
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at h1
    exact Ideal.comap_injective_of_surjective (f := ((f i).appIso ⊤).inv.hom)
      (hf := ((f i).appIso ⊤).symm.commRingCatIsoToRingEquiv.surjective) h1

/-- The standard charts `D₊(X i)` cover `ℙ³`. -/
theorem iSup_opensRange_awayι :
    ⨆ i : Fin 4, (Proj.awayι (homogeneousSubmodule (Fin 4) k) (X i) (X_mem_one k i)
      one_pos).opensRange = ⊤ := by
  simp_rw [Proj.opensRange_awayι]
  exact Stacks.ProjectiveSpace.iSup_basicOpen_X_eq_top k (Fin 4)

/-- `Away.mk` only depends on the numerator. -/
theorem away_mk_congr {f : MvPolynomial (Fin 4) k} {d : ℕ}
    (hf : f ∈ homogeneousSubmodule (Fin 4) k d) (n : ℕ) {x y : MvPolynomial (Fin 4) k}
    (h : x = y) (hx) (hy) :
    Away.mk (homogeneousSubmodule (Fin 4) k) hf n x hx =
      Away.mk (homogeneousSubmodule (Fin 4) k) hf n y hy := by
  subst h
  rfl

/-- **Pulling back the ideal sheaf of a homogeneous ideal along the involution.** If the
involution carries the generators of `𝔞` to those of `𝔟`, it pulls back the ideal sheaf of `𝔞`
to that of `𝔟`. -/
theorem comap_homogeneousIdealSheaf_involution
    (𝔞 𝔟 : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    (v w : Fin 2 → MvPolynomial (Fin 4) k)
    (hv : ∀ j, v j ∈ homogeneousSubmodule (Fin 4) k (generatorDegrees j • 1))
    (hw : ∀ j, w j ∈ homogeneousSubmodule (Fin 4) k (generatorDegrees j • 1))
    (h𝔞 : 𝔞.toIdeal = Ideal.span (Set.range v)) (h𝔟 : 𝔟.toIdeal = Ideal.span (Set.range w))
    (hvw : ∀ j, involutionHom k (v j) = w j) :
    (homogeneousIdealSheaf _ 𝔞).comap (involution k) = homogeneousIdealSheaf _ 𝔟 := by
  refine idealSheafData_ext_of_comap _ (iSup_opensRange_awayι k) fun i => ?_
  rw [← Scheme.IdealSheafData.comap_comp, awayι_comp_involution,
    comap_chart_homogeneousIdealSheaf _ 𝔞 (X_mem_one k _) one_pos v generatorDegrees hv h𝔞,
    comap_awayι_homogeneousIdealSheaf _ 𝔟 (X_mem_one k i) one_pos w generatorDegrees hw h𝔟]
  refine congrArg (fun F : Fin 2 → Away (homogeneousSubmodule (Fin 4) k) (X i) =>
    specIdeal (Ideal.span (Set.range F))) (funext fun j => ?_)
  rw [awayMapOfEq_mk _ _ _ (X_mem_one k i)]
  exact away_mk_congr k _ _ (hvw j) _ _

/-- **The involution pulls `C` back to `D`.** -/
theorem comap_idealSheafC_involution : (idealSheafC k).comap (involution k) = idealSheafD k :=
  comap_homogeneousIdealSheaf_involution k (conicHomogeneousIdealC k) (conicHomogeneousIdealD k)
    (generatorsC k) (generatorsD k)
    (generatorsC_mem k) (generatorsD_mem k) (conicIdealC_eq_span_range k)
    (conicIdealD_eq_span_range k) fun j => by
      fin_cases j <;> simp [generatorsC, generatorsD, swapIndex]
      ring

/-- **The involution pulls `D` back to `C`.** -/
theorem comap_idealSheafD_involution : (idealSheafD k).comap (involution k) = idealSheafC k :=
  comap_homogeneousIdealSheaf_involution k (conicHomogeneousIdealD k) (conicHomogeneousIdealC k)
    (generatorsD k) (generatorsC k)
    (generatorsD_mem k) (generatorsC_mem k) (conicIdealD_eq_span_range k)
    (conicIdealC_eq_span_range k) fun j => by
      fin_cases j <;> simp [generatorsC, generatorsD, swapIndex]
      ring

/-! ### The involution on points -/

/-- The involution on points: the homogeneous prime of `σ x` is the preimage of that of `x`. -/
theorem involution_apply_toIdeal (x : projectiveThreeSpace k) :
    (involution k x).asHomogeneousIdeal.toIdeal =
      x.asHomogeneousIdeal.toIdeal.comap (involutionHom k) :=
  rfl

/-- The involution is an involution on points. -/
@[simp]
theorem involution_involution_apply (x : projectiveThreeSpace k) :
    involution k (involution k x) = x := by
  refine ProjectiveSpectrum.ext (HomogeneousIdeal.ext (Ideal.ext fun a => ?_))
  rw [involution_apply_toIdeal, Ideal.mem_comap, involution_apply_toIdeal, Ideal.mem_comap,
    involutionHom_involutionHom]

/-- Moving the involution across an equation of points. -/
theorem involution_apply_eq_iff (x y : projectiveThreeSpace k) :
    involution k x = y ↔ x = involution k y :=
  ⟨fun h => by rw [← h, involution_involution_apply],
    fun h => by rw [h, involution_involution_apply]⟩

/-- A point lies in `D₊(f)` after the involution iff it lies in `D₊(σ f)`. -/
theorem involution_apply_mem_basicOpen_iff (x : projectiveThreeSpace k)
    (f : MvPolynomial (Fin 4) k) :
    involution k x ∈ Proj.basicOpen _ f ↔ x ∈ Proj.basicOpen _ (involutionHom k f) :=
  Iff.rfl

/-- **The involution sends `P` to `Q`.** -/
theorem involution_pointP : involution k (pointP k) = pointQ k := by
  refine (eq_coordinatePoint_iff k 1 _).mp ?_
  rw [involution_apply_toIdeal, coordinateIdeal, Ideal.span_le]
  rintro _ ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, involutionHom_X, pointP, coordinatePoint_toIdeal]
  refine Ideal.subset_span ⟨swapIndex i, fun h => hi ?_, rfl⟩
  have h' := congrArg swapIndex h
  rw [swapIndex_swapIndex] at h'
  exact h'

/-- **The involution sends `Q` to `P`.** -/
theorem involution_pointQ : involution k (pointQ k) = pointP k := by
  rw [involution_apply_eq_iff, involution_pointP]

/-- **The involution exchanges `Y - {P}` and `Y - {Q}`.** -/
theorem involution_preimage_opensAwayQ : involution k ⁻¹ᵁ opensAwayQ k = opensAwayP k := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change involution k x ∈ ({pointQ k}ᶜ : Set _) ↔ x ∈ ({pointP k}ᶜ : Set _)
  rw [Set.mem_compl_iff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_singleton_iff,
    involution_apply_eq_iff, involution_pointQ]

/-- **The involution exchanges `Y - {Q}` and `Y - {P}`.** -/
theorem involution_preimage_opensAwayP : involution k ⁻¹ᵁ opensAwayP k = opensAwayQ k := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change involution k x ∈ ({pointP k}ᶜ : Set _) ↔ x ∈ ({pointQ k}ᶜ : Set _)
  rw [Set.mem_compl_iff, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_singleton_iff,
    involution_apply_eq_iff, involution_pointP]

/-- **The involution preserves `Y - {P, Q}`.** -/
theorem involution_preimage_opensAwayPQ : involution k ⁻¹ᵁ opensAwayPQ k = opensAwayPQ k := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change involution k x ∈ ({pointP k, pointQ k}ᶜ : Set _) ↔ x ∈ ({pointP k, pointQ k}ᶜ : Set _)
  rw [Set.mem_compl_iff, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_singleton_iff, involution_apply_eq_iff,
    involution_apply_eq_iff, involution_pointP, involution_pointQ, or_comm]

/-! ### The free locus -/

/-- The linear forms `x - y` and `z - w`, which the involution negates. -/
def freeNum : Fin 2 → MvPolynomial (Fin 4) k := ![X 0 - X 1, X 2 - X 3]

/-- The linear forms `x + y` and `z + w`, which the involution fixes. -/
def freeDen : Fin 2 → MvPolynomial (Fin 4) k := ![X 0 + X 1, X 2 + X 3]

/-- The involution negates `x - y` and `z - w`. -/
theorem involutionHom_freeNum (i : Fin 2) : involutionHom k (freeNum k i) = -freeNum k i := by
  fin_cases i <;> simp [freeNum, swapIndex]

/-- The involution fixes `x + y` and `z + w`. -/
theorem involutionHom_freeDen (j : Fin 2) : involutionHom k (freeDen k j) = freeDen k j := by
  fin_cases j <;> simp [freeDen, swapIndex] <;> ring

/-- `freeNum` is linear. -/
theorem isHomogeneous_freeNum (i : Fin 2) : (freeNum k i).IsHomogeneous 1 := by
  fin_cases i
  · exact (isHomogeneous_X k 0).sub (isHomogeneous_X k 1)
  · exact (isHomogeneous_X k 2).sub (isHomogeneous_X k 3)

/-- `freeDen` is linear. -/
theorem isHomogeneous_freeDen (j : Fin 2) : (freeDen k j).IsHomogeneous 1 := by
  fin_cases j
  · exact (isHomogeneous_X k 0).add (isHomogeneous_X k 1)
  · exact (isHomogeneous_X k 2).add (isHomogeneous_X k 3)

/-- **The free locus `Y - (L₁ ∪ L₂)`** of the involution, where `L₁ = {[a : a : b : b]}` and
`L₂ = {[a : -a : b : -b]}`: the union of the four basic opens `D₊(ℓ · m)`,
`ℓ ∈ {x - y, z - w}`, `m ∈ {x + y, z + w}`. -/
def freeLocus : (projectiveThreeSpace k).Opens :=
  ⨆ (i : Fin 2) (j : Fin 2), Proj.basicOpen _ (freeNum k i * freeDen k j)

/-- Membership in the free locus. -/
theorem mem_freeLocus_iff (x : projectiveThreeSpace k) :
    x ∈ freeLocus k ↔ ∃ i j, freeNum k i * freeDen k j ∉ x.asHomogeneousIdeal := by
  simp only [freeLocus, TopologicalSpace.Opens.mem_iSup, Proj.mem_basicOpen]

/-- **The free locus is stable under the involution.** -/
theorem involution_preimage_freeLocus : involution k ⁻¹ᵁ freeLocus k = freeLocus k := by
  refine TopologicalSpace.Opens.ext (Set.ext fun x => ?_)
  change involution k x ∈ freeLocus k ↔ x ∈ freeLocus k
  rw [mem_freeLocus_iff, mem_freeLocus_iff]
  refine exists_congr fun i => exists_congr fun j => ?_
  change involutionHom k (freeNum k i * freeDen k j) ∉ x.asHomogeneousIdeal.toIdeal ↔
    freeNum k i * freeDen k j ∉ x.asHomogeneousIdeal.toIdeal
  rw [map_mul, involutionHom_freeNum, involutionHom_freeDen, neg_mul, neg_mem_iff]

/-- A variable lies in the ideal of every other coordinate point. -/
private theorem X_mem_coordinateIdeal {i j : Fin 4} (h : i ≠ j) :
    (X i : MvPolynomial (Fin 4) k) ∈ coordinateIdeal k j :=
  Ideal.subset_span ⟨i, h, rfl⟩

/-- A variable does not lie in the ideal of its own coordinate point. -/
private theorem X_not_mem_coordinateIdeal (j : Fin 4) :
    (X j : MvPolynomial (Fin 4) k) ∉ coordinateIdeal k j :=
  fun h => (X_mem_span_X_image_iff.mp h) rfl

/-- **`P` lies in the free locus.** -/
theorem pointP_mem_freeLocus : pointP k ∈ freeLocus k := by
  refine (mem_freeLocus_iff k _).mpr ⟨0, 0, fun hmem => ?_⟩
  change (X 0 - X 1) * (X 0 + X 1) ∈ coordinateIdeal k 0 at hmem
  have h1 := X_mem_coordinateIdeal k (by decide : (1 : Fin 4) ≠ 0)
  rcases (pointP k).isPrime.mem_or_mem hmem with h | h
  · have h' := add_mem h h1
    rw [sub_add_cancel] at h'
    exact X_not_mem_coordinateIdeal k 0 h'
  · have h' := sub_mem h h1
    rw [add_sub_cancel_right] at h'
    exact X_not_mem_coordinateIdeal k 0 h'

/-- **`Q` lies in the free locus.** -/
theorem pointQ_mem_freeLocus : pointQ k ∈ freeLocus k := by
  refine (mem_freeLocus_iff k _).mpr ⟨0, 0, fun hmem => ?_⟩
  change (X 0 - X 1) * (X 0 + X 1) ∈ coordinateIdeal k 1 at hmem
  have h0 := X_mem_coordinateIdeal k (by decide : (0 : Fin 4) ≠ 1)
  rcases (pointQ k).isPrime.mem_or_mem hmem with h | h
  · have h' := sub_mem h0 h
    rw [sub_sub_cancel] at h'
    exact X_not_mem_coordinateIdeal k 1 h'
  · have h' := sub_mem h h0
    rw [add_sub_cancel_left] at h'
    exact X_not_mem_coordinateIdeal k 1 h'

/-- **The involution of the free locus.** -/
def freeInvolution : (freeLocus k).toScheme ⟶ (freeLocus k).toScheme :=
  (involution k).resLE (freeLocus k) (freeLocus k) (involution_preimage_freeLocus k).ge

/-- The involution of the free locus is the restriction of the involution of `ℙ³`. -/
@[reassoc (attr := simp)]
theorem freeInvolution_ι : freeInvolution k ≫ (freeLocus k).ι = (freeLocus k).ι ≫ involution k :=
  Scheme.Hom.resLE_comp_ι _ _

/-- **The involution of the free locus squares to the identity.** -/
@[reassoc (attr := simp)]
theorem freeInvolution_comp_freeInvolution : freeInvolution k ≫ freeInvolution k = 𝟙 _ := by
  rw [← cancel_mono (freeLocus k).ι, Category.assoc, freeInvolution_ι, freeInvolution_ι_assoc,
    involution_comp_involution, Category.comp_id, Category.id_comp]

/-! ### The involution is free on the free locus -/

/-- Two morphisms that agree have the same `appLE`. -/
theorem appLE_eq_of_eq {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (h : f = g) (U V e e') :
    f.appLE U V e = g.appLE U V e' := by
  subst h
  rfl

/-- **No point of `D₊((a b)²)` is fixed, scheme-theoretically**, for linear forms `a`, `b` with
`σ a = -a` and `σ b = b`. If `c : T ⟶ ℙ³` satisfies `c ≫ σ = c`, then `c` misses `D₊((a b)²)`:
on it the section `u = a³ b / (a b)²` is negated by the involution, and `2 u` is a unit, so the
pullback of `2 u` is both a unit and zero on the preimage. -/
theorem not_mem_basicOpen_of_comp_involution_eq_of_linear (h2 : (2 : k) ≠ 0)
    {a b : MvPolynomial (Fin 4) k} (ha : a.IsHomogeneous 1) (hb : b.IsHomogeneous 1)
    (hga : involutionHom k a = -a) (hgb : involutionHom k b = b) {T : Scheme.{u}}
    (c : T ⟶ projectiveThreeSpace k) (hc : c ≫ involution k = c) (t : T) :
    c t ∉ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) := by
  intro ht
  have hs : (a * b) ^ 2 ∈ homogeneousSubmodule (Fin 4) k 4 :=
    (mem_homogeneousSubmodule _ _).mpr ((ha.mul hb).pow 2)
  have hu : a ^ 3 * b ∈ homogeneousSubmodule (Fin 4) k (1 • 4) :=
    (mem_homogeneousSubmodule _ _).mpr ((ha.pow 3).mul hb)
  have hw : C (2⁻¹ : k) * (a * b ^ 3) ∈ homogeneousSubmodule (Fin 4) k (1 • 4) :=
    (mem_homogeneousSubmodule _ _).mpr ((ha.mul (hb.pow 3)).C_mul _)
  have hgs : involutionHom k ((a * b) ^ 2) = (a * b) ^ 2 := by
    rw [map_pow, map_mul, hga, hgb, neg_mul, neg_sq]
  -- the involution negates `u = a³ b / (a b)²`
  have hgu : awayMapOfEq (involutionHom k) hgs
      (Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (a ^ 3 * b) hu) =
        -Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (a ^ 3 * b) hu := by
    rw [awayMapOfEq_mk _ _ _ hs]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_neg, Away.val_mk, Away.val_mk, Localization.neg_mk]
    congr 1
    rw [map_mul, map_pow, hga, hgb]
    ring
  -- `2 u` is a unit, with inverse `a b³ / (2 (a b)²)`
  have h2' : (C (2⁻¹ : k) : MvPolynomial (Fin 4) k) * 2 = 1 := by
    rw [show (2 : MvPolynomial (Fin 4) k) = C 2 from (map_ofNat C 2).symm, ← C_mul,
      inv_mul_cancel₀ h2, C_1]
  have hnum : (a ^ 3 * b + a ^ 3 * b) * (C (2⁻¹ : k) * (a * b ^ 3)) =
      ((a * b) ^ 2) ^ 1 * ((a * b) ^ 2) ^ 1 := by
    linear_combination (a ^ 4 * b ^ 4) * h2'
  have hunit : (Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (a ^ 3 * b) hu +
      Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (a ^ 3 * b) hu) *
        Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (C (2⁻¹ : k) * (a * b ^ 3)) hw = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_add, Away.val_mk,
      Away.val_mk, HomogeneousLocalization.val_one, Localization.add_mk_self,
      Localization.mk_mul]
    rw [hnum]
    exact Localization.mk_self (S := Submonoid.powers ((a * b) ^ 2))
      (⟨((a * b) ^ 2) ^ 1, ⟨1, rfl⟩⟩ * ⟨((a * b) ^ 2) ^ 1, ⟨1, rfl⟩⟩)
  obtain ⟨u₀, hu₀⟩ : ∃ u : Away (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2),
      u = Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (a ^ 3 * b) hu := ⟨_, rfl⟩
  obtain ⟨w₀, hw₀⟩ : ∃ w : Away (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2),
      w = Away.mk (homogeneousSubmodule (Fin 4) k) hs 1 (C (2⁻¹ : k) * (a * b ^ 3)) hw :=
    ⟨_, rfl⟩
  rw [← hu₀] at hgu hunit
  rw [← hw₀] at hunit
  -- pull back along `c`
  have hWW : Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) ≤
      involution k ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) :=
    fun x hx => by
      change involution k x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)
      rw [involution_apply_mem_basicOpen_iff, hgs]
      exact hx
  have hsec : Proj.awayToSection (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) ≫
      (involution k).appLE _ _ hWW =
        CommRingCat.ofHom (awayMapOfEq (involutionHom k) hgs) ≫
          Proj.awayToSection (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) :=
    awayToSection_comp_appLE_of_eq (involutionHom k) (irrelevant_le_map_involutionHom k) hgs hs hWW
  have hcomp : (involution k).appLE _ _ hWW ≫
      c.appLE (Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2))
        (c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)) le_rfl =
      c.appLE (Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2))
        (c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)) le_rfl :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (appLE_eq_of_eq hc _ _ _ _)
  obtain ⟨F, hF⟩ : ∃ F : Away (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2) →+*
      Γ(T, c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)),
      F = (c.appLE (Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2))
        (c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)) le_rfl).hom.comp
        (Proj.awayToSection (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)).hom :=
    ⟨_, rfl⟩
  have key : F u₀ = -F u₀ := by
    have e1 := congrArg (fun φ => φ.hom
      ((Proj.awayToSection (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)).hom u₀)) hcomp
    have e2 := congrArg (fun φ => φ.hom u₀) hsec
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e1 e2
    rw [hF, RingHom.comp_apply]
    conv_lhs => rw [← e1, e2, hgu]
    rw [map_neg, map_neg]
  have h0 : F u₀ + F u₀ = 0 := by
    nth_rw 1 [key]
    exact neg_add_cancel _
  have : Nonempty (c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2)) :=
    ⟨⟨t, ht⟩⟩
  have h10 : (1 : Γ(T, c ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((a * b) ^ 2))) =
      0 := by
    rw [← map_one F, ← hunit, map_mul, map_add, h0, zero_mul]
  exact one_ne_zero h10

/-- **No point of `D₊((ℓ m)²)` is fixed, scheme-theoretically**, for `ℓ ∈ {x - y, z - w}` and
`m ∈ {x + y, z + w}`. -/
theorem not_mem_basicOpen_of_comp_involution_eq (h2 : (2 : k) ≠ 0) {T : Scheme.{u}}
    (c : T ⟶ projectiveThreeSpace k) (hc : c ≫ involution k = c) (i j : Fin 2) (t : T) :
    c t ∉ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) ((freeNum k i * freeDen k j) ^ 2) :=
  not_mem_basicOpen_of_comp_involution_eq_of_linear k h2 (isHomogeneous_freeNum k i)
    (isHomogeneous_freeDen k j) (involutionHom_freeNum k i) (involutionHom_freeDen k j) c hc t

/-- **The involution acts freely on the free locus, scheme-theoretically**: a morphism
`c : T ⟶ Y - (L₁ ∪ L₂)` with `c ≫ σ = c` has empty source, when `2 ≠ 0` in `k`. -/
theorem isEmpty_of_comp_freeInvolution_eq (h2 : (2 : k) ≠ 0) {T : Scheme.{u}}
    (c : T ⟶ (freeLocus k).toScheme) (hc : c ≫ freeInvolution k = c) : IsEmpty T := by
  have hc' : (c ≫ (freeLocus k).ι) ≫ involution k = c ≫ (freeLocus k).ι := by
    rw [Category.assoc, ← freeInvolution_ι, ← Category.assoc, hc]
  refine ⟨fun t => ?_⟩
  have hmem : (freeLocus k).ι (c t) ∈ Set.range (freeLocus k).ι := ⟨c t, rfl⟩
  rw [Scheme.Opens.range_ι, SetLike.mem_coe, mem_freeLocus_iff] at hmem
  obtain ⟨i, j, hij⟩ := hmem
  refine not_mem_basicOpen_of_comp_involution_eq k h2 _ hc' i j t ?_
  rw [Proj.mem_basicOpen, Scheme.Hom.comp_apply]
  exact fun h => hij (((freeLocus k).ι (c t)).isPrime.mem_of_pow_mem 2 h)

/-! ### The conics lie in the free locus and in the two charts -/

/-- No point of `ℙ³` contains all four coordinates. -/
theorem not_forall_X_mem (x : projectiveThreeSpace k) :
    ¬ ∀ i : Fin 4, (X i : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
  intro h
  obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X x
  exact (Proj.mem_basicOpen _ _ _).mp hi (h i)

/-- A point of `C` contains `xy - z²` and `w`. -/
theorem mem_of_mem_supportSet_idealSheafC {x : projectiveThreeSpace k}
    (hx : x ∈ (idealSheafC k).supportSet) :
    (X 0 * X 1 - X 2 ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal ∧
      (X 3 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [idealSheafC, mem_supportSet_homogeneousIdealSheaf_iff] at hx
  change conicIdealC k ≤ _ at hx
  rw [conicIdealC_eq_span_range, Ideal.span_le, Set.range_subset_iff] at hx
  exact ⟨hx 0, hx 1⟩

/-- A point of `D` contains `xy - w²` and `z`. -/
theorem mem_of_mem_supportSet_idealSheafD {x : projectiveThreeSpace k}
    (hx : x ∈ (idealSheafD k).supportSet) :
    (X 0 * X 1 - X 3 ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal ∧
      (X 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
  rw [idealSheafD, mem_supportSet_homogeneousIdealSheaf_iff] at hx
  change conicIdealD k ≤ _ at hx
  rw [conicIdealD_eq_span_range, Ideal.span_le, Set.range_subset_iff] at hx
  exact ⟨hx 0, hx 1⟩

/-- A point containing `xy - u²` and `v`, where `{u, v} = {z, w}`, lies in `D₊(x) ∪ D₊(y)`. -/
private theorem mem_basicOpen_X_zero_or_X_one_of_mem (x : projectiveThreeSpace k) {u v : Fin 4}
    (huv : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = u ∨ i = v)
    (hu : (X 0 * X 1 - X u ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal)
    (hv : (X v : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal) :
    x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X 0) ∨
      x ∈ Proj.basicOpen (homogeneousSubmodule (Fin 4) k) (X 1) := by
  rw [Proj.mem_basicOpen, Proj.mem_basicOpen, ← not_and_or]
  rintro ⟨h0, h1⟩
  have hu' : (X u : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have := sub_mem (Ideal.mul_mem_right (X 1) x.asHomogeneousIdeal.toIdeal h0) hu
    rwa [sub_sub_cancel] at this
  refine not_forall_X_mem k x fun i => ?_
  rcases huv i with rfl | rfl | rfl | rfl
  exacts [h0, h1, hu', hv]

/-- The two conics lie in the union `D₊(x) ∪ D₊(y)` of the two charts. -/
theorem supportSet_idealSheafC_union_supportSet_idealSheafD_subset :
    (idealSheafC k).supportSet ∪ (idealSheafD k).supportSet ⊆
      Set.range (chartP k) ∪ Set.range (chartQ k) := by
  rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, opensRange_chartP,
    opensRange_chartQ]
  rintro x (hx | hx)
  · obtain ⟨hu, hv⟩ := mem_of_mem_supportSet_idealSheafC k hx
    exact mem_basicOpen_X_zero_or_X_one_of_mem k x (u := 2) (v := 3) (by decide) hu hv
  · obtain ⟨hu, hv⟩ := mem_of_mem_supportSet_idealSheafD k hx
    exact mem_basicOpen_X_zero_or_X_one_of_mem k x (u := 3) (v := 2) (by decide) hu hv

/-- A point containing `xy - u²` and `v`, where `{u, v} = {z, w}`, lies in the free locus. -/
private theorem mem_freeLocus_of_mem (x : projectiveThreeSpace k) {u v : Fin 4}
    (huv : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = u ∨ i = v)
    (hzw : ∃ ε : MvPolynomial (Fin 4) k,
      X u ^ 2 = ε * ((X 2 - X 3) * (X 2 + X 3)) + X v * X v)
    (hu : (X 0 * X 1 - X u ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal)
    (hv : (X v : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal) : x ∈ freeLocus k := by
  rw [mem_freeLocus_iff]
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  have hu' : (X u : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    refine x.isPrime.mem_of_pow_mem 2 ?_
    have h11 : ((X 2 - X 3) * (X 2 + X 3) : MvPolynomial (Fin 4) k) ∈
        x.asHomogeneousIdeal.toIdeal := hcon 1 1
    obtain ⟨ε, hε⟩ := hzw
    rw [hε]
    exact add_mem (Ideal.mul_mem_left _ ε h11) (Ideal.mul_mem_left _ (X v) hv)
  have hxy : (X 0 * X 1 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    have h := add_mem hu (Ideal.mul_mem_left _ (X u) hu')
    rwa [← sq, sub_add_cancel] at h
  have h00 : ((X 0 - X 1) * (X 0 + X 1) : MvPolynomial (Fin 4) k) ∈
      x.asHomogeneousIdeal.toIdeal := hcon 0 0
  have hsq : (X 0 ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal ∧
      (X 1 ^ 2 : MvPolynomial (Fin 4) k) ∈ x.asHomogeneousIdeal.toIdeal := by
    have e0 : (X 0 ^ 2 : MvPolynomial (Fin 4) k) = (X 0 - X 1) * (X 0 + X 1) + X 1 * X 1 := by
      ring
    have e1 : (X 1 ^ 2 : MvPolynomial (Fin 4) k) = X 0 * X 0 - (X 0 - X 1) * (X 0 + X 1) := by
      ring
    rcases x.isPrime.mem_or_mem hxy with h | h
    · refine ⟨?_, ?_⟩
      · rw [sq]; exact Ideal.mul_mem_left _ _ h
      · rw [e1]; exact sub_mem (Ideal.mul_mem_left _ _ h) h00
    · refine ⟨?_, ?_⟩
      · rw [e0]; exact add_mem h00 (Ideal.mul_mem_left _ _ h)
      · rw [sq]; exact Ideal.mul_mem_left _ _ h
  refine not_forall_X_mem k x fun i => ?_
  rcases huv i with rfl | rfl | rfl | rfl
  exacts [x.isPrime.mem_of_pow_mem 2 hsq.1, x.isPrime.mem_of_pow_mem 2 hsq.2, hu', hv]

/-- **The conic `C` lies in the free locus**: it misses the lines `L₁` and `L₂`. -/
theorem supportSet_idealSheafC_subset_freeLocus :
    (idealSheafC k).supportSet ⊆ (freeLocus k : Set (projectiveThreeSpace k)) := fun x hx => by
  obtain ⟨hu, hv⟩ := mem_of_mem_supportSet_idealSheafC k hx
  exact mem_freeLocus_of_mem k x (u := 2) (v := 3) (by decide) ⟨1, by ring⟩ hu hv

/-- **The conic `D` lies in the free locus**: it misses the lines `L₁` and `L₂`. -/
theorem supportSet_idealSheafD_subset_freeLocus :
    (idealSheafD k).supportSet ⊆ (freeLocus k : Set (projectiveThreeSpace k)) := fun x hx => by
  obtain ⟨hu, hv⟩ := mem_of_mem_supportSet_idealSheafD k hx
  exact mem_freeLocus_of_mem k x (u := 3) (v := 2) (by decide) ⟨-1, by ring⟩ hu hv

end Stacks.Examples.HironakaInvolution

end
