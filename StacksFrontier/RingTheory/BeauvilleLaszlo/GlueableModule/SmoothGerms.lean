module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Geometry.Manifold.Sheaf.LocallyRingedSpace
public import Mathlib.Geometry.Manifold.Sheaf.Smooth
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Module.PerfectSpace
public import Mathlib.Topology.Perfect

/-!
# Glueable modules: smooth germs at the origin

This file collects the analytic input for the non-glueable example of Stacks 0BNY, whose ring
is the ring of germs at `0` of smooth functions on `ℝ`, realized as Mathlib's stalk of the
sheaf of smooth functions on `ℝ`.

## Main results

* Hadamard's lemma: a smooth function `F` on a star-convex open set around `x` satisfies
  `F y = F x + ∑ᵢ (y - x)ᵢ • Hᵢ y` with smooth `Hᵢ`, obtained by differentiating under an
  interval integral.
* `smoothRingSheaf`, `smoothRingStalk`: the sheaf of smooth real functions on `ℝ` and its
  stalk at `0`.
* `regular_germ_of_punctured_nonzero`: the germ of a smooth function that vanishes nowhere
  except possibly at `0` is a non-zero-divisor.
* `smooth_section_division_at_zero`: Hadamard's lemma for sections, i.e. `g - g 0` is divisible
  by the coordinate near `0`.

## References

* [Stacks Project, Tag 0BNY](https://stacks.math.columbia.edu/tag/0BNY)
-/

@[expose] public section

namespace BeauvilleLaszlo

section

noncomputable section

open Filter Topology CategoryTheory Opposite
open scoped Manifold ContDiff Topology


end

end

section

noncomputable section

open scoped Manifold ContDiff
open Opposite Topology CategoryTheory Filter TopologicalSpace



universe u

open ContDiff

open scoped Interval

variable {E F : Type u} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedSpace ℝ E] [NormedSpace ℝ F]

private lemma ContinuousOn.intervalIntegral {X : Type*} [TopologicalSpace X] {μ :
  MeasureTheory.Measure ℝ}
    [MeasureTheory.NullSingletonClass μ] [MeasureTheory.IsLocallyFiniteMeasure μ] {f : X × ℝ → E} {u
      : Set X}
    {a₀ b₀ : ℝ} (hf : ContinuousOn f (u ×ˢ [[a₀, b₀]])) :
    ContinuousOn (fun x ↦ ∫ t in a₀..b₀, f (x, t) ∂μ) u := by
  wlog hab : a₀ ≤ b₀ with h
  · simp_rw [intervalIntegral.integral_symm b₀ a₀]
    exact (h (Set.uIcc_comm a₀ b₀ ▸ hf) (le_of_not_ge hab)).neg
  · rw [Set.uIcc_of_le hab] at hf
    rw [continuousOn_iff_continuous_restrict] at hf ⊢
    replace hf :
        Continuous (Function.uncurry fun (x : u) (t : ℝ) ↦ f (x, Set.projIcc _ _ hab t)) :=
      (hf.comp (f := (Homeomorph.Set.prod u _).symm ∘ Prod.map id (Set.projIcc _ _ hab))
        (by fun_prop)).congr fun (x, t) ↦ by simp
    refine (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf a₀ b₀).congr
      fun x ↦ intervalIntegral.integral_congr fun t ht ↦ ?_
    simp [Set.projIcc_of_mem hab <| Set.uIcc_of_le hab ▸ ht]

/-- The partial derivative in the first variable of a function differentiable on an open-by-set
product is the restriction of its derivative along the inclusion `x ↦ (x, t)`. -/
private theorem fderiv_curry_left_eq_comp_inl {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G] {f : H × ℝ → G} {u : Set H}
    {s : Set ℝ} (hu : IsOpen u) (hf : DifferentiableOn ℝ f (u ×ˢ s)) {x : H} {t : ℝ} (hx : x ∈ u)
    (ht : t ∈ s) :
    fderiv ℝ (fun y ↦ f (y, t)) x = (fderivWithin ℝ f (u ×ˢ s) (x, t)).comp (.inl ℝ H ℝ) := by
  rw [show (fun y ↦ f (y, t)) = (f ∘ fun y ↦ (y, t)) by rfl]
  rw [← fderivWithin_eq_fderiv (s := u) (hu.uniqueDiffWithinAt hx) <| by
    refine DifferentiableOn.differentiableAt (s := u) ?_ (hu.mem_nhds hx)
    exact (hf.comp (by fun_prop) (fun y hy ↦ ⟨hy, ht⟩))]
  rw [fderivWithin_comp _ (t := u ×ˢ s) (hf _ ⟨hx, ht⟩)
    (by fun_prop) (by exact fun y hy ↦ ⟨hy, ht⟩) (hu.uniqueDiffWithinAt hx)]
  congr
  exact (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffWithinAt hx)

open TopologicalSpace MeasureTheory Filter Topology Interval Set in
/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f : H × ℝ → E` is continuously differentiable on `u ×ˢ [[a, b]]` for a neighbourhood `u`
of `x₀`, then a derivative of `fun x => ∫ t in a..b, f (x, t) ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ`. -/
private nonrec theorem intervalIntegral.hasFDerivAt_integral_of_contDiffOn
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF : ContDiffOn ℝ 1 f (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t) ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ) x₀ := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h (μ := μ) hu (Set.uIcc_comm a b ▸ hF) hab).neg
    · simp [hab, hasFDerivAt_const]
  rw [uIcc_of_le hab.le] at hF
  replace ⟨u, hu, hxu, hF⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContDiffOn ℝ 1 f (u ×ˢ Icc a b) := by
    have ⟨u', hu'⟩ := mem_nhds_iff.1 hu
    exact ⟨u', hu'.2.1, hu'.2.2, hF.mono <| prod_mono_left hu'.1⟩
  let F' := fun x : H × ℝ ↦ fderiv ℝ (fun y ↦ f (y, x.2)) x.1
  have hF' : ContinuousOn F' (u ×ˢ Icc a b) := by
    refine .congr (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ Set.Icc a b) x).comp (.inl ℝ H ℝ))
      ?_ fun x hx ↦ ?_
    · refine ((ContinuousLinearMap.compL ℝ H (H × ℝ) E).flip
        (.inl ℝ H ℝ)).continuous.comp_continuousOn ?_
      refine (hF.continuousOn_fderivWithin ?_ le_rfl)
      exact hu.uniqueDiffOn.prod <| uniqueDiffOn_Icc hab
    · exact fderiv_curry_left_eq_comp_inl hu (hF.differentiableOn one_ne_zero) hx.1 hx.2
  let F'' := fun x ↦ ‖F' x‖
  have hF'' : ContinuousOn F'' _ := continuous_norm.comp_continuousOn hF'
  let ⟨ε, hε, hε', B, hB⟩ :
      ∃ ε > 0, Metric.ball x₀ ε ⊆ u ∧ ∃ B, ∀ x ∈ Metric.ball x₀ ε ×ˢ Icc a b, F'' x < B := by
    let ⟨B, hB⟩ := (isCompact_singleton.prod isCompact_Icc).bddAbove_image <|
      hF''.mono <| prod_mono_left <| singleton_subset_iff.2 hxu
    have ⟨v, hv, hv'⟩ := generalized_tube_lemma_left (s := {x₀}) isCompact_singleton
      (t := Icc a b) isCompact_Icc (s' := u) (n := F'' ⁻¹' (Iio (B + 1))) (by
        refine nhdsSetWithin_mono_left ?_ <| hF''.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
          (t := Iic B) (u := Iio (B + 1)) <| isOpen_Iio.mem_nhdsSet.2 (by simp)
        intro x hx
        exact ⟨prod_mono_left (by simp [hxu]) hx, mem_upperBounds.1 hB _ <| mem_image_of_mem _ hx⟩)
    rw [nhdsSetWithin_singleton, hu.nhdsWithin_eq hxu] at hv
    have ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hv (hu.mem_nhds hxu))
    exact ⟨ε, hε, hε'.trans inter_subset_right, B + 1,
      fun x hx ↦ hv' <| prod_mono_left (hε'.trans inter_subset_left) hx⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ B)
    (F' := fun x t ↦ fderiv ℝ (fun x ↦ f (x, t)) x) (Metric.ball_mem_nhds _ hε) ?_ ?_ ?_ ?_ ?_ ?_
  · refine eventually_nhds_iff.2 ⟨u, fun x hx ↦ ?_, hu, hxu⟩
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hx, ht⟩
  · apply ContinuousOn.intervalIntegrable
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hxu, uIcc_of_le hab.le ▸ ht⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF'.comp (f := fun t ↦ (x₀, t)) (by fun_prop) fun t ht ↦ ⟨hxu, ht⟩
  · refine .of_forall fun t ht x hx ↦ ?_
    exact (hB (x, t) ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩).le
  · exact intervalIntegrable_const
  · refine .of_forall fun t ht x hx ↦ ?_
    refine (DifferentiableOn.differentiableAt ?_ (hu.mem_nhds <| hε' hx)).hasFDerivAt
    exact hF.differentiableOn_one.comp (by fun_prop) fun x hx ↦
      ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩

private lemma ContDiffOn.intervalIntegral {μ : MeasureTheory.Measure ℝ}
    [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.NullSingletonClass μ]
    {f : E × ℝ → F} {u : Set E} (hu : IsOpen u) {a b : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (u ×ˢ [[a, b]])) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, f (x, t) ∂μ) u := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h hu (Set.uIcc_comm a b ▸ hf) hab).neg
    · simp [hab, contDiffOn_const]
  revert F; show ∀ F : _, _
  refine ENat.nat_induction n ?_ ?_ ?_
  · intro F _ _ f
    simp_rw [WithTop.coe_zero, contDiffOn_zero]
    exact ContinuousOn.intervalIntegral
  · intro k h F _ _ f hf
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := k) hu).2 ⟨?_, by simp, ?_⟩
    · intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      exact h.differentiableAt.differentiableWithinAt
    · have := hf.fderivWithin (hu.uniqueDiffOn.prod <| Set.uIcc_of_le hab.le ▸ uniqueDiffOn_Icc hab)
        (m := k) le_rfl
      refine (h _ (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ [[a, b]]) x).comp (.inl ℝ E ℝ))
        (by fun_prop)).congr ?_
      intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      rw [h.fderiv]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      exact fderiv_curry_left_eq_comp_inl hu (hf.differentiableOn (by simp)) hx ht
  · intro h F _ _ f hf
    exact contDiffOn_infty.2 fun n ↦ h n F <| hf.of_le <| WithTop.coe_le_coe.2 le_top

/-- The function appearing in Hadamard's lemma applied to the function `f` at `x` for a basis
vector `b`. -/
private noncomputable def hadamardFun (f : E → F) (x b : E) : E → F :=
    fun y ↦ ∫ t in (0 : ℝ)..1, lineDeriv ℝ f (x + t • (y - x)) b

private protected lemma ContDiffOn.hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex
  ℝ x s)
    {f : E → F} {n m : ℕ∞} (hf : ContDiffOn ℝ n f s) (hm : m + 1 ≤ n) (b : E) :
    ContDiffOn ℝ m (hadamardFun f x b) s := by
  unfold hadamardFun
  refine ContDiffOn.intervalIntegral (f := fun y ↦ lineDeriv ℝ f (x + y.2 • (y.1 - x)) b) hs ?_
  rw [Set.uIcc_of_le zero_le_one]
  refine .congr ?_ (fun y hy ↦ DifferentiableAt.lineDeriv_eq_fderiv <| (hf.differentiableOn <|
    by simp [(show n ≠ 0 by positivity [le_of_add_le_right hm])]).differentiableAt <|
      hs.mem_nhds <| hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2)
  refine .mono ?_ (s := (fun y : E × ℝ ↦ x + y.2 • (y.1 - x)) ⁻¹' s)
    fun y hy ↦ hs'.add_smul_sub_mem hy.1 hy.2.1 hy.2.2
  exact (ContinuousLinearMap.apply ℝ F b).contDiff.comp_contDiffOn <|
    (hf.fderiv_of_isOpen hs <| WithTop.coe_le_coe.2 hm).comp (by fun_prop) <| s.mapsTo_preimage _

private protected lemma ContDiff.hadamardFun {f : E → F} {n m : ℕ∞} (hf : ContDiff ℝ n f)
    (hm : m + 1 ≤ n) (x b : E) : ContDiff ℝ m (hadamardFun f x b) :=
  contDiffOn_univ.1 <| ContDiffOn.hadamardFun isOpen_univ (starConvex_univ x) (contDiffOn_univ.2 hf)
    hm b

variable [CompleteSpace F]

open _root_.intervalIntegral in
private lemma eqOn_add_sum_hadamardFun {x : E} {s : Set E} (hs : IsOpen s) (hs' : StarConvex ℝ x s)
    {f : E → F} {n : WithTop ℕ∞} (hf : ContDiffOn ℝ n f s) (hn : 1 ≤ n)
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    s.EqOn f (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  have hn' : n ≠ 0 := (one_pos.trans_le hn).ne'
  intro y hy
  have hs'' : ∀ t ∈ Set.uIcc (0 : ℝ) 1, x + t • (y - x) ∈ s := fun t ht ↦ by
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact hs'.add_smul_sub_mem hy ht.1 ht.2
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ f (x + t • (y - x)) := fun t ht ↦
    (hf.differentiableOn hn').differentiableAt <| hs.mem_nhds <| hs'' _ ht
  refine sub_eq_iff_eq_add'.1 <| Eq.trans (by simp) <| (integral_deriv_eq_sub
    (a := 0) (b := 1) (f := f ∘ fun t ↦ x + t • (y - x)) ?_ ?_).symm.trans ?_
  · intro t ht
    have := hd t ht
    fun_prop
  · refine ContinuousOn.intervalIntegrable ?_
    exact ((hf.comp (by fun_prop) <| s.mapsTo_preimage _).continuousOn_deriv_of_isOpen
      (hs.preimage <| by fun_prop) hn).mono fun t ht ↦ hs'' _ ht
  · unfold hadamardFun
    simp_rw [← integral_smul]
    rw [← integral_finset_sum]
    · refine integral_congr fun t ht ↦ ?_
      rw [← fderiv_apply_one_eq_deriv, fderiv_comp]
      · simp_rw [DifferentiableAt.lineDeriv_eq_fderiv (hd t ht)]
        simp_rw [← ContinuousLinearMap.map_smul, ← map_sum]
        simp [deriv_smul_const, - map_sub]
      · exact hd t ht
      · simp
    · intro i _
      refine (continuousOn_const.smul ?_).intervalIntegrable
      refine .congr ?_ (fun t ht ↦ DifferentiableAt.lineDeriv_eq_fderiv (hd t ht))
      refine .mono ?_  (s := (fun t ↦ x + t • (y - x)) ⁻¹' s) fun t ht ↦ hs'' _ ht
      exact (ContinuousLinearMap.apply ℝ F _).continuous.comp_continuousOn <|
        (hf.continuousOn_fderiv_of_isOpen hs hn).comp (by fun_prop) <| s.mapsTo_preimage _

private lemma eq_add_sum_hadamardFun {x : E} {f : E → F} {n : WithTop ℕ∞} (hf : ContDiff ℝ n f)
    (hn : 1 ≤ n) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E) :
    f = (fun y ↦ f x + ∑ i : ι, b.repr (y - x) i • hadamardFun f x (b i) y) := by
  simpa using eqOn_add_sum_hadamardFun isOpen_univ (starConvex_univ x) hf.contDiffOn hn b

private theorem smooth_hadamard_real (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ∀ x, f x = f 0 + x * g x := by
  let g := hadamardFun f 0 1
  refine ⟨g, ?_, ?_⟩
  · exact ContDiff.hadamardFun (f := f) hf (by simp) 0 1
  · intro x
    have h := congrFun (eq_add_sum_hadamardFun (x := 0) hf (by simp)
      (Module.Basis.singleton Unit ℝ)) x
    simpa [g, Module.Basis.singleton_repr, Module.Basis.singleton_apply,
      Finset.sum_const_zero] using h

private theorem continuous_zero_of_punctured_zero {U : Set ℝ} (hU : IsOpen U)
    (g : U → ℝ) (hg : Continuous g)
    (hz : ∀ x : U, x.1 ≠ 0 → g x = 0) : ∀ x : U, g x = 0 := by
  intro x
  by_cases hx : x.1 = 0
  · let z : U := ⟨0, hx ▸ x.2⟩
    have hcl : (0 : ℝ) ∈ closure (U \ {0}) := by
      exact mem_closure_iff_clusterPt.mpr
        (accPt_principal_iff_clusterPt.mp (hU.preperfect 0 z.2))
    have hzcl : z ∈ closure {y : U | y.1 ≠ 0} := by
      rw [closure_subtype]
      have himg : Subtype.val '' {y : U | y.1 ≠ 0} = U \ {0} := by
        ext y
        simp [Set.mem_image, and_comm]
      simpa only [himg] using hcl
    have hzz : g z = 0 :=
      (hg.continuousAt.continuousWithinAt).eq_const_of_mem_closure hzcl
        (by intro y hy; exact hz y hy)
    have hxz : x = z := Subtype.ext (by simpa [z] using hx)
    exact hxz ▸ hzz
  · exact hz x hx



abbrev smoothRingSheaf := smoothSheafCommRing (modelWithCornersSelf ℝ ℝ)
  (modelWithCornersSelf ℝ ℝ) ℝ ℝ
abbrev smoothRingStalk := smoothRingSheaf.presheaf.stalk (0 : ℝ)

theorem regular_germ_of_punctured_nonzero
    (h : smoothRingSheaf.presheaf.obj (op ⊤))
    (h_ne : ∀ x : ℝ, x ≠ 0 → h ⟨x, Set.mem_univ x⟩ ≠ 0) :
    IsRegular (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h) := by
  have hzero : ∀ g : smoothRingStalk, smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h * g = 0 →
    g = 0 := by
    intro g hg
    obtain ⟨U, h0U, g0, rfl⟩ := smoothRingSheaf.presheaf.exists_germ_eq g
    let hU : smoothRingSheaf.presheaf.obj (op U) := smoothRingSheaf.presheaf.map (homOfLE le_top).op
      h
    have hh : smoothRingSheaf.presheaf.germ U 0 h0U hU = smoothRingSheaf.presheaf.germ ⊤ 0
      (Set.mem_univ 0) h := by
      exact smoothRingSheaf.presheaf.germ_res_apply (homOfLE le_top) 0 h0U h
    have hmul : smoothRingSheaf.presheaf.germ U 0 h0U (hU * g0) = 0 := by
      rw [map_mul, hh]
      exact hg
    have hmul' : smoothRingSheaf.presheaf.germ U 0 h0U (hU * g0) =
        smoothRingSheaf.presheaf.germ U 0 h0U (0 : smoothRingSheaf.presheaf.obj (op U)) := by
      simpa using hmul
    obtain ⟨W, h0W, i1, i2, heq⟩ := smoothRingSheaf.presheaf.germ_eq 0 h0U h0U _ _ hmul'
    have hWmul : smoothRingSheaf.presheaf.map i1.op (hU * g0) = 0 := by
      simpa using heq
    let gW : smoothRingSheaf.presheaf.obj (op W) := smoothRingSheaf.presheaf.map i1.op g0
    have hz : ∀ x : W, x.1 ≠ 0 → gW x = 0 := by
      intro x hx
      have hpoint := congrArg (fun s : smoothRingSheaf.presheaf.obj (op W) => s x) hWmul
      change (smoothRingSheaf.presheaf.map i1.op hU) x * gW x = 0 at hpoint
      have hhx : (smoothRingSheaf.presheaf.map i1.op hU) x ≠ 0 := by
        show h ⟨x.1, Set.mem_univ x.1⟩ ≠ 0
        exact h_ne x.1 hx
      exact (mul_eq_zero.mp hpoint).resolve_left hhx
    have hgW : gW = 0 := by
      apply ContMDiffMap.ext
      exact continuous_zero_of_punctured_zero W.2 gW (smoothSheaf.contMDiff_section gW).continuous
        hz
    have h0g : smoothRingSheaf.presheaf.germ U 0 h0U g0 = 0 := by
      rw [← smoothRingSheaf.presheaf.germ_res_apply i1 0 h0W g0]
      simp [gW, hgW]
    exact h0g
  have hleft : IsLeftRegular (smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h) := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    calc
      smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h * (a - b) =
          smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h * a -
            smoothRingSheaf.presheaf.germ ⊤ 0 (Set.mem_univ 0) h * b := mul_sub _ _ _
      _ = 0 := sub_eq_zero.mpr hab
  refine ⟨hleft, ?_⟩
  intro a b hab
  apply hleft
  simpa only [mul_comm] using hab

private theorem smooth_section_contDiffOn (U : Opens ℝ)
    (g : smoothRingSheaf.presheaf.obj (op U)) :
    ∃ F : ℝ → ℝ, ContDiffOn ℝ ∞ F U ∧ ∀ x : U, F x.1 = g x := by
  classical
  let F : ℝ → ℝ := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  refine ⟨F, ?_, by intro x; simp [F]⟩
  apply (U.2.contDiffOn_iff (f := F)).2
  intro x hx
  have hrestr : ContMDiffAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ ℝ) ∞ (fun z : U => F z.1) ⟨x, hx⟩ := by
    convert (smoothSheaf.contMDiff_section g).contMDiffAt (x := ⟨x, hx⟩) using 1
    funext y
    simp [F]
  exact contMDiffAt_iff_contDiffAt.mp (contMDiffAt_subtype_iff.mp hrestr)

private theorem section_of_contDiffOn (W : Opens ℝ) (F : ℝ → ℝ)
    (hF : ContDiffOn ℝ ∞ F W) :
    ∃ q : smoothRingSheaf.presheaf.obj (op W), ∀ x : W, q x = F x.1 := by
  have hmap : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
      ∞ (fun x : W => F x.1) := by
    intro x
    apply contMDiffAt_subtype_iff.mpr
    exact (hF.contDiffAt (W.2.mem_nhds x.2)).contMDiffAt
  exact ⟨⟨fun x => F x.1, hmap⟩, by intro x; rfl⟩

theorem smooth_section_division_at_zero (U : Opens ℝ) (h0U : (0 : ℝ) ∈ U)
    (g : smoothRingSheaf.presheaf.obj (op U)) :
    ∃ (W : Opens ℝ) (h0W : (0 : ℝ) ∈ W) (hWU : W ≤ U)
      (q : smoothRingSheaf.presheaf.obj (op W)),
      ∀ x : W, g ⟨x.1, hWU x.2⟩ = g ⟨0, h0U⟩ + x.1 * q x := by
  obtain ⟨F, hFU, hFg⟩ := smooth_section_contDiffOn U g
  obtain ⟨r, hr, hballU⟩ := Metric.isOpen_iff.mp U.2 0 h0U
  let W : Opens ℝ := ⟨Metric.ball 0 r, Metric.isOpen_ball⟩
  have h0W : (0 : ℝ) ∈ W := Metric.mem_ball_self hr
  have hstar : StarConvex ℝ 0 (W : Set ℝ) :=
    (convex_ball 0 r).starConvex h0W
  have hFW : ContDiffOn ℝ ∞ F W := hFU.mono hballU
  have hH : ContDiffOn ℝ ∞ (hadamardFun F 0 1) W :=
    ContDiffOn.hadamardFun W.2 hstar hFW (by simp) 1
  obtain ⟨q, hq⟩ := section_of_contDiffOn W (hadamardFun F 0 1) hH
  refine ⟨W, h0W, hballU, q, ?_⟩
  intro x
  have heq := eqOn_add_sum_hadamardFun W.2 hstar hFW (by simp)
    (Module.Basis.singleton Unit ℝ) x.2
  have hfx : F x.1 = g ⟨x.1, hballU x.2⟩ :=
    hFg ⟨x.1, hballU x.2⟩
  have hf0 : F 0 = g ⟨0, h0U⟩ := hFg ⟨0, h0U⟩
  rw [← hfx, ← hf0, hq]
  simpa [Module.Basis.singleton_repr, Module.Basis.singleton_apply,
    Finset.sum_const_zero] using heq

end

end

end BeauvilleLaszlo

end
