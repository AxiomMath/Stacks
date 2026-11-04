module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.ModuleTower
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAffineChartCokernelSections
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.RingTheory.AdicCompletion.FiniteModuleDescent

/-!
# The kernel and the cokernel of the chart comparison map are ideal-power torsion

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a morphism of inverse systems whose levelwise
kernels and cokernels are annihilated by one power `𝓘 ^ t` of `𝓘`.  Over a Noetherian affine
étale chart `V` with ring `A = 𝒪_F(V)`, ideal `I = 𝓘(V)` and completed ring `S = A ^∧`, this
file proves that the kernel of the comparison map
`AlgebraicGeometry.Space.chartCompletedComparison` is annihilated by `I ^ t`.

This is the translation of the hypothesis of Stacks 0888 into the hypothesis of the
formal-glueing descent `AdicCompletion.exists_finite_descent_of_isIPowerTorsion`, and it is the
step of the proof of Stacks 0889 which is not a transport.  The condition of Stacks 0888 is
*levelwise*, so it says that `I ^ t` kills the kernel of each map on sections
`E_n(V) ⟶ (G / 𝓘 ⁿ⁺¹ G)(V)`.  The projections of the completed module onto those sections are
surjective with kernel `I ⁿ⁺¹` times it, so `I ^ t` times the kernel of the comparison map lies
in every `I ⁿ⁺¹` times the completed module; the completed module is an adic completion, hence
`I`-adically Hausdorff, so that intersection vanishes.

## Main results

* `AlgebraicGeometry.Space.smul_eq_zero_of_chartCompletedComparisonLinear_eq_zero` — **an element
  of `I ^ t` annihilates every element of the kernel of the comparison map.**
* `AlgebraicGeometry.Space.isIPowerTorsion_ker_chartCompletedComparison` — the kernel of the
  comparison map is `I S`-power torsion, in the form the descent theorem asks for.

## Implementation notes

The exponent is the one supplied by
`AlgebraicGeometry.Space.IsSystemKernelCokernelAnnihilatedByPower`, and it is *uniform in the
level*; that is what makes the intersection argument work, and it is why the source states its
hypothesis with a single exponent for all levels at once.

Annihilation of the levelwise kernel is read on sections through
`AlgebraicGeometry.Space.idealPowerMultiple_eq_bot_iff`, whose right-hand side
`AlgebraicGeometry.Space.IsPowAnnihilated` is a condition on the sections over *every* chart, and
through `SheafOfModules.exact_kernel_ι_val_app`, which identifies the sections of a kernel with
the kernel of the map on sections.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 05E6](https://stacks.math.columbia.edu/tag/05E6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)
    (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (hE : IsCoherentAdicSystem B S hS F hF 𝓘 E)
    (G : Modules.{u, u} B S hS F hF) (hG : IsCoherent B S hS F hF G)
    (α : E ⟶ adicQuotientSystem B S hS F hF 𝓘 G)
    {V : SmallEtale B S hS F} (hV : IsNoetherianAffineChart B S hS F V)

/-! ### The kernel -/

/-- If `I ^ t` kills `m`, then so does the `t`-th power of the extension of `I` to an algebra. -/
private theorem smul_eq_zero_of_mem_map_pow {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    {I : Ideal R} {t : ℕ} {m : M} (h : ∀ r ∈ I ^ t, r • m = 0) {a : A}
    (ha : a ∈ Ideal.map (algebraMap R A) I ^ t) : a • m = 0 := by
  rw [← Ideal.map_pow] at ha
  refine (Ideal.map_le_iff_le_comap (K := LinearMap.ker (LinearMap.toSpanSingleton A M m))).mpr
    (fun r hr => ?_) ha
  change algebraMap R A r • m = 0
  rw [algebraMap_smul]
  exact h r hr

/-- **An element of `𝓘(V) ^ t` annihilates the kernel of the comparison map**, when `𝓘 ^ t`
annihilates the levelwise kernels of `α`.

The projection of the completed module onto the sections at level `n` of an element of the kernel
lands in the sections of the levelwise kernel of `α`, which `𝓘 ^ t` annihilates; so the multiple
lies in the kernel of every projection, that is in `𝓘(V) ⁿ⁺¹` times the completed module, and the
completed module is Hausdorff. -/
theorem smul_eq_zero_of_chartCompletedComparisonLinear_eq_zero {t : ℕ}
    (ht : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.app (op k))) = ⊥)
    (r : chartRing B S hS F hF V) (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ t)
    (y : chartCompletedSections B S hS F hF 𝓘 E V)
    (hy : chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV y = 0) :
    r • y = 0 := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  have hhaus : IsHausdorff (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartCompletedSections B S hS F hF 𝓘 E V) := inferInstance
  refine hhaus.haus (r • y) fun n => ?_
  rw [SModEq.zero]
  match n with
  | 0 => simp
  | k + 1 =>
    rw [← ker_chartCompletedLevel B S hS F hF 𝓘 hE hIcart hV hcomplete k, LinearMap.mem_ker,
      map_smul]
    have h0 : (α.app (op k)).val.app (op V)
        (chartCompletedLevel B S hS F hF 𝓘 E hcomplete k y) = 0 := by
      have h1 := eval_chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV k y
      rw [hy, map_zero] at h1
      exact (LinearEquiv.map_eq_zero_iff _).mp h1.symm
    obtain ⟨w, hw⟩ :=
      (SheafOfModules.exact_kernel_ι_val_app (α.app (op k)) (op V) _).1 h0
    have hwz : r • w = 0 :=
      (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 t (kernel (α.app (op k)))).1 (ht k) V r hr w
    have hsm : (kernel.ι (α.app (op k))).val.app (op V) (r • w) =
        r • (kernel.ι (α.app (op k))).val.app (op V) w :=
      ((kernel.ι (α.app (op k))).val.app (op V)).hom.map_smul r w
    rw [← hw]
    refine hsm.symm.trans ?_
    refine (congrArg
      (fun z : (kernel (α.app (op k))).val.obj (op V) =>
        (kernel.ι (α.app (op k))).val.app (op V) z) hwz).trans ?_
    exact ((kernel.ι (α.app (op k))).val.app (op V)).hom.map_zero

/-- **The kernel of the comparison map is `I A ^∧`-power torsion**, in the form the formal-glueing
descent `AdicCompletion.exists_finite_descent_of_isIPowerTorsion` asks for.

The exponent is the one annihilating the levelwise kernels of `α`; it is uniform, so a single
power of the ideal of the completed ring annihilates the whole kernel.  An element of the
extended ideal is a sum of multiples of images of elements of `𝓘(V) ^ t`, each of which
annihilates the kernel by
`AlgebraicGeometry.Space.smul_eq_zero_of_chartCompletedComparisonLinear_eq_zero`. -/
theorem isIPowerTorsion_ker_chartCompletedComparison {t : ℕ} (ht0 : 0 < t)
    (ht : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.app (op k))) = ⊥) :
    IsIPowerTorsion
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (LinearMap.ker (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV))
      (Ideal.map (algebraMap (chartRing B S hS F hF V)
          (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)))
        (chartSectionIdeal B S hS F hF 𝓘 V)) := by
  intro y
  refine ⟨t, ht0, fun a ha => ?_⟩
  have hy : chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
      (y : chartCompletedSections B S hS F hF 𝓘 E V) = 0 :=
    (chartCompletedComparison_apply B S hS F hF 𝓘 hIcart hE G hG α hV _).symm.trans
      (LinearMap.mem_ker.mp y.2)
  exact Submodule.coe_eq_zero.mp ((Submodule.coe_smul a y).trans
    (smul_eq_zero_of_mem_map_pow (fun r hrmem =>
      smul_eq_zero_of_chartCompletedComparisonLinear_eq_zero B S hS F hF 𝓘 hIcart hE G hG α hV
        ht r hrmem _ hy) ha))

/-! ### The cokernel -/

/-- **An element of `𝓘(V) ^ t` times an element of the adic completion of `G(V)` is in the image
of the comparison map modulo any power of `𝓘(V)`**, when `𝓘 ^ t` annihilates the levelwise
cokernels of `α`.

At level `k` the element is, after multiplication by `r`, in the image of the map on sections of
`α` — that is exactly annihilation of the levelwise cokernel, read on sections by
`AlgebraicGeometry.Space.ker_val_app_cokernel_π_of_cartesian` — and the projection of the
completed module onto the sections at level `k` is surjective, so a preimage there has the right
image modulo `𝓘(V) ᵏ⁺¹`. -/
theorem exists_sub_chartCompletedComparisonLinear_mem {t : ℕ}
    (htc : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥)
    (r : chartRing B S hS F hF V) (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ t)
    (z : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))) (k : ℕ) :
    ∃ y : chartCompletedSections B S hS F hF 𝓘 E V,
      r • z - chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV y ∈
        chartSectionIdeal B S hS F hF 𝓘 V ^ (k + 1) •
          (⊤ : Submodule (chartRing B S hS F hF V)
            (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)))) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  set Gcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
    hG.toIsQuasicoherentOnSite with hGcart
  set e := chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart G Gcart hV.1 k with he
  set ζ : ((adicQuotientSystem B S hS F hF 𝓘 G).obj (op k)).val.obj (op V) :=
    e (AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) (k + 1) z)
    with hζ
  have hcok : r • ((cokernel.π (α.app (op k))).val.app (op V) ζ) = 0 :=
    (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 t (cokernel (α.app (op k)))).1 (htc k) V r hr _
  have hsm : (cokernel.π (α.app (op k))).val.app (op V) (r • ζ) =
      r • ((cokernel.π (α.app (op k))).val.app (op V) ζ) :=
    ((cokernel.π (α.app (op k))).val.app (op V)).hom.map_smul r ζ
  have hmem : r • ζ ∈ LinearMap.range ((α.app (op k)).val.app (op V)).hom := by
    rw [← ker_val_app_cokernel_π_of_cartesian B S hS F hF (α.app (op k))
      (isCartesianOnAffineCharts_of_isCoherentAdicSystem B S hS F hF 𝓘 hE k)
      (isCartesianOnAffineCharts_idealPowerQuotient B S hS F hF 𝓘 hIcart G Gcart (k + 1))
      hV.1]
    exact LinearMap.mem_ker.mpr (hsm.trans hcok)
  obtain ⟨w, hw⟩ := hmem
  obtain ⟨y, hy⟩ := surjective_chartCompletedLevel B S hS F hF 𝓘 hE hV.1 hcomplete k w
  refine ⟨y, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing _), LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  have hzr : AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) (k + 1)
      (r • z) = r • AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V)
        (G.val.obj (op V)) (k + 1) z :=
    map_smul _ r z
  have hφ := eval_chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV k y
  have hlin : r • ζ = e (r • AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V)
      (G.val.obj (op V)) (k + 1) z) := by
    rw [hζ]
    exact (map_smul e r _).symm
  rw [hzr, hφ, hy, hw, hlin, LinearEquiv.symm_apply_apply]

/-- **An element of `𝓘(V) ^ t` annihilates the cokernel of the comparison map**, when `𝓘 ^ t`
annihilates the levelwise cokernels of `α`.

A multiple `r • z` is, by
`AlgebraicGeometry.Space.exists_sub_chartCompletedComparisonLinear_mem`, in the image modulo
every power of `𝓘(V)`; the cokernel is a finite module over the completed ring, hence
`𝓘(V)`-adically complete and in particular Hausdorff, so the class vanishes.  The exponent is the
uniform one of the hypothesis, which is what the global algebraization needs. -/
theorem smul_eq_zero_cokernel_chartCompletedComparison {t : ℕ}
    (htc : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥)
    (r : chartRing B S hS F hF V) (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ t)
    (q : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) ⧸
        LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) :
    r • q = 0 := by
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  have : Module.Finite
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))) :=
    Module.Finite.equiv (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
      (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)))
  have : Module.Finite
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) ⧸
        LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) :=
    Module.Finite.quotient _ _
  have : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) ⧸
        LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) :=
    Stacks.Coherent.finiteCompletionModule_isAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (Ideal.fg_of_isNoetherianRing _) _
  have hhaus : IsHausdorff (chartSectionIdeal B S hS F hF 𝓘 V)
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) ⧸
        LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) :=
    inferInstance
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
    (LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) q
  refine hhaus.haus _ fun n => ?_
  rw [SModEq.zero]
  match n with
  | 0 => simp
  | k + 1 =>
    obtain ⟨y, hy⟩ := exists_sub_chartCompletedComparisonLinear_mem B S hS F hF 𝓘 hIcart hE
      G hG α hV htc r hr z k
    have hker : (Submodule.mkQ
        (LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)))
        (chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV y) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        ⟨y, chartCompletedComparison_apply B S hS F hF 𝓘 hIcart hE G hG α hV y⟩
    have himg := Submodule.mem_map_of_mem
      (f := LinearMap.restrictScalars (chartRing B S hS F hF V) (Submodule.mkQ
        (LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)))) hy
    rw [Submodule.map_smul'', Submodule.map_top] at himg
    have hle := smul_le_smul_left (chartSectionIdeal B S hS F hF 𝓘 V ^ (k + 1))
      (show LinearMap.range (LinearMap.restrictScalars (chartRing B S hS F hF V)
        (Submodule.mkQ (LinearMap.range
          (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)))) ≤ ⊤ from le_top)
      himg
    have heq : (Submodule.mkQ
          (LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)))
          (r • z) =
        (Submodule.mkQ
          (LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)))
          (r • z - chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV y) := by
      rw [map_sub, hker, sub_zero]
    rw [show r • Submodule.Quotient.mk (p := LinearMap.range
        (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV)) z =
        Submodule.mkQ _ (r • z) from rfl, heq]
    exact hle

/-- **An element of `𝓘(V) ^ t` times an element of the adic completion of `G(V)` lies in the
image of the comparison map**, when `𝓘 ^ t` annihilates the levelwise cokernels of `α`. -/
theorem smul_mem_range_chartCompletedComparison {t : ℕ}
    (htc : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥)
    (r : chartRing B S hS F hF V) (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ t)
    (z : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))) :
    r • z ∈ LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV) :=
  (Submodule.Quotient.mk_eq_zero _).1
    (smul_eq_zero_cokernel_chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV htc r hr
      (Submodule.Quotient.mk z))

/-- **The cokernel of the comparison map is `I A ^∧`-power torsion**, in the form the
formal-glueing descent `AdicCompletion.exists_finite_descent_of_isIPowerTorsion` asks for.

An element of `𝓘(V) ^ t` times a class in the cokernel is, by
`AlgebraicGeometry.Space.exists_sub_chartCompletedComparisonLinear_mem`, in every power of
`𝓘(V)` times the cokernel; the cokernel is a finite module over the completed ring, hence
`𝓘(V)`-adically complete and in particular Hausdorff, so that class vanishes. -/
theorem isIPowerTorsion_cokernel_chartCompletedComparison {t : ℕ} (ht0 : 0 < t)
    (htc : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥) :
    IsIPowerTorsion
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) ⧸
        LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV))
      (Ideal.map (algebraMap (chartRing B S hS F hF V)
          (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)))
        (chartSectionIdeal B S hS F hF 𝓘 V)) := by
  intro q
  refine ⟨t, ht0, fun a ha => ?_⟩
  exact smul_eq_zero_of_mem_map_pow (fun r hr =>
    smul_eq_zero_cokernel_chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV htc r hr q)
    ha

/-! ### The descent of the comparison map -/

/-- **The formal-glueing descent of the comparison map over a Noetherian affine chart.**

Let `α : E ⟶ G^∧` be a morphism of inverse systems whose levelwise kernels and cokernels are
annihilated by a power of `𝓘`.  Over a Noetherian affine chart `V` with ring `A`, ideal
`I = 𝓘(V)` and completed ring `A ^∧`, the comparison map
`AlgebraicGeometry.Space.chartCompletedComparisonTensor` descends: there are a finite `A`-module
`M₀`, a map `ψ : M₀ ⟶ G(V)` whose kernel and cokernel are `I`-power torsion, and an isomorphism
`A ^∧ ⊗_A M₀ ≅ (lim_n E_n(V)) ^∧` identifying the comparison map with the base change of `ψ`.

This is `AdicCompletion.exists_finite_descent_of_isIPowerTorsion`, whose two hypotheses are
`AlgebraicGeometry.Space.isIPowerTorsion_ker_chartCompletedComparison` and
`AlgebraicGeometry.Space.isIPowerTorsion_cokernel_chartCompletedComparison` transported from the
adic completion of `G(V)` to the extension of scalars along
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
theorem exists_chartCompletedComparison_descent
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α) :
    ∃ (M₀ : ModuleCat.{u} (chartRing B S hS F hF V))
      (ψ : M₀ →ₗ[chartRing B S hS F hF V] G.val.obj (op V))
      (e : TensorProduct (chartRing B S hS F hF V)
          (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)) M₀
        ≃ₗ[AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
          chartCompletedSections B S hS F hF 𝓘 E V),
      Module.Finite (chartRing B S hS F hF V) M₀ ∧
        IsIPowerTorsion (chartRing B S hS F hF V) (LinearMap.ker ψ)
          (chartSectionIdeal B S hS F hF 𝓘 V) ∧
        IsIPowerTorsion (chartRing B S hS F hF V)
          (G.val.obj (op V) ⧸ LinearMap.range ψ) (chartSectionIdeal B S hS F hF 𝓘 V) ∧
        (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV).comp e.toLinearMap =
          LinearMap.baseChange
            (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)) ψ := by
  obtain ⟨t, ht0, hkc⟩ := hα
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  have : Module.Finite
      (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
      (chartCompletedSections B S hS F hF 𝓘 E V) :=
    moduleFinite_chartCompletedSections B S hS F hF 𝓘 hE hIcart hV
  set eq := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
    (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) with heq
  have hcomp : (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV) =
      eq.toLinearMap.comp
        (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV) := by
    refine LinearMap.ext fun x => ?_
    exact ((chartCompletedComparison_apply B S hS F hF 𝓘 hIcart hE G hG α hV x).trans
      (ofTensorProductEquiv_chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG
        α hV x).symm)
  have hker : LinearMap.ker (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV) =
      LinearMap.ker (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV) := by
    rw [hcomp]
    exact (LinearMap.ker_comp_of_ker_eq_bot _ eq.ker).symm
  have hrange : Submodule.map eq.toLinearMap
      (LinearMap.range (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV)) =
      LinearMap.range (chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV) := by
    rw [hcomp, LinearMap.range_comp]
  refine AdicCompletion.exists_finite_descent_of_isIPowerTorsion.{u, u}
    (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))
    (ModuleCat.of _ (chartCompletedSections B S hS F hF 𝓘 E V))
    (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV) ?_ ?_
  · exact Stacks.AdicCompletion.FiniteModule.isIPowerTorsion_of_linearEquiv _
      (LinearEquiv.ofEq _ _ hker).symm
      (isIPowerTorsion_ker_chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV ht0
        (fun k => (hkc k).1))
  · exact Stacks.AdicCompletion.FiniteModule.isIPowerTorsion_of_linearEquiv _
      (Submodule.Quotient.equiv _ _ eq hrange).symm
      (isIPowerTorsion_cokernel_chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV ht0
        (fun k => (hkc k).2))

end AlgebraicGeometry.Space

end
