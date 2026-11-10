module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullbackChart

/-!
# The formal pullback over an affine chart is the local algebraization

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a morphism of inverse systems whose levelwise
kernels and cokernels are annihilated by a power of `𝓘`.  Over a Noetherian affine étale chart
`V` with ring `A = 𝒪_F(V)` and ideal `I = 𝓘(V)`, the formal-glueing descent
`AlgebraicGeometry.Space.exists_chartCompletedComparison_descent` produces a finite `A`-module
together with a map to `G(V)` and an identification of its extension of scalars with the
completed module of the tower of sections of `E`.

**This file identifies that module with the sections of the formal pullback over `V`.**  The
identification is not a choice: `AdicCompletion.existsUnique_of_descent` says that the descended
module *is* the fibre product of `G(V)` and the completed module over the extension of scalars,
and `AlgebraicGeometry.Space.completionToLimit_eq_limMap_iff` says that the sections of the
formal pullback over `V` are that same fibre product.

## Main results

* `AlgebraicGeometry.Space.exists_formalPullback_chartEquiv` — **the sections of the formal
  pullback over a Noetherian affine chart are the descended module**, by a linear equivalence
  compatible with the identification of its extension of scalars with the completed module.
* `AlgebraicGeometry.Space.moduleFinite_formalPullback_sections` — those sections are a finite
  module over the ring of the chart.
* `AlgebraicGeometry.Space.formalPullbackLevel_app_surjective_ker` — the projection of the
  formal pullback onto level `n` of `E` is, on those sections, the reduction modulo
  `𝓘(V) ⁿ⁺¹`.
* `AlgebraicGeometry.Space.smul_eq_zero_of_formalPullbackMap_eq_zero` and
  `AlgebraicGeometry.Space.exists_formalPullbackMap_eq_smul` — the kernel of the projection to
  `G` is annihilated by `𝓘 ^ t`, and `𝓘(V) ^ t` times a section of `G` lifts, for the exponent
  `t` of the hypothesis on `α`.

## Implementation notes

The map from the descended module to the sections of the formal pullback is built by choice from
`AlgebraicGeometry.Space.exists_formalPullback_section`, and is linear because a section of the
formal pullback is determined by its two components,
`AlgebraicGeometry.Space.formalPullback_section_ext`; its bijectivity is the uniqueness clause of
`AdicCompletion.existsUnique_of_descent` in one direction and
`AlgebraicGeometry.Space.exists_formalPullback_section` in the other.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
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

/-- The two identifications of `AlgebraicGeometry.Space.chartFormalPullbackProj` and
`AlgebraicGeometry.Space.chartLimitSectionOfCompleted` are mutually inverse on the sections of
`lim E`. -/
theorem chartFormalPullbackProj_section (z : chartCompletedSections B S hS F hF 𝓘 E V) :
    haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
        (chartSectionsLimit B S hS F hF E V) :=
      isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
    Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
        (M := chartSectionsLimit B S hS F hF E V)
      ((chartLimitSectionsIso B S hS F hF E V).hom
        (chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV z)) = z := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set cL := Stacks.Coherent.completeModuleEquivAdicCompletion
    (chartSectionIdeal B S hS F hF 𝓘 V)
    (M := chartSectionsLimit B S hS F hF E V) with hcL
  have hiso : (chartLimitSectionsIso B S hS F hF E V).hom
      ((chartLimitSectionsIso B S hS F hF E V).inv (cL.symm z)) = cL.symm z :=
    congrArg (fun k : chartSectionsLimit B S hS F hF E V ⟶ chartSectionsLimit B S hS F hF E V =>
      k (cL.symm z)) (chartLimitSectionsIso B S hS F hF E V).inv_hom_id
  rw [chartLimitSectionOfCompleted, hiso, LinearEquiv.apply_symm_apply]

/-- The identification of `AlgebraicGeometry.Space.chartLimitSectionOfCompleted` undoes that of
`AlgebraicGeometry.Space.chartFormalPullbackProj` on a section of the formal pullback. -/
theorem chartLimitSectionOfCompleted_chartFormalPullbackProj
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :
    chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV
        (chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p) =
      (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set cL := Stacks.Coherent.completeModuleEquivAdicCompletion
    (chartSectionIdeal B S hS F hF 𝓘 V)
    (M := chartSectionsLimit B S hS F hF E V) with hcL
  set y := (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p with hy
  have hinv : (chartLimitSectionsIso B S hS F hF E V).inv
      ((chartLimitSectionsIso B S hS F hF E V).hom y) = y :=
    congrArg (fun k : (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        (op V)).obj (limit E) ⟶ (SheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
        (op V)).obj (limit E) => k y)
      (chartLimitSectionsIso B S hS F hF E V).hom_inv_id
  rw [chartLimitSectionOfCompleted, chartFormalPullbackProj, LinearEquiv.symm_apply_apply, hinv]

/-! ### The projections of the formal pullback onto the levels of `E` -/

/-- The projection of the formal pullback onto the term at level `n` of `E`. -/
abbrev formalPullbackLevel (n : ℕ) : formalPullback B S hS F hF 𝓘 G α ⟶ E.obj (op n) :=
  formalPullbackProj B S hS F hF 𝓘 G α ≫ limit.π E (op n)

/-- Over a Noetherian affine chart, the projection of the formal pullback onto level `n` is the
projection of the completed module, read through
`AlgebraicGeometry.Space.chartFormalPullbackProj`. -/
theorem formalPullbackLevel_app (n : ℕ)
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :
    (formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op V) p =
      chartCompletedLevel B S hS F hF 𝓘 E
        (isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV) n
        (chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  change _ = (chartSectionsLevel B S hS F hF E V n).hom
    ((Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
      (M := chartSectionsLimit B S hS F hF E V)).symm
      (Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
        (M := chartSectionsLimit B S hS F hF E V)
        ((chartLimitSectionsIso B S hS F hF E V).hom
          ((formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p))))
  rw [LinearEquiv.symm_apply_apply, comp_val_app_apply_chart]
  exact (chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF E V n _).symm

/-! ### The sections of the formal pullback are the descended module -/

include hG in
/-- **The sections of the formal pullback over a Noetherian affine chart are the descended
module.**  There are a finite `A`-module `M₀`, an `A`-linear equivalence `θ` of `M₀` with the
sections of the formal pullback over `V`, and an identification `e` of the extension of scalars
`A ^∧ ⊗_A M₀` with the completed module of the tower of sections of `E`, such that `θ` followed by
`AlgebraicGeometry.Space.chartFormalPullbackProj` is `m ↦ e (1 ⊗ m)`.

`M₀` is the descent of `AlgebraicGeometry.Space.exists_chartCompletedComparison_descent`; the map
`θ` sends `m` to the section of the formal pullback whose components are `ψ m` and `e (1 ⊗ m)`,
which exists by `AlgebraicGeometry.Space.exists_formalPullback_section` and the equation of
`AlgebraicGeometry.Space.completionToLimit_eq_limMap_iff`.  It is injective and surjective by the
uniqueness and the existence halves of `AdicCompletion.existsUnique_of_descent`. -/
theorem exists_formalPullback_chartEquiv
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α) :
    ∃ (M₀ : ModuleCat.{u} (chartRing B S hS F hF V))
      (θ : M₀ ≃ₗ[chartRing B S hS F hF V] (formalPullback B S hS F hF 𝓘 G α).val.obj (op V))
      (e : TensorProduct (chartRing B S hS F hF V)
          (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)) M₀
        ≃ₗ[AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
          chartCompletedSections B S hS F hF 𝓘 E V),
      Module.Finite (chartRing B S hS F hF V) M₀ ∧
        ∀ m : M₀, chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV (θ m) =
          e ((1 : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
            (chartRing B S hS F hF V)) ⊗ₜ m) := by
  obtain ⟨M₀, ψ, e, hfin, hK, hC, he⟩ :=
    exists_chartCompletedComparison_descent B S hS F hF 𝓘 hIcart hE G hG α hV hα
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set Â := AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)
  have hcompat : ∀ m : M₀, chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV
      (e ((1 : Â) ⊗ₜ m)) = (1 : Â) ⊗ₜ ψ m := fun m => by
    have h := LinearMap.congr_fun he ((1 : Â) ⊗ₜ m)
    simpa using h
  have hpair : ∀ m : M₀, (completionToLimit B S hS F hF 𝓘 G).val.app (op V) (ψ m) =
      (limMap α).val.app (op V)
        (chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ m))) := by
    intro m
    refine (completionToLimit_eq_limMap_iff B S hS F hF 𝓘 hIcart hE G hG α hV _ _).2 ?_
    rw [chartFormalPullbackProj_section B S hS F hF 𝓘 hIcart hE hV,
      ← ofTensorProductEquiv_chartCompletedComparisonTensor, hcompat,
      ← AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of, LinearEquiv.apply_symm_apply]
  choose θf hθa hθp using fun m : M₀ =>
    exists_formalPullback_section B S hS F hF 𝓘 G α V (ψ m) _ (hpair m)
  have hadd : ∀ m m' : M₀,
      chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ (m + m'))) =
        chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ m)) +
          chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ m')) := by
    intro m m'
    rw [TensorProduct.tmul_add, map_add]
    simp only [chartLimitSectionOfCompleted, map_add]
    rfl
  have hsmul : ∀ (r : chartRing B S hS F hF V) (m : M₀),
      chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ (r • m))) =
        r • chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV (e ((1 : Â) ⊗ₜ m)) := by
    intro r m
    rw [TensorProduct.tmul_smul, show e (r • ((1 : Â) ⊗ₜ m)) = r • e ((1 : Â) ⊗ₜ m) from
      e.toLinearMap.map_smul_of_tower r _]
    simp only [chartLimitSectionOfCompleted, map_smul]
    rfl
  let θ : M₀ →ₗ[chartRing B S hS F hF V] (formalPullback B S hS F hF 𝓘 G α).val.obj (op V) :=
    { toFun := θf
      map_add' := fun m m' => formalPullback_section_ext B S hS F hF 𝓘 G α V
        (by rw [map_add, hθa, hθa, hθa, map_add])
        (by
          rw [map_add, hθp, hθp, hθp]
          exact hadd m m')
      map_smul' := fun r m => formalPullback_section_ext B S hS F hF 𝓘 G α V
        (by rw [map_smul, hθa, hθa, map_smul]; rfl)
        (by
          rw [map_smul, hθp, hθp]
          exact hsmul r m) }
  have hθproj : ∀ m : M₀, chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV (θ m) =
      e ((1 : Â) ⊗ₜ m) := fun m => by
    change chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV (θf m) = _
    rw [chartFormalPullbackProj, hθp m]
    exact chartFormalPullbackProj_section B S hS F hF 𝓘 hIcart hE hV _
  have hinj : Function.Injective θ := by
    intro m m' hmm
    have ha : ψ m' = ψ m := by
      rw [← hθa m, ← hθa m']
      exact congrArg (fun q => (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) q) hmm.symm
    have hp : e ((1 : Â) ⊗ₜ m') = e ((1 : Â) ⊗ₜ m) := by
      rw [← hθproj m, ← hθproj m', hmm]
    obtain ⟨m₁, -, huniq⟩ := AdicCompletion.existsUnique_of_descent
      (chartSectionIdeal B S hS F hF 𝓘 V) ψ
      (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV) e he hK hC (ψ m)
      (e ((1 : Â) ⊗ₜ m)) (hcompat m)
    exact (huniq m ⟨rfl, rfl⟩).trans (huniq m' ⟨ha, hp⟩).symm
  have hsurj : Function.Surjective θ := by
    intro p
    obtain ⟨m, ⟨hma, hmp⟩, -⟩ := AdicCompletion.existsUnique_of_descent
      (chartSectionIdeal B S hS F hF 𝓘 V) ψ
      (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV) e he hK hC
      ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p)
      (chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p)
      (chartCompletedComparisonTensor_chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G hG α hV p)
    refine ⟨m, formalPullback_section_ext B S hS F hF 𝓘 G α V ?_ ?_⟩
    · exact (hθa m).trans hma
    · change (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) (θf m) = _
      rw [hθp m, hmp]
      exact chartLimitSectionOfCompleted_chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p
  exact ⟨M₀, LinearEquiv.ofBijective θ ⟨hinj, hsurj⟩, e, hfin, hθproj⟩

include hIcart hE hG hV in
/-- **The sections of the formal pullback over a Noetherian affine chart are a finite module.** -/
theorem moduleFinite_formalPullback_sections
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α) :
    Module.Finite (chartRing B S hS F hF V) ((formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :=
  by
  obtain ⟨M₀, θ, e, hfin, -⟩ :=
    exists_formalPullback_chartEquiv B S hS F hF 𝓘 hIcart hE G hG α hV hα
  exact Module.Finite.equiv θ

include hIcart hE hG hV in
/-- **The projection of the formal pullback onto level `n` is, on the sections over a Noetherian
affine chart, the reduction modulo `𝓘(V) ^ (n + 1)`**: it is surjective, with kernel
`𝓘(V) ^ (n + 1)` times the sections of the formal pullback.

Through the descended module `M₀` of `AlgebraicGeometry.Space.exists_formalPullback_chartEquiv`
the projection is the canonical map `M₀ → M₀ ^∧` followed by an identification of `M₀ ^∧` with
the completed module and the projection of the completed module onto level `n`, whose kernel is
`𝓘(V) ^ (n + 1)` times the completed module; and the canonical map into the completion followed
by the evaluation at `n + 1` is the reduction modulo `𝓘(V) ^ (n + 1)`. -/
theorem formalPullbackLevel_app_surjective_ker
    (hα : IsSystemKernelCokernelAnnihilatedByPower B S hS F hF 𝓘 α) (n : ℕ) :
    Function.Surjective ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op V)).hom ∧
      LinearMap.ker ((formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op V)).hom =
        chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
          (⊤ : Submodule (chartRing B S hS F hF V)
            ((formalPullback B S hS F hF 𝓘 G α).val.obj (op V))) := by
  obtain ⟨M₀, θ, e, hfin, hθ⟩ :=
    exists_formalPullback_chartEquiv B S hS F hF 𝓘 hIcart hE G hG α hV hα
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set I := chartSectionIdeal B S hS F hF 𝓘 V with hI
  let ε : AdicCompletion I M₀ ≃ₗ[chartRing B S hS F hF V]
      chartCompletedSections B S hS F hF 𝓘 E V :=
    ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀).symm.trans e).restrictScalars
      (chartRing B S hS F hF V)
  let Φ := chartCompletedLevel B S hS F hF 𝓘 E hcomplete n ∘ₗ ε.toLinearMap
  have hΦker : LinearMap.ker Φ = I ^ (n + 1) • (⊤ : Submodule _ (AdicCompletion I M₀)) :=
    Stacks.Coherent.ker_comp_linearEquiv_pow_smul_top _ _ _
      (ker_chartCompletedLevel B S hS F hF 𝓘 hE hIcart hV hcomplete n)
  have hΦsurj : Function.Surjective Φ :=
    (surjective_chartCompletedLevel B S hS F hF 𝓘 hE hV.1 hcomplete n).comp ε.surjective
  have hcomp : ∀ m : M₀, (formalPullbackLevel B S hS F hF 𝓘 G α n).val.app (op V) (θ m) =
      Φ (AdicCompletion.of I M₀ m) := by
    intro m
    rw [formalPullbackLevel_app B S hS F hF 𝓘 hIcart hE G α hV n, hθ m]
    change _ = chartCompletedLevel B S hS F hF 𝓘 E hcomplete n
      (e ((AdicCompletion.ofTensorProductEquivOfFiniteNoetherian I M₀).symm
        (AdicCompletion.of I M₀ m)))
    rw [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian_symm_of]
  have hker_eval : LinearMap.ker (AdicCompletion.eval I M₀ (n + 1)) =
      I ^ (n + 1) • (⊤ : Submodule _ (AdicCompletion I M₀)) :=
    (AdicCompletion.pow_smul_top_eq_ker_eval (Ideal.fg_of_isNoetherianRing I)).symm
  have hker0 : ∀ m : M₀, Φ (AdicCompletion.of I M₀ m) = 0 ↔
      m ∈ I ^ (n + 1) • (⊤ : Submodule (chartRing B S hS F hF V) M₀) := by
    intro m
    rw [← LinearMap.mem_ker, hΦker, ← hker_eval, LinearMap.mem_ker, AdicCompletion.eval_of,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hsurj0 : ∀ y, ∃ m : M₀, Φ (AdicCompletion.of I M₀ m) = y := by
    intro y
    obtain ⟨x, rfl⟩ := hΦsurj y
    obtain ⟨m, hm⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval I M₀ (n + 1) x)
    refine ⟨m, ?_⟩
    rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, hΦker, ← hker_eval, LinearMap.mem_ker,
      map_sub, AdicCompletion.eval_of, hm, sub_self]
  have hmap : Submodule.map (θ : M₀ →ₗ[chartRing B S hS F hF V] _)
      (I ^ (n + 1) • (⊤ : Submodule (chartRing B S hS F hF V) M₀)) =
        I ^ (n + 1) • (⊤ : Submodule (chartRing B S hS F hF V)
          ((formalPullback B S hS F hF 𝓘 G α).val.obj (op V))) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := hsurj0 y
    exact ⟨θ m, (hcomp m).trans hm⟩
  · ext q
    obtain ⟨m, rfl⟩ := θ.surjective q
    rw [LinearMap.mem_ker, ← hmap, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
      ← hker0, ← hcomp]
    rfl

/-! ### The kernel and the cokernel of the projection to `G` -/

omit hIcart hE in
/-- **`𝓘 ^ t` annihilates the kernel of the projection of the formal pullback to `G`**, over every
étale chart, when `𝓘 ^ t` annihilates the levelwise kernels of `α`.

A section of the formal pullback with vanishing first component has second component a section
of `lim E` killed by `lim α`; its components lie in the sections of the levelwise kernels of
`α`, which `𝓘 ^ t` annihilates. -/
theorem smul_eq_zero_of_formalPullbackMap_eq_zero {t : ℕ}
    (ht : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (kernel (α.app (op k))) = ⊥)
    (W : SmallEtale B S hS F) (r : chartRing B S hS F hF W)
    (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 W ^ t)
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op W))
    (hp : (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op W) p = 0) :
    r • p = 0 := by
  have hsm : ∀ {X Y : Modules.{u, u} B S hS F hF} (f : X ⟶ Y) (x : X.val.obj (op W)),
      f.val.app (op W) (r • x) = r • f.val.app (op W) x :=
    fun f x => (f.val.app (op W)).hom.map_smul r x
  have hz : ∀ {X Y : Modules.{u, u} B S hS F hF} (f : X ⟶ Y),
      f.val.app (op W) 0 = 0 := fun f => (f.val.app (op W)).hom.map_zero
  set y := (formalPullbackProj B S hS F hF 𝓘 G α).val.app (op W) p with hy
  have h1 : (completionToLimit B S hS F hF 𝓘 G).val.app (op W)
      ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op W) p) =
        (limMap α).val.app (op W) y :=
    congrArg (fun k : formalPullback B S hS F hF 𝓘 G α ⟶
      limit (adicQuotientSystem B S hS F hF 𝓘 G) => k.val.app (op W) p)
      (formalPullback_comm B S hS F hF 𝓘 G α)
  have hlim : (limMap α).val.app (op W) y = 0 := by
    rw [← h1, hp, hz]
  have key : ∀ n : ℕ, r • (limit.π E (op n)).val.app (op W) y = 0 := by
    intro n
    have h0 : (α.app (op n)).val.app (op W) ((limit.π E (op n)).val.app (op W) y) = 0 := by
      have h2 : (limit.π (adicQuotientSystem B S hS F hF 𝓘 G) (op n)).val.app (op W)
          ((limMap α).val.app (op W) y) =
          (α.app (op n)).val.app (op W) ((limit.π E (op n)).val.app (op W) y) :=
        congrArg (fun k : (limit E : Modules.{u, u} B S hS F hF) ⟶
          (adicQuotientSystem B S hS F hF 𝓘 G).obj (op n) => k.val.app (op W) y)
          (limMap_π α (op n))
      rw [← h2, hlim, hz]
    obtain ⟨w, hw⟩ := (SheafOfModules.exact_kernel_ι_val_app (α.app (op n)) (op W) _).1 h0
    have hwz : r • w = 0 :=
      (idealPowerMultiple_eq_bot_iff B S hS F hF 𝓘 t (kernel (α.app (op n)))).1 (ht n) W r hr w
    rw [← hw, ← hsm, hwz, hz]
  have hry : r • y = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (chartLimitSectionsIso B S hS F hF E W).hom).1
    refine Limits.Concrete.limit_ext _ _ _ fun j => ?_
    have e1 := chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF E W j.unop (r • y)
    have e2 := chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF E W j.unop 0
    refine e1.trans (Eq.trans ?_ e2.symm)
    rw [hsm, key, hz]
  exact formalPullback_section_ext B S hS F hF 𝓘 G α W
    (by rw [hsm, hp, smul_zero, hz]) (by rw [hsm, ← hy, hry, hz])

include hIcart hE hG hV in
/-- **`𝓘(V) ^ t` times a section of `G` over a Noetherian affine chart lifts to the formal
pullback**, when `𝓘 ^ t` annihilates the levelwise cokernels of `α`: the image of the
multiple in the adic completion of `G(V)` is in the image of the comparison map,
`AlgebraicGeometry.Space.smul_mem_range_chartCompletedComparison`, and that is the equation
defining the sections of the formal pullback. -/
theorem exists_formalPullbackMap_eq_smul {t : ℕ}
    (htc : ∀ k : ℕ, idealPowerMultiple B S hS F hF 𝓘 t (cokernel (α.app (op k))) = ⊥)
    (r : chartRing B S hS F hF V) (hr : r ∈ chartSectionIdeal B S hS F hF 𝓘 V ^ t)
    (g : G.val.obj (op V)) :
    ∃ p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V),
      (formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p = r • g := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  obtain ⟨z, hz⟩ := smul_mem_range_chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV
    htc r hr (AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) g)
  obtain ⟨p, hp, -⟩ := exists_formalPullback_section B S hS F hF 𝓘 G α V (r • g)
    (chartLimitSectionOfCompleted B S hS F hF 𝓘 hIcart hE hV z)
    ((completionToLimit_eq_limMap_iff B S hS F hF 𝓘 hIcart hE G hG α hV _ _).2 (by
      rw [chartFormalPullbackProj_section B S hS F hF 𝓘 hIcart hE hV z, map_smul]
      exact hz))
  exact ⟨p, hp⟩

end AlgebraicGeometry.Space

end
