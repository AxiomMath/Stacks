module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicAffineQuotientSections
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFormalPullback
public import StacksFrontier.RingTheory.AdicCompletion.CategoricalLimit

/-!
# The completion of a module along `𝓘`, read on an affine chart

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, and let `M` be an `𝒪_F`-module which is cartesian
on affine charts.  Over an *affine* étale chart `V` with ring `A = 𝒪_F(V)` and ideal
`I = 𝓘(V)`, the sections of the completion `M^∧ = (M / 𝓘 ⁿ⁺¹ M)_n` of `M` form the tower of adic
quotients of `A`-modules `n ↦ M(V) / I ⁿ⁺¹ M(V)`, and therefore the sections over `V` of the
inverse limit `lim_n M / 𝓘 ⁿ⁺¹ M` are the `I`-adic completion of `M(V)`.

This file proves that, and records the compatibility of the identification with the canonical map
`M ⟶ lim_n M / 𝓘 ⁿ⁺¹ M`.

## Main definitions

* `AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv` — over an affine chart, the sections of
  `M / 𝓘 ⁿ⁺¹ M` are the adic quotient `M(V) / I ⁿ⁺¹ M(V)`.
* `AlgebraicGeometry.Space.chartCompletionLimitEquiv` — **the sections over an affine chart of the
  limit of the completion are the `I`-adic completion of the sections**, as a linear equivalence
  `AdicCompletion I (M(V)) ≃ₗ[A] lim_n (M / 𝓘 ⁿ⁺¹ M)(V)`.

## Main results

* `AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv_mk` — the level identification is the
  quotient projection, read on a section of `M`.
* `AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv_naturality` — it intertwines the transition
  maps of the completion with the projections `Submodule.factorPow` of the tower of adic
  quotients.
* `AlgebraicGeometry.Space.chartSectionsLevel_chartCompletionLimitEquiv` and
  `AlgebraicGeometry.Space.chartSectionsLevel_chartCompletionLimitEquiv_of` — the components of
  the identification, on a general element of the completion and on the image of a section of
  `M`.

## Implementation notes

The identification is `AdicCompletion.quotientSystemLimitEquiv`, which takes the inverse system
abstractly together with the level identifications and their compatibility, so no isomorphism of
functors has to be transported.  Its two inputs are
`AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π`: over an affine chart the projection
onto `M / 𝓘 ⁿ⁺¹ M` is surjective on sections with kernel `I ⁿ⁺¹ M(V)`.  Both of those need only
that `𝓘` and `M` are cartesian on affine charts, so neither coherence nor local Noetherianity
appears below.

The tower is zero-indexed, as `AlgebraicGeometry.Space.IsCoherentAdicSystem` is, so its term at
`n` is the quotient at level `n + 1`; that is exactly the shifted indexing
`AdicCompletion.quotientSystemLimitEquiv` is stated for.

## References

* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 05GG](https://stacks.math.columbia.edu/tag/05GG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- Equal morphisms of `𝒪_F`-modules agree on sections over every chart. -/
private theorem val_app_apply_congr {X Y : Modules.{u, u} B S hS F hF} {f g : X ⟶ Y}
    (h : f = g) (V : SmallEtale B S hS F) (x : X.val.obj (op V)) :
    f.val.app (op V) x = g.val.app (op V) x :=
  h ▸ rfl

/-! ### The levels of the completion over an affine chart -/

variable (hIcart : IsCartesianOnAffineCharts 𝓘.toSheafOfModules)
    (M : Modules.{u, u} B S hS F hF) (hMcart : IsCartesianOnAffineCharts M)

/-- **Over an affine chart the sections of `M / 𝓘 ⁿ⁺¹ M` are the adic quotient
`M(V) / I ⁿ⁺¹ M(V)`.**

The projection onto `M / 𝓘 ⁿ⁺¹ M` is surjective on the sections over an affine chart with kernel
`I ⁿ⁺¹ M(V)`, by `AlgebraicGeometry.Space.surjective_val_app_idealPowerQuotient_π` and
`AlgebraicGeometry.Space.ker_val_app_idealPowerQuotient_π`. -/
def chartAdicQuotientLevelEquiv {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V))
    (n : ℕ) :
    (M.val.obj (op V) ⧸ chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
        (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))) ≃ₗ[
      chartRing B S hS F hF V]
      (chartSectionsSystem B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V).obj (op n) :=
  (Submodule.quotEquivOfEq _ _
      (ker_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart (n + 1) hV).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (surjective_val_app_idealPowerQuotient_π B S hS F hF 𝓘 hIcart M hMcart (n + 1) hV))

/-- The level identification of `AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv` sends the
class of a section of `M` to its image under the quotient projection. -/
theorem chartAdicQuotientLevelEquiv_mk {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V))
    (n : ℕ) (x : M.val.obj (op V)) :
    chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart M hMcart hV n
        (Submodule.Quotient.mk x) =
      (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M).ι).val.app (op V) x :=
  rfl

/-- The level identification intertwines the transition maps of the completion with the
projections of the tower of adic quotients. -/
theorem chartAdicQuotientLevelEquiv_naturality {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) {m n : ℕ} (h : m ≤ n)
    (x : M.val.obj (op V) ⧸ chartSectionIdeal B S hS F hF 𝓘 V ^ (n + 1) •
      (⊤ : Submodule (chartRing B S hS F hF V) (M.val.obj (op V)))) :
    (chartSectionsSystem B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V).map
        (homOfLE h).op (chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart M hMcart hV n x) =
      chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart M hMcart hV m
        (Submodule.factorPow (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V))
          (Nat.add_le_add_right h 1) x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x₀ =>
    exact val_app_apply_congr B S hS F hF
      (π_comp_idealPowerQuotientMapOfLE B S hS F hF 𝓘 (Nat.add_le_add_right h 1) M) V x₀

/-! ### The limit of the completion over an affine chart -/

/-- **Over an affine chart the sections of `lim_n M / 𝓘 ⁿ⁺¹ M` are the `I`-adic completion of the
sections of `M`.**

This is `AdicCompletion.quotientSystemLimitEquiv` applied to the tower of sections of the
completion, whose level identifications are
`AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv` and whose compatibility is
`AlgebraicGeometry.Space.chartAdicQuotientLevelEquiv_naturality`. -/
def chartCompletionLimitEquiv {V : SmallEtale B S hS F} (hV : IsAffine (chartScheme V)) :
    AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V)) ≃ₗ[
        chartRing B S hS F hF V]
      chartSectionsLimit B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V :=
  AdicCompletion.quotientSystemLimitEquiv _ _ _
    (chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart M hMcart hV)
    (fun h x => chartAdicQuotientLevelEquiv_naturality B S hS F hF 𝓘 hIcart M hMcart hV h x)

/-- The components of `AlgebraicGeometry.Space.chartCompletionLimitEquiv`: projecting to level `n`
recovers the evaluation of the completion at level `n + 1`. -/
theorem chartSectionsLevel_chartCompletionLimitEquiv {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) (n : ℕ)
    (x : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V))) :
    chartSectionsLevel B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V n
        (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart M hMcart hV x) =
      chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart M hMcart hV n
        (AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V)) (n + 1) x) :=
  AdicCompletion.limit_π_quotientSystemLimitEquiv _ _ _ _ _ n x

/-- `AlgebraicGeometry.Space.chartCompletionLimitEquiv` on the image of a section of `M`: its
level-`n` component is the image of that section under the projection onto `M / 𝓘 ⁿ⁺¹ M`. -/
theorem chartSectionsLevel_chartCompletionLimitEquiv_of {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) (n : ℕ) (x : M.val.obj (op V)) :
    chartSectionsLevel B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V n
        (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart M hMcart hV
          (AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V)) x)) =
      (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M).ι).val.app (op V) x := by
  rw [chartSectionsLevel_chartCompletionLimitEquiv, AdicCompletion.eval_of]
  exact chartAdicQuotientLevelEquiv_mk B S hS F hF 𝓘 hIcart M hMcart hV n x

/-! ### The sections of a limit of `𝒪_F`-modules -/

/-- **The sections of an inverse limit of `𝒪_F`-modules over a chart are the inverse limit of the
sections.**  Evaluation at a chart preserves limits. -/
def chartLimitSectionsIso (D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF) (V : SmallEtale B S hS F) :
    (SheafOfModules.evaluation
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          (op V)).obj (limit D) ≅
      chartSectionsLimit B S hS F hF D V :=
  preservesLimitIso
    (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op V)) D

/-- The identification of the sections of a limit with the limit of the sections is compatible
with the projections. -/
theorem chartLimitSectionsIso_hom_chartSectionsLevel (D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (n : ℕ) :
    (chartLimitSectionsIso B S hS F hF D V).hom ≫ chartSectionsLevel B S hS F hF D V n =
      (limit.π D (op n)).val.app (op V) :=
  preservesLimitIso_hom_π
    (SheafOfModules.evaluation
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) (op V)) D
    (op n)

/-- The projections of the limit of the sections, read through the identification with the
sections of the limit. -/
theorem chartSectionsLevel_chartLimitSectionsIso_hom (D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF)
    (V : SmallEtale B S hS F) (n : ℕ)
    (x : (limit D : Modules.{u, u} B S hS F hF).val.obj (op V)) :
    chartSectionsLevel B S hS F hF D V n ((chartLimitSectionsIso B S hS F hF D V).hom x) =
      (limit.π D (op n)).val.app (op V) x :=
  congrArg
    (fun k : (SheafOfModules.evaluation
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))
          (op V)).obj (limit D) ⟶ (chartSectionsSystem B S hS F hF D V).obj (op n) => k x)
    (chartLimitSectionsIso_hom_chartSectionsLevel B S hS F hF D V n)

/-- The identification of the sections of a limit with the limit of the sections is natural in
the inverse system. -/
theorem chartLimitSectionsIso_hom_chartSectionsLimitMap
    {D D' : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (τ : D ⟶ D') (V : SmallEtale B S hS F)
    (x : (limit D : Modules.{u, u} B S hS F hF).val.obj (op V)) :
    chartSectionsLimitMap B S hS F hF τ V ((chartLimitSectionsIso B S hS F hF D V).hom x) =
      (chartLimitSectionsIso B S hS F hF D' V).hom ((limMap τ).val.app (op V) x) := by
  refine Limits.Concrete.limit_ext _ _ _ fun j => ?_
  have hl : chartSectionsLevel B S hS F hF D' V j.unop
      (chartSectionsLimitMap B S hS F hF τ V ((chartLimitSectionsIso B S hS F hF D V).hom x)) =
      (chartSectionsSystemMap B S hS F hF τ V).app (op j.unop)
        (chartSectionsLevel B S hS F hF D V j.unop
          ((chartLimitSectionsIso B S hS F hF D V).hom x)) :=
    congrArg
      (fun k : chartSectionsLimit B S hS F hF D V ⟶ (chartSectionsSystem B S hS F hF D' V).obj
          (op j.unop) => k ((chartLimitSectionsIso B S hS F hF D V).hom x))
      (chartSectionsLimitMap_chartSectionsLevel B S hS F hF τ V j.unop)
  have hr : (limit.π D' (op j.unop)).val.app (op V) ((limMap τ).val.app (op V) x) =
      (τ.app (op j.unop)).val.app (op V) ((limit.π D (op j.unop)).val.app (op V) x) :=
    val_app_apply_congr B S hS F hF (limMap_π τ (op j.unop)) V x
  have h2 := chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF D V j.unop x
  have h3 := chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF D' V j.unop
    ((limMap τ).val.app (op V) x)
  exact hl.trans ((congrArg
    (fun z : (chartSectionsSystem B S hS F hF D V).obj (op j.unop) =>
      (chartSectionsSystemMap B S hS F hF τ V).app (op j.unop) z) h2).trans
    (hr.symm.trans h3.symm))

/-! ### The canonical map into the limit, over an affine chart -/

/-- **The canonical map `M ⟶ lim_n M / 𝓘 ⁿ⁺¹ M`, read over an affine chart, is the completion map
of the sections.** -/
theorem chartLimitSectionsIso_completionToLimit {V : SmallEtale B S hS F}
    (hV : IsAffine (chartScheme V)) (x : M.val.obj (op V)) :
    (chartLimitSectionsIso B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V).hom
        ((completionToLimit B S hS F hF 𝓘 M).val.app (op V) x) =
      chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart M hMcart hV
        (AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (M.val.obj (op V)) x) := by
  have hcomp : ∀ n : ℕ,
      chartSectionsLevel B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V n
          ((chartLimitSectionsIso B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 M) V).hom
            ((completionToLimit B S hS F hF 𝓘 M).val.app (op V) x)) =
        (cokernel.π (idealPowerMultiple B S hS F hF 𝓘 (n + 1) M).ι).val.app (op V) x := by
    intro n
    refine (chartSectionsLevel_chartLimitSectionsIso_hom B S hS F hF
      (adicQuotientSystem B S hS F hF 𝓘 M) V n _).trans ?_
    exact val_app_apply_congr B S hS F hF (completionToLimit_π B S hS F hF 𝓘 M (op n)) V x
  refine Limits.Concrete.limit_ext _ _ _ fun j => ?_
  refine (hcomp j.unop).trans ?_
  exact (chartSectionsLevel_chartCompletionLimitEquiv_of B S hS F hF 𝓘 hIcart M hMcart hV
    j.unop x).symm

end AlgebraicGeometry.Space

end
