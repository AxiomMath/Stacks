module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionChartTorsion

/-!
# The formal pullback over an affine chart is the fibre product of the descent datum

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a morphism of inverse systems.  Over a
Noetherian affine étale chart `V` with ring `A = 𝒪_F(V)` and ideal `I = 𝓘(V)`, the sections of
the formal pullback `AlgebraicGeometry.Space.formalPullback` are pairs consisting of a section of
`G` and a section of `lim E` which agree in `lim G / 𝓘 ⁿ⁺¹ G`.  This file translates that
agreement into the equation the formal-glueing descent of
`AlgebraicGeometry.Space.chartCompletedComparison` is stated with: the second component, read in
the completed module `(lim_n E_n(V)) ^∧`, is sent by the comparison map to the image of the first
component in the adic completion of `G(V)`.

That is exactly the statement `φ y = 1 ⊗ g` whose solutions
`AdicCompletion.existsUnique_of_descent` counts, so it is the bridge between the global formal
pullback and the local descent.

## Main definitions

* `AlgebraicGeometry.Space.chartFormalPullbackProj` — the second projection of the formal
  pullback over an affine chart, landing in the completed module of the tower of sections of `E`.
* `AlgebraicGeometry.Space.chartLimitSectionOfCompleted` — the inverse identification, from the
  completed module back to the sections of `lim E`.

## Main results

* `AlgebraicGeometry.Space.completionToLimit_eq_limMap_iff` — **the defining condition of the
  formal pullback over an affine chart is the equation `φ y = 1 ⊗ g` the formal-glueing descent is
  stated with.**
* `AlgebraicGeometry.Space.chartCompletedComparisonLinear_chartFormalPullbackProj` — **the
  comparison map carries the second component of a section of the formal pullback to the image of
  its first component**, in the adic completion of the sections of `G`.
* `AlgebraicGeometry.Space.chartCompletedComparisonTensor_chartFormalPullbackProj` — the same
  equation with the comparison map read over the extension of scalars, where the right-hand side
  is the elementary tensor `1 ⊗ g`.

## Implementation notes

Three identifications are composed, and each is already available: the sections of a limit are
the limit of the sections (`AlgebraicGeometry.Space.chartLimitSectionsIso`), the limit of the
tower of sections of `E` is its own completion because it is adically complete
(`Stacks.Coherent.completeModuleEquivAdicCompletion`), and the limit of the tower of sections of
`G^∧` is the adic completion of the sections of `G`
(`AlgebraicGeometry.Space.chartCompletionLimitEquiv`).  The commuting square of the formal
pullback, read on the sections over the chart, is what makes the three fit together.

## References

* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
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

/-- The second projection of the formal pullback over a Noetherian affine chart, landing in the
completed module of the tower of sections of `E`: restrict to the chart, identify the sections of
the limit with the limit of the sections, and identify that limit with its own completion. -/
def chartFormalPullbackProj
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :
    chartCompletedSections B S hS F hF 𝓘 E V :=
  haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
      (M := chartSectionsLimit B S hS F hF E V)
    ((chartLimitSectionsIso B S hS F hF E V).hom
      ((formalPullbackProj B S hS F hF 𝓘 G α).val.app (op V) p))

/-- The completed module of the tower of sections of `E` over a Noetherian affine chart,
compared with the sections of `lim E`: the inverse of the identification used by
`AlgebraicGeometry.Space.chartFormalPullbackProj`. -/
def chartLimitSectionOfCompleted (z : chartCompletedSections B S hS F hF 𝓘 E V) :
    (limit E : Modules.{u, u} B S hS F hF).val.obj (op V) :=
  haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  (chartLimitSectionsIso B S hS F hF E V).inv
    ((Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
      (M := chartSectionsLimit B S hS F hF E V)).symm z)

/-- The comparison map, computed on the completed module of a section of `lim E`. -/
theorem chartCompletedComparisonLinear_completeModuleEquiv
    (y : (limit E : Modules.{u, u} B S hS F hF).val.obj (op V)) :
    haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
        (chartSectionsLimit B S hS F hF E V) :=
      isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
    chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
        (Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
          (M := chartSectionsLimit B S hS F hF E V)
          ((chartLimitSectionsIso B S hS F hF E V).hom y)) =
      (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
            hG.toIsQuasicoherentOnSite) hV.1).symm
        ((chartLimitSectionsIso B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 G) V).hom
          ((limMap α).val.app (op V) y)) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set cL := Stacks.Coherent.completeModuleEquivAdicCompletion
    (chartSectionIdeal B S hS F hF 𝓘 V)
    (M := chartSectionsLimit B S hS F hF E V) with hcL
  have hstep : chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
      (cL ((chartLimitSectionsIso B S hS F hF E V).hom y)) =
      (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
            hG.toIsQuasicoherentOnSite) hV.1).symm
        (chartSectionsLimitMap B S hS F hF α V
          ((chartLimitSectionsIso B S hS F hF E V).hom y)) := by
    show (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
          hG.toIsQuasicoherentOnSite) hV.1).symm
      (chartSectionsLimitMap B S hS F hF α V
        (cL.symm (cL ((chartLimitSectionsIso B S hS F hF E V).hom y)))) = _
    rw [LinearEquiv.symm_apply_apply]
  rw [hstep, chartLimitSectionsIso_hom_chartSectionsLimitMap]

/-- The image in the adic completion of a section of `G`, computed through the identification of
the limit of the completion with that adic completion. -/
theorem of_eq_chartCompletionLimitEquiv_symm (g : G.val.obj (op V)) :
    AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) g =
      (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
            hG.toIsQuasicoherentOnSite) hV.1).symm
        ((chartLimitSectionsIso B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 G) V).hom
          ((completionToLimit B S hS F hF 𝓘 G).val.app (op V) g)) := by
  rw [chartLimitSectionsIso_completionToLimit B S hS F hF 𝓘 hIcart G
    (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
      hG.toIsQuasicoherentOnSite) hV.1 g, LinearEquiv.symm_apply_apply]

/-- **The defining condition of the formal pullback over an affine chart is the equation the
formal-glueing descent is stated with.**  A section `g` of `G` and a section `y` of `lim E` over
a Noetherian affine chart agree in `lim G / 𝓘 ⁿ⁺¹ G` exactly when the comparison map sends the
completed module of `y` to the image of `g` in the adic completion of `G(V)`. -/
theorem completionToLimit_eq_limMap_iff
    (g : G.val.obj (op V)) (y : (limit E : Modules.{u, u} B S hS F hF).val.obj (op V)) :
    haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
        (chartSectionsLimit B S hS F hF E V) :=
      isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
    ((completionToLimit B S hS F hF 𝓘 G).val.app (op V) g = (limMap α).val.app (op V) y ↔
      chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
          (Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
            (M := chartSectionsLimit B S hS F hF E V)
            ((chartLimitSectionsIso B S hS F hF E V).hom y)) =
        AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) g) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  rw [chartCompletedComparisonLinear_completeModuleEquiv,
    of_eq_chartCompletionLimitEquiv_symm B S hS F hF 𝓘 hIcart G hG hV g]
  rw [eq_comm]
  exact ((chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
        hG.toIsQuasicoherentOnSite) hV.1).symm.injective.comp
    (ConcreteCategory.bijective_of_isIso
      (chartLimitSectionsIso B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 G) V).hom).1).eq_iff.symm

/-- **The comparison map carries the second component of a section of the formal pullback to the
image of its first component in the adic completion of the sections of `G`.**

The commuting square of the formal pullback says that the two components agree in
`lim G / 𝓘 ⁿ⁺¹ G`; reading that limit as the adic completion of the sections of `G` turns the
agreement into this equation. -/
theorem chartCompletedComparisonLinear_chartFormalPullbackProj
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :
    chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
        (chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p) =
      AdicCompletion.of (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))
        ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  refine (completionToLimit_eq_limMap_iff B S hS F hF 𝓘 hIcart hE G hG α hV _ _).1 ?_
  exact congrArg (fun k : formalPullback B S hS F hF 𝓘 G α ⟶
    limit (adicQuotientSystem B S hS F hF 𝓘 G) => k.val.app (op V) p)
    (formalPullback_comm B S hS F hF 𝓘 G α)

/-- **The same equation with the comparison map read over the extension of scalars**, where the
right-hand side is the elementary tensor `1 ⊗ g`. -/
theorem chartCompletedComparisonTensor_chartFormalPullbackProj
    (p : (formalPullback B S hS F hF 𝓘 G α).val.obj (op V)) :
    chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV
        (chartFormalPullbackProj B S hS F hF 𝓘 hIcart hE G α hV p) =
      (1 : AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)) ⊗ₜ[
          chartRing B S hS F hF V]
        ((formalPullbackMap B S hS F hF 𝓘 G α).val.app (op V) p) := by
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  refine (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
    (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))).injective ?_
  rw [ofTensorProductEquiv_chartCompletedComparisonTensor,
    chartCompletedComparisonLinear_chartFormalPullbackProj]
  simp [AdicCompletion.ofTensorProductEquivOfFiniteNoetherian]

end AlgebraicGeometry.Space

end
