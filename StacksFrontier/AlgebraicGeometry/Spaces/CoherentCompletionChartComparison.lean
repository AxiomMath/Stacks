module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelStabilization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionChartLimit
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

/-!
# The comparison map of a map into a completion, over an affine chart

Let `F` be an algebraic space over a scheme `S`, let `𝓘 ⊆ 𝒪_F` be a sheaf of ideals on its small
étale site which is cartesian on affine charts, let `G` be a coherent `𝒪_F`-module, let `E` be a
coherent `𝓘`-adic system and let `α : E ⟶ G^∧` be a morphism of inverse systems.  Over a
Noetherian affine étale chart `V` with ring `A = 𝒪_F(V)`, ideal `I = 𝓘(V)` and completed ring
`S = A^∧`, the sections of `E` form a tower whose limit is `I`-adically complete and whose
completion `M' = (lim_n E_n(V))^∧` is a finite `S`-module, by
`AlgebraicGeometry.Space.moduleFinite_chartCompletedSections`.  This file builds out of `α` the
`S`-linear comparison map

`φ : M' ⟶ S ⊗_A G(V)`

whose kernel and cokernel the hypothesis of Stacks 08BB controls, and which is the input of the
formal-glueing descent `AdicCompletion.exists_finite_descent_of_isIPowerTorsion`.

## Main definitions

* `AlgebraicGeometry.Space.chartCompletedComparisonLinear` — the comparison map, as an
  `A`-linear map `M' →ₗ[A] AdicCompletion I (G(V))`.
* `AlgebraicGeometry.Space.chartCompletedComparison` — the same map read as `S`-linear, which is
  the form the descent theorem consumes.
* `AlgebraicGeometry.Space.chartCompletedComparisonTensor` — the comparison map with target
  `S ⊗_A G(V)`.

## Main results

* `AlgebraicGeometry.Space.chartCompletedComparisonLinear_apply` — the comparison map is the
  limit of the maps on sections of `α`, read through the identification of the limit of the
  completion with the adic completion of the sections.
* `AlgebraicGeometry.Space.eval_chartCompletedComparisonLinear` — **its level-`n + 1` component
  is the map on sections of `α` at level `n`**, which is what turns the levelwise hypothesis of
  Stacks 0888 into a statement about the kernel and the cokernel of `φ`.

## Implementation notes

The comparison map is built `A`-linearly and then upgraded: an `A`-linear map between modules
over the completion whose target is Hausdorff is automatically linear over the completion, by
`Stacks.Coherent.completion_linearMap_smul`.  Doing it the other way round would require an
`S`-module structure on the inverse limit `lim_n E_n(V)` itself, which this development does not
have — only its completion carries one, exactly as recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartTower`.

The identification of the limit of the sections of `G^∧` with the adic completion of `G(V)` is
`AlgebraicGeometry.Space.chartCompletionLimitEquiv`, and the identification of `lim_n E_n(V)`
with its own completion is `Stacks.Coherent.completeModuleEquivAdicCompletion`, which applies
because the limit of the tower of sections of a coherent adic system over a Noetherian affine
chart is `I`-adically complete.

The last step to `S ⊗_A G(V)` is Mathlib's
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`, which needs the ring of the chart
Noetherian and the sections of `G` finite over it; both hold over a Noetherian affine chart, the
second by `AlgebraicGeometry.Space.moduleFinite_sections_of_isCoherent`.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
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

/-! ### The comparison map -/

/-- **The comparison map of `α` over a Noetherian affine chart, as an `A`-linear map.**  It sends
the completion of the limit of the tower of sections of `E` to the `I`-adic completion of the
sections of `G`: undo the completion of the limit, which is already complete, apply the limit of
the maps on sections of `α`, and read the result through the identification of the limit of the
sections of `G^∧` with the adic completion of `G(V)`. -/
def chartCompletedComparisonLinear :
    chartCompletedSections B S hS F hF 𝓘 E V →ₗ[chartRing B S hS F hF V]
      AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) :=
  haveI : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  (chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
          hG.toIsQuasicoherentOnSite) hV.1).symm.toLinearMap ∘ₗ
    (ModuleCat.Hom.hom (chartSectionsLimitMap B S hS F hF α V)) ∘ₗ
      (Stacks.Coherent.completeModuleEquivAdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V)
        (M := chartSectionsLimit B S hS F hF E V)).symm.toLinearMap

/-- **The level-`n + 1` component of the comparison map is the map on sections of `α` at level
`n`.**  This is what carries the levelwise hypothesis of Stacks 0888 over to the kernel and the
cokernel of the comparison map. -/
theorem eval_chartCompletedComparisonLinear (n : ℕ)
    (x : chartCompletedSections B S hS F hF 𝓘 E V) :
    AdicCompletion.eval (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) (n + 1)
        (chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV x) =
      (chartAdicQuotientLevelEquiv B S hS F hF 𝓘 hIcart G
          (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
            hG.toIsQuasicoherentOnSite) hV.1 n).symm
        ((α.app (op n)).val.app (op V)
          (chartCompletedLevel B S hS F hF 𝓘 E
            (isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV) n x)) := by
  have hcomplete : IsAdicComplete (chartSectionIdeal B S hS F hF 𝓘 V)
      (chartSectionsLimit B S hS F hF E V) :=
    isAdicComplete_chartSectionsLimit B S hS F hF 𝓘 hE hIcart hV
  set Gcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF G
    hG.toIsQuasicoherentOnSite with hGcart
  set q := chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G Gcart hV.1 with hq
  set cL := Stacks.Coherent.completeModuleEquivAdicCompletion
    (chartSectionIdeal B S hS F hF 𝓘 V)
    (M := chartSectionsLimit B S hS F hF E V) with hcL
  set z := chartSectionsLimitMap B S hS F hF α V (cL.symm x) with hz
  have hphi : chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV x = q.symm z := rfl
  have hlevel := chartSectionsLevel_chartCompletionLimitEquiv B S hS F hF 𝓘 hIcart G Gcart hV.1 n
    (q.symm z)
  rw [q.apply_symm_apply] at hlevel
  have hz' : chartSectionsLevel B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 G) V n z =
      (α.app (op n)).val.app (op V)
        (chartCompletedLevel B S hS F hF 𝓘 E hcomplete n x) :=
    congrArg
      (fun k : chartSectionsLimit B S hS F hF E V ⟶
          (chartSectionsSystem B S hS F hF (adicQuotientSystem B S hS F hF 𝓘 G) V).obj (op n) =>
        k (cL.symm x))
      (chartSectionsLimitMap_chartSectionsLevel B S hS F hF α V n)
  rw [hphi, ← hz', hlevel, LinearEquiv.symm_apply_apply]

/-! ### The comparison map over the completed ring -/

/-- **The comparison map of `α` over a Noetherian affine chart, read over the completed ring.**

The underlying map is `AlgebraicGeometry.Space.chartCompletedComparisonLinear`, which is only
`A`-linear by construction; it is linear over `A ^∧` by
`Stacks.Coherent.completion_linearMap_smul`, the target being an adic completion and therefore
Hausdorff. -/
def chartCompletedComparison :
    chartCompletedSections B S hS F hF 𝓘 E V →ₗ[
        AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
      AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V)) where
  toFun := chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV
  map_add' := (chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV).map_add
  map_smul' r x :=
    haveI : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
    Stacks.Coherent.completion_linearMap_smul (chartSectionIdeal B S hS F hF 𝓘 V)
      (Ideal.fg_of_isNoetherianRing _)
      (chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV) r x

/-- The comparison map over the completed ring has the same underlying function as the `A`-linear
one. -/
theorem chartCompletedComparison_apply (x : chartCompletedSections B S hS F hF 𝓘 E V) :
    chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV x =
      chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV x :=
  rfl

/-! ### The comparison map with target the extension of scalars -/

/-- **The comparison map of `α` over a Noetherian affine chart, with target the extension of
scalars `A ^∧ ⊗_A G(V)`.**  This is the shape the formal-glueing descent
`AdicCompletion.exists_finite_descent_of_isIPowerTorsion` consumes.

The sections of `G` over a Noetherian affine chart are a finite module over the Noetherian ring
of the chart, so the adic completion of those sections is the extension of scalars to the
completed ring, by `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
def chartCompletedComparisonTensor :
    chartCompletedSections B S hS F hF 𝓘 E V →ₗ[
        AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V)]
      TensorProduct (chartRing B S hS F hF V)
        (AdicCompletion (chartSectionIdeal B S hS F hF 𝓘 V) (chartRing B S hS F hF V))
        (G.val.obj (op V)) :=
  haveI : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  haveI : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
        (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))).symm.toLinearMap ∘ₗ
    chartCompletedComparison B S hS F hF 𝓘 hIcart hE G hG α hV

/-- The comparison map with target the extension of scalars is the one with target the adic
completion, read through
`AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`. -/
theorem ofTensorProductEquiv_chartCompletedComparisonTensor
    (x : chartCompletedSections B S hS F hF 𝓘 E V) :
    haveI : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
    haveI : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
      moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
    AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
        (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))
        (chartCompletedComparisonTensor B S hS F hF 𝓘 hIcart hE G hG α hV x) =
      chartCompletedComparisonLinear B S hS F hF 𝓘 hIcart hE G hG α hV x := by
  have : IsNoetherianRing (chartRing B S hS F hF V) := hV.2
  have : Module.Finite (chartRing B S hS F hF V) (G.val.obj (op V)) :=
    moduleFinite_sections_of_isCoherent B S hS F hF G hG hV.1
  exact (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian
    (chartSectionIdeal B S hS F hF 𝓘 V) (G.val.obj (op V))).apply_symm_apply _

end AlgebraicGeometry.Space

end
