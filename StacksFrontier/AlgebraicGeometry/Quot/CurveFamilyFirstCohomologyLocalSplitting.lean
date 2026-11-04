module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeOfCoversTop
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictFree
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFirstCohomologyFromSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedPerfectConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.ChartSliceTransport
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Part (2) of Stacks 0E1J from an étale-local splitting of `Rf_*𝒪_X`

Let `f : X → S` be a family of curves (Stacks 0D4Z) with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for every
`s ∈ S`. If, étale locally on `S`, there is a decomposition

`Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]`, `M` finite free,

then `R¹f_*𝒪_X = H¹(Rf_*𝒪_X)` is finite free on the members of an étale covering, hence finite
locally free: part (2) of Stacks 0E1J. The decomposition is the étale-local form of
`AlgebraicGeometry.CurveFamily.DerivedPushforwardSplitsOffSingle`, restricted to the charts of the
small étale site of the base by `AlgebraicGeometry.Space.etaleModulePullback`.

## Main definitions

* `AlgebraicGeometry.CurveFamily.HasLocalDerivedPushforwardSplitting`: a family of charts
  covering the base on each of which `(Rf_*𝒪_X)|_V ≅ 𝒪_V ⊕ 𝒪_V^{⊕ I}[-1]` with `I` finite.

## Main results

* `nonempty_free_iso_over_of_etaleModulePullback_iso_free`: a module on the small étale site of an
  algebraic space whose restriction to a chart is finite free is finite free on the slice at that
  chart.
* `hasFiniteLocallyFreeFirstHigherDirectImage_of_localSplitting`: part (2) of Stacks 0E1J for a
  family with an étale-local splitting.
* `hasFiniteLocallyFreeFirstHigherDirectImage_of_forall_localSplitting`: part (2) of Stacks 0E1J
  for every family in `Curves^{h0,1}`, given an étale-local splitting for each of them.

## Implementation notes

The derived categories are those of the standard model, fixed inside the statements by `letI`.

## References

* [Stacks Project, Tag 0E1J](https://stacks.math.columbia.edu/tag/0E1J)
* [Stacks Project, Tag 0E6B](https://stacks.math.columbia.edu/tag/0E6B)
* [Stacks Project, Tag 0CTM](https://stacks.math.columbia.edu/tag/0CTM)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

namespace CurveFamily

/-- **A module whose restriction to a chart is finite free is finite free on the slice at that
chart.** -/
theorem nonempty_free_iso_over_of_etaleModulePullback_iso_free
    {T : AlgebraicSpaces B integerBase hZ}
    (M : Space.Modules.{u, u} B integerBase hZ T.1 T.2) (V : Space.SmallEtale B integerBase hZ T.1)
    (I : Type u)
    (e : (Space.etaleModulePullback.{u, u} B integerBase hZ
        (Space.chartToSpace B integerBase hZ T V)
        (Space.isEtale_chartToSpace B integerBase hZ T V)).obj M ≅
      SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
        (Space.chartSpace B integerBase hZ T V).1) I) :
    Nonempty (SheafOfModules.free (R := (Space.structureRingSheaf B integerBase hZ T).over V) I ≅
      M.over V) := by
  let F := Space.chartModuleSliceReindex B integerBase hZ T V
  have : F.IsEquivalence := Space.isEquivalence_chartModuleSliceReindex B integerBase hZ T V
  have eF : F.obj (SheafOfModules.free
      (R := (Space.structureRingSheaf B integerBase hZ T).over V) I) ≅
      SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
        (Space.chartSpace B integerBase hZ T V).1) I :=
    SheafOfModules.freeIsoOfUnitIso F
      (Space.chartModuleSliceReindexUnitRingStructureIso B integerBase hZ T V) I inferInstance
  exact ⟨F.preimageIso (eF ≪≫ e.symm ≪≫
    ((Space.chartSliceReindexOverIso B integerBase hZ T V).app M).symm)⟩

/-- **An étale-local splitting `Rf_*𝒪_X ≅ 𝒪_S ⊕ M[-1]` with `M` finite free**, for a family of
curves `f : X → S`: a family of charts `V_k` of the small étale site of `S` covering the final
object such that on each of them `(Rf_*𝒪_X)|_{V_k} ≅ 𝒪_{V_k}[0] ⊕ 𝒪_{V_k}^{⊕ I_k}[-1]` for a
finite type `I_k`. This is Stacks 0E6B, part (b) for `f`, with the summand `P` sharpened to
`H¹(P)[-1]` and `H¹(P)` free. -/
def HasLocalDerivedPushforwardSplitting (X : CurveFamily B hZ) : Prop :=
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  letI := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  ∃ (ι : Type (u + 1)) (V : ι → Space.SmallEtale B integerBase hZ (schemeSpace X.base).1),
    (Space.SmallEtale.topology B integerBase hZ (schemeSpace X.base).1).CoversTop V ∧
    ∀ k : ι,
      letI := HasDerivedCategory.standard
        (Space.Modules.{u, u} B integerBase hZ
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
          (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2)
      ∃ I : Type u, Finite I ∧
        Nonempty ((Space.etaleModulePullback.{u, u} B integerBase hZ
            (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
            (Space.isEtale_chartToSpace B integerBase hZ
              (schemeSpace X.base) (V k))).mapDerivedCategory.obj
            ((Space.smallEtaleDerivedModulePushforward B integerBase hZ X.toBase).obj
              ((DerivedCategory.singleFunctor
                (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) 0).obj
                (Space.structureSheafModule B integerBase hZ X.total))) ≅
          (DerivedCategory.singleFunctor
            (Space.Modules.{u, u} B integerBase hZ
              (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
              (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2) 0).obj
              (SheafOfModules.unit _) ⊞
            (DerivedCategory.singleFunctor
              (Space.Modules.{u, u} B integerBase hZ
                (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
                (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2) 1).obj
              (SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
                (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1) I))

/-- **Part (2) of Stacks 0E1J for a family with an étale-local splitting.** If `Rf_*𝒪_X` splits
étale locally as in `HasLocalDerivedPushforwardSplitting`, then `R¹f_*𝒪_X` is finite locally
free. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of_localSplitting {X : CurveFamily B hZ}
    (h : X.HasLocalDerivedPushforwardSplitting) :
    X.HasFiniteLocallyFreeFirstHigherDirectImage := by
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2)
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ (schemeSpace X.base).1 (schemeSpace X.base).2)
  obtain ⟨ι, V, hV, hk⟩ := h
  refine SheafOfModules.isFiniteLocallyFree_of_coversTop.{u, u, u + 1} hV _ fun k => ?_
  let := HasDerivedCategory.standard
    (Space.Modules.{u, u} B integerBase hZ
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1
      (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).2)
  obtain ⟨I, hI, ⟨e⟩⟩ := hk k
  let E := Space.etaleModulePullback.{u, u} B integerBase hZ
    (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
    (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
  have := Space.etaleModulePullback_additive.{u, u} B integerBase hZ
    (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
    (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
  have := Space.preservesFiniteLimits_etaleModulePullback B integerBase hZ
    (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
    (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
  have := Space.preservesFiniteColimits_etaleModulePullback B integerBase hZ
    (Space.chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
    (Space.isEtale_chartToSpace B integerBase hZ (schemeSpace X.base) (V k))
  have e₁ : E.obj (X.firstDirectImage B hZ) ≅
      SheafOfModules.free (R := Space.ringStructureSheaf B integerBase hZ
        (Space.chartSpace B integerBase hZ (schemeSpace X.base) (V k)).1) I :=
    E.mapIso X.homologyDerivedPushforwardIsoFirstHigherDirectImage.symm ≪≫
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso E 1).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ 1).mapIso e ≪≫
      DerivedCategory.homologyBiprodSingleIso _ _ (by norm_num)
  exact ⟨I, hI, nonempty_free_iso_over_of_etaleModulePullback_iso_free _ (V k) I e₁⟩

/-- If every family of curves with `κ(s) = H⁰(X_s, 𝒪_{X_s})` for all `s` has an étale-local
splitting of `Rf_*𝒪_X`, then every such family has finite locally free `R¹f_*𝒪_X`. -/
theorem hasFiniteLocallyFreeFirstHigherDirectImage_of_forall_localSplitting
    (h : ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasLocalDerivedPushforwardSplitting) :
    ∀ X : CurveFamily B hZ, X.HasResidueFieldGlobalFunctions →
      X.HasFiniteLocallyFreeFirstHigherDirectImage :=
  fun X hX => hasFiniteLocallyFreeFirstHigherDirectImage_of_localSplitting (h X hX)

end CurveFamily

end AlgebraicGeometry

end
