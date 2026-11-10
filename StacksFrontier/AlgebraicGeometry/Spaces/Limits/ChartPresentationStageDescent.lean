module

public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationChartsBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ChartRestrictionStagesColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.GlobalFunctionsStagesModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.PresentationStageDescent

/-!
# The standard-étale presentation of the limit chart, descended to a stage

Let `A` be a limit situation with an affine surjective étale chart `U₀ ⟶ X₀` of its chosen stage
whose relation `R₀ = U₀ ×_{X₀} U₀` is again affine, and let `X = lim X_i` be its limit. Stacks
07SI then presents the global functions of the limit as the filtered colimit of those of the
stages (`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_stageModel`), and Stacks 01Z0
presents the regular functions of the limit chart as the filtered colimit of those of the stage
charts (`AlgebraicGeometry.Space.LimitSituation.isStagesColimit_appTop_chartStagesCone`).

This file joins the two systems by the restriction homomorphisms `Γ(X_i, 𝒪) ⟶ Γ(U_i, 𝒪)` and
feeds the pair to `AlgebraicGeometry.Space.exists_ge_presentationStageDescent`: a standard-étale
presentation of the regular functions of the limit chart over the global functions of the limit,
together with surjectivity of its spectrum, descends to a single stage.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation.chartFunctionsAt` and `.chartFunctionsTransition`: the
  regular functions of the chart of a stage and the transition homomorphisms between them.
* `AlgebraicGeometry.Space.LimitSituation.chartRestrictionAt`: restriction of the global
  functions of a stage to the chart of that stage, read on the canonical `u`-model.

## Main results

* `AlgebraicGeometry.Space.LimitSituation.directedSystem_chartFunctionsTransition`: the regular
  functions of the stage charts form a directed system.
* `AlgebraicGeometry.Space.LimitSituation.chartFunctionsTransition_chartRestrictionAt` and
  `.chartStagesCone_π_chartRestrictionAt`: restriction to the charts is compatible with the
  transitions of the system and with the passage to the limit.
* `AlgebraicGeometry.Space.LimitSituation.exists_ge_chartPresentationStageDescent`: the descent.

## Implementation notes

*Where the two compatibilities come from.* The stagewise one is
`AlgebraicGeometry.Space.LimitSituation.stageGlobalFunctionsEquiv_naturality` and the limit one is
`AlgebraicGeometry.Space.LimitSituation.globalFunctionsChartRestriction_limitEtaleChart`; both are
proved, and all that is added here is the change of spelling from the value of a compatible family
at a chart to the restriction homomorphism, which is a definitional unfolding, together with the
conjugation by the identifications of the `u`-models.

*The directed-system laws of the chart functions* are the functoriality of the reindexed diagram
of schemes followed by global sections; a preorder is a thin category, so the two laws are
`CategoryTheory.Functor.map_id` and `CategoryTheory.Functor.map_comp`.

Nothing here raises a compiler limit or disables a linter.

## References

* [Stacks Project, Tag 07SQ](https://stacks.math.columbia.edu/tag/07SQ)
* [Stacks Project, Tag 07SI](https://stacks.math.columbia.edu/tag/07SI)
* [Stacks Project, Tag 01Z0](https://stacks.math.columbia.edu/tag/01Z0)
* [Stacks Project, Tag 00U9](https://stacks.math.columbia.edu/tag/00U9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite MvPolynomial

universe u

namespace AlgebraicGeometry.Space.LimitSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (A : LimitSituation B S hS hZ X) {U₀ R₀ : BigAffineFppf B S hS}
  {f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ A.system.obj (op A.base)}
  {t : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj R₀) ⟶
    yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀)}
  {s : (BigAffineFppf.inclusion B S hS).obj R₀ ⟶ (BigAffineFppf.inclusion B S hS).obj U₀}

/-- The regular functions of the chart of a stage. -/
abbrev chartFunctionsAt (i : A.Stages) : Type u :=
  Γ((A.chartStagesDiagram U₀ f₀).obj (op i), ⊤)

/-- The transition homomorphism of the system of regular functions of the stage charts. -/
abbrev chartFunctionsTransition (i j : A.Stages) (h : i ≤ j) :
    A.chartFunctionsAt (U₀ := U₀) (f₀ := f₀) i →+* A.chartFunctionsAt (U₀ := U₀) (f₀ := f₀) j :=
  ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom

/-- The regular functions of the stage charts form a directed system. -/
instance directedSystem_chartFunctionsTransition :
    DirectedSystem (A.chartFunctionsAt (U₀ := U₀) (f₀ := f₀))
      fun i j h => A.chartFunctionsTransition (U₀ := U₀) (f₀ := f₀) i j h where
  map_self i x := by
    change ((A.chartStagesDiagram U₀ f₀).map (homOfLE (le_refl i)).op).appTop.hom x = x
    rw [show (homOfLE (le_refl i)).op = 𝟙 (op i) from rfl,
      CategoryTheory.Functor.map_id]
    rfl
  map_map {i j k} hij hjk x := by
    change ((A.chartStagesDiagram U₀ f₀).map (homOfLE hjk).op).appTop.hom
        (((A.chartStagesDiagram U₀ f₀).map (homOfLE hij).op).appTop.hom x)
      = ((A.chartStagesDiagram U₀ f₀).map (homOfLE (hij.trans hjk)).op).appTop.hom x
    rw [show (homOfLE (hij.trans hjk)).op
        = (homOfLE hjk).op ≫ (homOfLE hij).op from rfl, CategoryTheory.Functor.map_comp]
    rfl

/-- The restriction of the global functions of a stage to the chart of that stage, read on the
canonical `u`-model of those global functions. -/
def chartRestrictionAt
    (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
    (i : A.Stages) :
    A.stageModel i →+* A.chartFunctionsAt (U₀ := U₀) (f₀ := f₀) i :=
  (globalFunctionsChartRestriction B S hS (A.stage i.1)
    (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)).comp (A.stageModelEquiv i).toRingHom

section Compat

variable (hf₀ : IsEtaleChart B S hS (A.system.obj (op A.base)) (CostructuredArrow.mk f₀))
  (hsurj : IsSurjective B S hS f₀) (hpb : IsPullback t (yoneda.map s) f₀ f₀)

include hsurj hpb

/-- **Restriction to the stage charts is compatible with the transitions of the system.** -/
theorem chartFunctionsTransition_chartRestrictionAt (i j : A.Stages) (h : i ≤ j)
    (x : A.stageModel i) :
    A.chartFunctionsTransition (U₀ := U₀) (f₀ := f₀) i j h (A.chartRestrictionAt hf₀ i x)
      = A.chartRestrictionAt hf₀ j (A.stageModelTransition i j h x) := by
  have key := A.stageGlobalFunctionsEquiv_naturality hf₀ hsurj hpb i j h
    (A.stageModelEquiv i x)
  rw [A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb j,
    A.stageGlobalFunctionsEquiv_val hf₀ hsurj hpb i] at key
  change ((A.chartStagesDiagram U₀ f₀).map (homOfLE h).op).appTop.hom
      ((A.stageModelEquiv i x).val
        (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ i)))
    = (A.stageModelEquiv j (A.stageModelTransition i j h x)).val
        (op (A.stagesEtaleChart (A.chartSystem U₀ f₀) hf₀ j))
  rw [stageModelTransition_apply, RingEquiv.apply_symm_apply]
  exact key.symm

/-- **Restriction to the stage charts is compatible with the passage to the limit.** -/
theorem chartStagesCone_π_chartRestrictionAt (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded) {Alim : Type u} [CommRing Alim]
    (eA : Alim ≃+* globalFunctions B S hS (A.limitSpace hX).obj) (i : A.Stages)
    (x : A.stageModel i) :
    ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op i)).appTop.hom
        (A.chartRestrictionAt hf₀ i x)
      = ((globalFunctionsChartRestriction B S hS (A.limitSpace hX)
          (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI)
            hf₀)).comp eA.toRingHom) (A.modelProjection hX eA i x) := by
  refine Eq.trans (A.globalFunctionsChartRestriction_limitEtaleChart hX hI hf₀ hsurj hpb i
    (A.stageModelEquiv i x)).symm ?_
  exact congrArg (globalFunctionsChartRestriction B S hS (A.limitSpace hX)
    (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI) hf₀))
    (eA.apply_symm_apply _).symm

/-- **The standard-étale presentation of the limit chart descends to a stage.** -/
theorem exists_ge_chartPresentationStageDescent (hX : IsAlgebraicSpace B S hS X)
    (hI : A.ChartsBounded) {Alim : Type u} [CommRing Alim]
    (eA : Alim ≃+* globalFunctions B S hS (A.limitSpace hX).obj)
    {m : ℕ} (gl : Fin m → MvPolynomial (Fin m) Alim)
    (hl : Fin m → Γ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).pt, ⊤))
    (hrel : ∀ l, eval₂ ((globalFunctionsChartRestriction B S hS (A.limitSpace hX)
        (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI)
          hf₀)).comp eA.toRingHom) hl (gl l) = 0)
    (hΔ : IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range gl)) (detJacobian gl)))
    (hsurjSpec : Function.Surjective (PrimeSpectrum.comap
      ((globalFunctionsChartRestriction B S hS (A.limitSpace hX)
        (A.limitEtaleChart (A.chartSystem U₀ f₀) (A.chartLimitBridgeOfChartsBounded U₀ f₀ hI)
          hf₀)).comp eA.toRingHom)))
    (i₀ : A.Stages) :
    ∃ (j : A.Stages) (_ : i₀ ≤ j) (g : Fin m → MvPolynomial (Fin m) (A.stageModel j))
      (h : Fin m → A.chartFunctionsAt (U₀ := U₀) (f₀ := f₀) j)
      (_ : ∀ l, eval₂ (A.chartRestrictionAt hf₀ j) h (g l) = 0),
      (∀ k, map (A.modelProjection hX eA j) (g k) = gl k) ∧
        (∀ k, ((A.chartStagesConeOfChartsBounded U₀ f₀ hI).π.app (op j)).appTop.hom (h k) = hl k) ∧
        IsUnit (Ideal.Quotient.mk (Ideal.span (Set.range g)) (detJacobian g)) ∧
        Function.Surjective (PrimeSpectrum.comap
          (algebraMap (A.stageModel j) (presentationAlgebra g))) := by
  have _ : IsDirectedOrder A.Stages := inferInstance
  have hcol := A.isStagesColimit_appTop_chartStagesCone (U₀ := U₀) (f₀ := f₀) hI
  exact exists_ge_presentationStageDescent
    (nt := fun i j h => A.chartFunctionsTransition (U₀ := U₀) (f₀ := f₀) i j h)
    (A.modelProjection_stageModelTransition hX eA hI hf₀ hsurj hpb)
    (A.exists_stageModel_eq hX eA hI hf₀ hsurj hpb)
    (fun i x hx => A.exists_stageModelTransition_eq_zero hX eA hI hf₀ hsurj hpb i x hx)
    (fun i j h x => hcol.ι_trans i j h x) (fun a => hcol.exists_stage a)
    (fun i x hx => by
      obtain ⟨j, hij, hj⟩ := hcol.exists_trans_eq i x 0 (by rw [hx, map_zero])
      exact ⟨j, hij, by rw [hj, map_zero]⟩)
    (A.chartFunctionsTransition_chartRestrictionAt hf₀ hsurj hpb)
    (A.chartStagesCone_π_chartRestrictionAt hf₀ hsurj hpb hX hI eA)
    gl hl hrel hΔ hsurjSpec i₀

end Compat

end AlgebraicGeometry.Space.LimitSituation

end
