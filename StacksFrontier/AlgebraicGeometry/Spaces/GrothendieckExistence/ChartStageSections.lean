module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EtaleStageSectionsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ChartBaseRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.RelativePseudoCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTensorSectionsBaseChange
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsAdjunctionComp
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplementQuasiSeparated

/-!
# The derived sections of `K` over an affine étale chart, after base change to `Aₙ`

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], with its
canonical map `K ⟶ (iₙ,* Fₙ)[0]` (`FlatSheafExistenceSituation.derivedLimitProjection`). Let `U`
be an affine étale chart of `X`, with ring of functions `Γ(U)`, and `φ_U : A ⟶ Γ(U)` its ring map
from `A = lim Aₙ` (`FlatSheafExistenceSituation.chartBaseRingHom`). Put `E = RΓ(U, K)`, read in
`D(A)` along `φ_U`. This file proves the chart statements of [Stacks, Tag 0CX9], given
[Stacks, Tag 0CX6] (1) at level `n` (the hypothesis `h0CX6`, in the form consumed by
`FlatSheafExistenceSituation.isIso_etaleStageBaseChangeMap_of_isIso`):

* (a) `Hⁱ(E ⊗^𝐋_A Aₙ) = 0` for `i ≠ 0`;
* (b) if moreover `Hⁱ(E) = 0` for `i > 0`, the map `H⁰(E) ⟶ H⁰(RΓ(U, iₙ,* Fₙ))` induced by
  `K ⟶ (iₙ,* Fₙ)[0]` is surjective with kernel `(ker(A → Aₙ) Γ(U)) • H⁰(E)`, that is
  `H⁰(E) ⊗_A Aₙ ≅ Γ(U, iₙ,* Fₙ)`.

They are instances of the statements over variable spaces of
`AlgebraicGeometry/Spaces/ChartTensorSectionsBaseChange.lean`, at the chart and the stage `Xₙ`,
read over the literal rings `A = lim Aₙ` and `Aₙ` through `Γ(Spec R, 𝒪) ≅ R`.

## Main results

All in the namespace `AlgebraicGeometry.Space.FlatSheafExistenceSituation`:

* `isIso_chartTensorSectionsIdentification`: the identification `ψ_U` is invertible.
* `isZero_homology_chartDerivedSections_of_isIso`: (a).
* `surjective_and_ker_chartDerivedSections_of_isIso`: (b).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasRightDerivedFunctor_chartSections

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)
  (U : SmallEtale D.B D.S D.containsLimitBase D.X.left.1)

/-- The morphism `U ⟶ Spec A` of the big fppf site underlying an étale chart `U` of `X`. -/
abbrev chartBaseHom :
    (SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U ⟶
      limitBaseObject D.system D.B D.containsLimitBase :=
  yoneda.preimage (U.1.hom ≫ D.X.hom.hom)

/-- The chart morphism `h_U ⟶ X` followed by `X ⟶ Spec A` is the morphism represented by
`chartBaseHom`. -/
theorem representedChartToSpace_comp_hom :
    representedChartToSpace D.X.left U ≫ D.X.hom =
      representedSpaceMap D.B D.S D.containsLimitBase (D.chartBaseHom U) :=
  ObjectProperty.hom_ext _ (yoneda.map_preimage _).symm

/-- `chartBaseRingHom` is the ring map of `chartBaseHom` after `A ≅ Γ(Spec A, 𝒪)`. -/
theorem chartBaseRingHom_eq :
    D.chartBaseRingHom U = (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
      (D.chartBaseHom U)).hom.comp (Scheme.ΓSpecIso (limit D.system)).inv.hom :=
  rfl

/-- The ring map `Γ(Spec A, 𝒪) ⟶ Γ(Spec Aₙ, 𝒪)` of the projection to level `n` is `A ⟶ Aₙ`, through
`R ≅ Γ(Spec R, 𝒪)`. -/
theorem baseObjectProjection_ringHom_comp :
    (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
        (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom.comp
        (Scheme.ΓSpecIso (limit D.system)).symm.commRingCatIsoToRingEquiv.toRingHom =
      (Scheme.ΓSpecIso (D.system.obj (op n))).symm.commRingCatIsoToRingEquiv.toRingHom.comp
        (limit.π D.system (op n)).hom :=
  (congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (limit.π D.system (op n)))).symm

/-- The projection `A ⟶ Aₙ`, read on `Γ(Spec -, 𝒪)`, is surjective. -/
theorem surjective_baseObjectProjection_ringHom :
    Function.Surjective (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom := by
  have h := congrArg (fun f : (limit D.system : CommRingCat) →+* _ => ⇑f)
    (D.baseObjectProjection_ringHom_comp n)
  intro y
  obtain ⟨a, ha⟩ := GrothendieckExistence.surjective_limit_π D.system D.transition_surjective n
    ((Scheme.ΓSpecIso (D.system.obj (op n))).hom y)
  refine ⟨(Scheme.ΓSpecIso (limit D.system)).inv a, ?_⟩
  have := congrFun h a
  simp only [RingHom.coe_comp, Function.comp_apply] at this
  refine this.trans ?_
  change (Scheme.ΓSpecIso (D.system.obj (op n))).inv ((limit.π D.system (op n)) a) = y
  rw [ha]
  exact (Scheme.ΓSpecIso (D.system.obj (op n))).hom_inv_id_apply y

variable [IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
    ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U))]
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
  (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)

/-- The data of the chart `U` entering the base change map `c_U` at level `n`: the chart
morphism is étale, quasi-compact and quasi-separated, and the chart is a quasi-compact and
quasi-separated space. -/
theorem chartStage_hyps :
    IsEtale D.B D.S D.containsLimitBase (representedChartToSpace D.X.left U).hom ∧
    IsQuasiCompactSpace D.B D.S D.containsLimitBase
      (yoneda.obj ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U)) ∧
    IsAbsolutelyQuasiSeparated D.B D.S D.containsLimitBase D.B.contains_terminal
      (yoneda.obj ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U)) :=
  ⟨isEtale_representedChartToSpace D.X.left U,
    isQuasiCompactSpace_yoneda_of_isAffine D.B D.S D.containsLimitBase _ inferInstance,
    isAbsolutelyQuasiSeparated_yoneda_obj D.B D.S D.containsLimitBase D.B.contains_terminal _
      inferInstance⟩

/-- **`ψ_U` is invertible at the chart `U` and the stage `Xₙ`**: the instance of
`isIso_etaleTensorSectionsIdentification`, `U` being étale, hence flat, over `X` and so Tor
independent of `Xₙ`. -/
theorem isIso_chartTensorSectionsIdentification :
    IsIso (etaleTensorSectionsIdentification D.B D.S D.containsLimitBase
      (T := limitBaseObject D.system D.B D.containsLimitBase)
      (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
      (X := D.X.left) (X₀ := D.stage n) (U₀ := D.etaleStage n (representedChartToSpace D.X.left U))
      D.X.hom (D.stageToBase n)
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
      (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
      (D.F n) (D.isQuasicoherentOnSite_F n) (representedChartToSpace D.X.left U)
      (D.etaleStageInclusion n (representedChartToSpace D.X.left U))
      (D.etaleStageProjection n (representedChartToSpace D.X.left U))
      (D.isPullback_etaleStage n (representedChartToSpace D.X.left U)).flip.w
      (D.isQuasiCompact_isQuasiSeparated_of_isEtale (representedChartToSpace D.X.left U)
        (D.chartStage_hyps U).1 (D.chartStage_hyps U).2.1 (D.chartStage_hyps U).2.2).1
      (D.isQuasiCompact_isQuasiSeparated_of_isEtale (representedChartToSpace D.X.left U)
        (D.chartStage_hyps U).1 (D.chartStage_hyps U).2.1 (D.chartStage_hyps U).2.2).2
      (qcohDerived_singleFunctor_of_isQuasicoherentOnSite D.B D.S D.containsLimitBase
        (D.pushforwardModule n) (D.isQuasicoherentOnSite_pushforwardModule n))) := by
  have hj := (D.chartStage_hyps U).1
  have hjqc := (D.isQuasiCompact_isQuasiSeparated_of_isEtale (representedChartToSpace D.X.left U)
    (D.chartStage_hyps U).1 (D.chartStage_hyps U).2.1 (D.chartStage_hyps U).2.2).1
  have hjqs := (D.isQuasiCompact_isQuasiSeparated_of_isEtale (representedChartToSpace D.X.left U)
    (D.chartStage_hyps U).1 (D.chartStage_hyps U).2.1 (D.chartStage_hyps U).2.2).2
  have sqU := AlgebraicSpaces.isPullback_hom D.B D.S D.containsLimitBase
    (D.isPullback_etaleStage n (representedChartToSpace D.X.left U)).flip
  exact isIso_etaleTensorSectionsIdentification D.B D.S D.containsLimitBase
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₀ := D.stage n) (U₀ := D.etaleStage n (representedChartToSpace D.X.left U))
    D.X.hom (D.stageToBase n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) (representedChartToSpace D.X.left U)
    (D.etaleStageInclusion n (representedChartToSpace D.X.left U))
    (D.etaleStageProjection n (representedChartToSpace D.X.left U)) hjqc hjqs
    (qcohDerived_singleFunctor_of_isQuasicoherentOnSite D.B D.S D.containsLimitBase
      (D.pushforwardModule n) (D.isQuasicoherentOnSite_pushforwardModule n))
    (D.isPullback_etaleStage n (representedChartToSpace D.X.left U)).flip
    (isQuasiCompact_of_isPullback D.B D.S D.containsLimitBase sqU hjqc)
    (isQuasiSeparated_of_isPullback D.B D.S D.containsLimitBase sqU hjqs)
    (torIndependent_of_isFlat_left _ (D.closedImmersion n)
      (isFlat_of_isEtale D.B D.S D.containsLimitBase hj))

/-- **(a) of [Stacks, Tag 0CX9] on an affine étale chart, given [Stacks, Tag 0CX6] (1) at level
`n`**: `Hⁱ(RΓ(U, K) ⊗^𝐋_A Aₙ) = 0` for `i ≠ 0`, with `RΓ(U, K)` read over `A` along
`chartBaseRingHom`. -/
theorem isZero_homology_chartDerivedSections_of_isIso
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (D.system.obj (op n))) i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (limit.π D.system (op n)).hom).functor.obj
        ((ModuleCat.restrictScalars (D.chartBaseRingHom U)).mapDerivedCategory.obj
          (chartDerivedSections D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 U
            (D.coheratorObj DQ L))))) := by
  obtain ⟨hj, hUqc, hUqs⟩ := D.chartStage_hyps U
  obtain ⟨hjqc, hjqs⟩ := D.isQuasiCompact_isQuasiSeparated_of_isEtale
    (representedChartToSpace D.X.left U) hj hUqc hUqs
  have hc := D.isIso_etaleStageBaseChangeMap_of_isIso n (representedChartToSpace D.X.left U) hj
    hUqc hUqs hjqc hjqs adj p h0CX6
  have hzero := isZero_homology_extendScalars_derivedSections_of_isIso D.B D.S D.containsLimitBase
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₀ := D.stage n) (U₀ := D.etaleStage n (representedChartToSpace D.X.left U))
    D.X.hom (D.stageToBase n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) (D.isQuasicoherentOnSite_pushforwardModule n) U
    (D.chartBaseHom U) (D.representedChartToSpace_comp_hom U)
    (D.etaleStageInclusion n (representedChartToSpace D.X.left U))
    (D.etaleStageProjection n (representedChartToSpace D.X.left U))
    (D.isPullback_etaleStage n (representedChartToSpace D.X.left U)).flip hjqc hjqs
    (D.derivedLimitProjection adj p n) hc (D.isIso_chartTensorSectionsIdentification n U) i hi
  have h := StacksDraft.isZero_homology_extendScalars_restrictScalars_ringEquiv
    (Scheme.ΓSpecIso (limit D.system)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (D.system.obj (op n))).symm.commRingCatIsoToRingEquiv
    (limit.π D.system (op n)).hom _ (D.baseObjectProjection_ringHom_comp n) _ i hzero
  exact IsZero.of_iso h ((DerivedCategory.homologyFunctor _ i).mapIso
    ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (limit.π D.system (op n)).hom).functor.mapIso
      ((CochainComplex.DerivedExtensionScalars.derivedRestrictScalarsCompIso.{u, u}
        (Scheme.ΓSpecIso (limit D.system)).symm.commRingCatIsoToRingEquiv.toRingHom
        (representedAffineCommRingCatHom D.B D.S D.containsLimitBase (D.chartBaseHom U)).hom).app
          _).symm))

/-- (b) over `Γ(Spec A, 𝒪)`: the map `ψₙ`, read over `Γ(Spec A, 𝒪)`, is surjective with kernel
`ker(Γ(Spec A, 𝒪) → Γ(Spec Aₙ, 𝒪)) • ⊤`; the instance of
`surjective_and_ker_homology_derivedSections_map_of_isIso` at the chart and the stage `Xₙ`. -/
theorem surjective_and_ker_restrictScalars_chartDerivedSections_of_isIso
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (hle : ∀ i > 0, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).obj
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))))) :
    Function.Surjective ((DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).map
          (D.derivedLimitProjection adj p n))) ∧
      LinearMap.ker ((ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B D.S
          D.containsLimitBase (D.chartBaseHom U)).hom).map
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} ((structurePresheaf D.B D.S
            D.containsLimitBase D.X.left.1).obj (op U))) 0).map
          ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).map
            (D.derivedLimitProjection adj p n)))).hom =
        RingHom.ker (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom • ⊤ := by
  have hj := (D.chartStage_hyps U).1
  have hUqc := (D.chartStage_hyps U).2.1
  have hUqs := (D.chartStage_hyps U).2.2
  have hjqc := (D.isQuasiCompact_isQuasiSeparated_of_isEtale
    (representedChartToSpace D.X.left U) hj hUqc hUqs).1
  have hjqs := (D.isQuasiCompact_isQuasiSeparated_of_isEtale
    (representedChartToSpace D.X.left U) hj hUqc hUqs).2
  exact surjective_and_ker_homology_derivedSections_map_of_isIso D.B D.S D.containsLimitBase
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₀ := D.stage n) (U₀ := D.etaleStage n (representedChartToSpace D.X.left U))
    D.X.hom (D.stageToBase n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (D.closedImmersion_comp_hom n) (D.isAffineHom_closedImmersion n)
    (D.F n) (D.isQuasicoherentOnSite_F n) (D.isQuasicoherentOnSite_pushforwardModule n) U
    (D.chartBaseHom U) (D.representedChartToSpace_comp_hom U)
    (D.etaleStageInclusion n (representedChartToSpace D.X.left U))
    (D.etaleStageProjection n (representedChartToSpace D.X.left U))
    (D.isPullback_etaleStage n (representedChartToSpace D.X.left U)).flip hjqc hjqs
    (D.derivedLimitProjection adj p n)
    (D.isIso_etaleStageBaseChangeMap_of_isIso n (representedChartToSpace D.X.left U) hj
      hUqc hUqs hjqc hjqs adj p h0CX6) (D.isIso_chartTensorSectionsIdentification n U)
    (D.surjective_baseObjectProjection_ringHom n) hle

/-- **(b) of [Stacks, Tag 0CX9] on an affine étale chart, given [Stacks, Tag 0CX6] (1) at level
`n`**: if `RΓ(U, K)` has no cohomology in positive degrees, the map
`ψₙ : H⁰(RΓ(U, K)) ⟶ H⁰(RΓ(U, (iₙ,* Fₙ)[0]))` induced by `K ⟶ (iₙ,* Fₙ)[0]` is surjective
with kernel `(ker(A → Aₙ) Γ(U)) • H⁰(RΓ(U, K))`. -/
theorem surjective_and_ker_chartDerivedSections_of_isIso
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (hle : ∀ i > 0, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (chartDerivedSections D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 U
        (D.coheratorObj DQ L)))) :
    Function.Surjective ((DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).map
          (D.derivedLimitProjection adj p n))) ∧
      LinearMap.ker ((DerivedCategory.homologyFunctor _ 0).map
        ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).map
          (D.derivedLimitProjection adj p n))).hom =
        (Ideal.map (D.chartBaseRingHom U) (RingHom.ker (limit.π D.system (op n)).hom)) • ⊤ := by
  have hb := D.surjective_and_ker_restrictScalars_chartDerivedSections_of_isIso n U adj p h0CX6
    hle
  let e := (Scheme.ΓSpecIso (limit D.system)).symm.commRingCatIsoToRingEquiv
  let e₀ := (Scheme.ΓSpecIso (D.system.obj (op n))).symm.commRingCatIsoToRingEquiv
  have e3 : RingHom.ker (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom =
      (RingHom.ker (limit.π D.system (op n)).hom).map e.toRingHom := by
    rw [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv]
    ext z
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.mem_ker]
    have h := congrArg (fun f : (limit D.system : CommRingCat) →+* _ => f (e.symm z))
      (D.baseObjectProjection_ringHom_comp n)
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at h
    rw [show e (e.symm z) = z from e.apply_symm_apply z] at h
    rw [h]
    exact RingEquiv.map_eq_zero_iff e₀
  have hI : Ideal.map (D.chartBaseRingHom U) (RingHom.ker (limit.π D.system (op n)).hom) =
      Ideal.map (representedAffineCommRingCatHom D.B D.S D.containsLimitBase (D.chartBaseHom U)).hom
        (RingHom.ker (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom) := by
    rw [e3, Ideal.map_map, chartBaseRingHom_eq]
    rfl
  refine ⟨hb.1, ?_⟩
  refine Eq.trans ?_ (congrArg (· • ⊤) hI.symm)
  ext y
  exact (SetLike.ext_iff.mp hb.2 y).trans (ModuleCat.mem_smul_top_restrictScalars_iff
    (representedAffineCommRingCatHom D.B D.S D.containsLimitBase (D.chartBaseHom U)).hom _
    (RingHom.ker (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)).hom) y)

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
