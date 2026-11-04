module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ChartStageSections
public import
  StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.ExistenceNeighbourhoodOfCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartLocalVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.HomologyZeroTransposeChartIso

/-!
# The existence neighbourhood of a derived limit of flat sheaves

In Situation [Stacks, Tag 0CX4] let `K = DQ_X(L)` be the object of [Stacks, Tag 0CX5], for a
coherator `adj : ι ⊣ DQ_X` and a presentation `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` of `L` as the derived
limit of `(iₙ,* Fₙ)`. Given

* [Stacks, Tag 0CX6] (1): the base change maps `RΓ(X, E ⊗^𝐋 K) ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)`
  are isomorphisms for perfect `E` (the hypothesis `h0CX6`), and
* [Stacks, Tag 0CX7]: `K` is pseudo-coherent relative to `A` (the hypothesis `h0CX7`),

there is an open subspace `W ⊂ X` containing `X₀` on which `Hⁱ(K) = 0` for `i ≠ 0`,
`H⁰(K)` is of finite presentation, and `H⁰(K) ⊗ 𝒪_{Xₙ} ≅ Fₙ` through the canonical map.

## Main results

In the namespace `AlgebraicGeometry.Space.FlatSheafExistenceSituation`:

* `isZero_homology_extendScalars_chartDerivedSections_of_isIso`: on an affine étale chart, given
  [Stacks, Tag 0CX6] (1) at level `n`, `Hⁱ(RΓ(U, K) ⊗^𝐋 Γ(Spec Aₙ, 𝒪)) = 0` for `i ≠ 0`.
* `exists_isExistenceNeighbourhood_of_isIso_of_isRelativelyPseudoCoherent`: the existence of the
  open subspace `W`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry.GrothendieckExistence (limitBase)

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasRightDerivedFunctor_chartSections

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})
  {DQ : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory}
  (adj : (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ DQ)
  {L : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left}
  (p : L ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩)

/-- On an affine étale chart `U`, given [Stacks, Tag 0CX6] (1) at level `n`,
`Hⁱ(RΓ(U, K) ⊗^𝐋 Γ(Spec Aₙ, 𝒪)) = 0` for `i ≠ 0`. -/
theorem isZero_homology_extendScalars_chartDerivedSections_of_isIso (n : ℕ)
    (U : SmallEtale D.B D.S D.containsLimitBase D.X.left.1)
    [IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U))]
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (baseObjectProjection D.system D.B D.containsLimitBase
            D.containsBaseAt n)).hom).functor.obj
        ((ModuleCat.restrictScalars (representedAffineCommRingCatHom D.B D.S D.containsLimitBase
          (D.chartBaseHom U)).hom).mapDerivedCategory.obj
          ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
            (Stacks.SheafOfModules.Tensor.ringSheaf
              (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) U).obj
            ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj
              (DQ.obj L)))))) := by
  have hj := (D.chartStage_hyps U).1
  have hUqc := (D.chartStage_hyps U).2.1
  have hUqs := (D.chartStage_hyps U).2.2
  have hjqc := (D.isQuasiCompact_isQuasiSeparated_of_isEtale
    (representedChartToSpace D.X.left U) hj hUqc hUqs).1
  have hjqs := (D.isQuasiCompact_isQuasiSeparated_of_isEtale
    (representedChartToSpace D.X.left U) hj hUqc hUqs).2
  have hc := D.isIso_etaleStageBaseChangeMap_of_isIso n (representedChartToSpace D.X.left U) hj
    hUqc hUqs hjqc hjqs adj p h0CX6
  exact isZero_homology_extendScalars_derivedSections_of_isIso D.B D.S D.containsLimitBase
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

/-- Given [Stacks, Tag 0CX6] (1) at level `n`, the comparison `D.stageComparison` at level `n`
is an isomorphism on the charts above an affine chart `c` without positive cohomology of
`RΓ(c, K)`. -/
theorem isIso_stageComparison_val_app_of_isIso (n : ℕ)
    (c : SmallEtale D.B D.S D.containsLimitBase D.X.left.1)
    (hc : IsAffineChart D.B D.S D.containsLimitBase D.X.left.1 c)
    (h0CX6 : ∀ E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left,
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (hle : ∀ i > 0, IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2).O) c).obj
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L)))))
    (T : SmallEtale D.B D.S D.containsLimitBase (D.stage n).1)
    (f : T ⟶ (smallBaseChange D.B D.S D.containsLimitBase (D.closedImmersion n)
      (D.isClosedImmersion_closedImmersion n).rep).obj c) :
    IsIso ((D.stageComparison ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj
      (DQ.obj L)) (D.derivedLimitProjection adj p) n).val.app (op T)) := by
  have : IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj c)) := hc
  have hb := D.surjective_and_ker_restrictScalars_chartDerivedSections_of_isIso n c adj p h0CX6 hle
  exact isIso_homologyZeroTranspose_val_app_of_chart (B := D.B) (S := D.S)
    (hS := D.containsLimitBase)
    (T := limitBaseObject D.system D.B D.containsLimitBase)
    (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    D.X.hom.hom (D.stageToBase n).hom
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion n) (congrArg (fun k => k.hom) (D.closedImmersion_comp_hom n))
    (D.isClosedImmersion_closedImmersion n) (D.isAffineHom_closedImmersion n)
    ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))
    (DQ.obj L).property (D.F n) (D.isQuasicoherentOnSite_F n)
    (D.derivedLimitProjection adj p n) c hc hb.1 hb.2 T f

/-- For a coherator `adj : ι ⊣ DQ_X` and a presentation `L ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ L[1]` of the derived
limit `L` of `(iₙ,* Fₙ)`, with `K = DQ_X(L)` and its canonical maps `K ⟶ Fₙ`: if the base change
maps of [Stacks, Tag 0CX6] (1) are isomorphisms and `K` is pseudo-coherent relative to `A`, there
is an open subspace `W` of `X` containing `X₀` such that `Hⁱ(K)|_W = 0` for `i ≠ 0`, `H⁰(K)|_W`
is of finite presentation, and `H⁰(K)|_W ⊗ 𝒪_{Xₙ} ≅ Fₙ` on `W ×_X Xₙ` through the canonical
maps. -/
theorem exists_isExistenceNeighbourhood_of_isIso_of_isRelativelyPseudoCoherent
    (hp : ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
          D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left))
    (h0CX6 : ∀ (n : ℕ) (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left),
      spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E →
        IsIso (D.limitTensorSectionsBaseChangeMap adj L E p n))
    (h0CX7 : IsRelativelyPseudoCoherent D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2
      D.X.hom.hom D.isLocallyOfFiniteType_structureMorphism (D.coheratorObj DQ L)) :
    ∃ (W : Subfunctor D.X.left.1) (hW : IsOpenSubspace D.B D.S D.containsLimitBase W),
      D.IsExistenceNeighbourhood
        ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))
        (D.derivedLimitProjection adj p) W hW := by
  have hL : IsDerivedLimit D.derivedSystem L := ⟨p, hp⟩
  have hKb := ((D.derivedLimit_bounded.2.2.1 DQ adj L hL).2.1)
  have hT : IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
      (limitBaseObject D.system D.B D.containsLimitBase)) :=
    inferInstanceAs (IsAffine (limitBase D.system))
  have hloc := fun (x : points D.B D.S D.containsLimitBase D.X.left.1)
      (hx : x ∈ D.pointsOverFirstStage) =>
    exists_affineChart_vanishing_of_isRelativelyPseudoCoherent D.B D.S D.containsLimitBase
      D.X.left (T := limitBaseObject D.system D.B D.containsLimitBase)
      (T₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt 0) (hT := hT)
      D.X.hom.hom D.isLocallyOfFiniteType_structureMorphism
      (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt 0)
      (D.surjective_baseObjectProjection_ringHom 0)
      ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))
      (DQ.obj L).property hKb h0CX7
      (fun U hU i hi =>
        have : IsAffine ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).obj
          ((SmallEtale.toOver D.B D.S D.containsLimitBase D.X.left.1).obj U)) := hU
        D.isZero_homology_extendScalars_chartDerivedSections_of_isIso adj p 0 U (h0CX6 0) i
          (ne_of_gt hi))
      x hx
  choose c hcA hcx h1 h2 hle using hloc
  let c' : D.pointsOverFirstStage → SmallEtale D.B D.S D.containsLimitBase D.X.left.1 :=
    fun x => c x.1 x.2
  refine ⟨D.chartsNeighbourhood c', D.isOpenSubspace_chartsNeighbourhood c',
    D.isExistenceNeighbourhood_chartsNeighbourhood c'
      ((spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.obj (DQ.obj L))
      (DQ.obj L).property (D.derivedLimitProjection adj p)
      (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hcx x hx⟩)
      (fun i hi j T f => h1 j.1 j.2 i hi T f) (fun j T hT f => h2 j.1 j.2 T hT f)
      (fun n j T f => D.isIso_stageComparison_val_app_of_isIso adj p n (c' j) (hcA j.1 j.2)
        (h0CX6 n) (hle j.1 j.2) T f)⟩

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
