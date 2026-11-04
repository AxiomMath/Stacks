module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeOnReductionsCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentabilityRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.FiniteTypeOnReductionsIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.LocalPropertyClassClosure
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram

/-!
# Characterising finite type on reductions on affine charts

For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic spaces over `S`, the
property of Stacks 0GC2 on arrows of countably indexed weakly admissible topological rings holding
on every affine étale square, after an affine étale covering of the target, or after an affine
étale covering of the source, is equivalent to the morphism of reductions being locally of finite
type.

## Main results

* `chartPropertyAscendsAlongAffineEtale_finiteTypeOnReductions`: The property of Stacks 0GC2
  ascends along affine étale maps of charts.
* `chartPropertyDescendsAlongFiniteAffineEtaleCover_finiteTypeOnReductions`: The property of
  Stacks 0GC2 descends along finite affine étale coverings of charts.
* `isLocallyOfFiniteTypeOnReductions_tfae'`: The four conditions of Stacks 0GC7 are equivalent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TopologicalRing

universe u

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The locality axioms of Situation 0CBA for the property of Stacks 0GC2 -/

/-- **Axiom (1) of Situation 0CBA for the property of Stacks 0GC2, read on affine formal
algebraic spaces.** The property ascends along affine étale maps of charts. -/
theorem chartPropertyAscendsAlongAffineEtale_finiteTypeOnReductions :
    ChartPropertyAscendsAlongAffineEtale' B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ hloc ht ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap B S hS _ _
      TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal'.{u}.toPropertyIsLocal
      TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal'.{u}.isomorphismInvariant
      (fun φ _ _ hC ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hC) hloc ht

/-- **Axioms (2) and (3) of Situation 0CBA for the property of Stacks 0GC2, read on affine
formal algebraic spaces.** The property descends along finite affine étale coverings of
charts. -/
theorem chartPropertyDescendsAlongFiniteAffineEtaleCover_finiteTypeOnReductions :
    ChartPropertyDescendsAlongFiniteAffineEtaleCover' B S hS
      TopologicalRing.IsCountablyWeaklyAdmissible
      TopologicalRing.FiniteTypeOnReductionsProperty :=
  fun t _ _ _ _ W Z _ m _ _ _ _ _ hcover hPm ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap B S hS _ _
      TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal'.{u}.toPropertyIsLocal
      TopologicalRing.isFiniteTypeOnReductions_propertyIsLocal'.{u}.isomorphismInvariant
      (fun _ _ _ _ _ hC ↦ hC)
      (fun φ _ _ hC ↦ TopologicalRing.isCountablyWeaklyAdmissible_completionOver φ hC)
      t W Z m hcover hPm

/-! ### Stacks 0GC7 -/

variable {B S hS}

/-- **Stacks 0GC7.** For a morphism `f : X ⟶ Y` of locally countably indexed formal algebraic
spaces over `S`, the condition that every affine representable étale square over `f` carry an
arrow of `WAdm^{count}` with the property of Stacks 0GC2, the existence of an affine étale
covering of `Y` together with affine étale coverings of the fibre products of its members with
`X` on which that condition holds, the existence of an affine étale covering of `X` whose
members factor through affine representable étale charts of `Y` by such arrows, and the morphism
of reductions `f_red` being locally of finite type, are all equivalent. -/
theorem isLocallyOfFiniteTypeOnReductions_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hbridge : ChartPropertyIsFiniteTypeOnReductions B S hS)
    (hredsquare : IsLocallyOfFiniteTypeOnReductionsOnEveryAffineEtaleSquare B S hS)
    (hredcover : IsLocallyOfFiniteTypeOnReductionsOfTargetCover B S hS) :
    List.TFAE
      [HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsCountablyWeaklyAdmissible
          TopologicalRing.FiniteTypeOnReductionsProperty f,
        IsLocallyOfFiniteTypeOnReductions B S hS f] := by
  have href := hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible B S hS f
  have h0AKX := isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS
  tfae_have 1 → 2 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f h
  tfae_have 3 → 1 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS
    TopologicalRing.IsCountablyWeaklyAdmissible
    TopologicalRing.FiniteTypeOnReductionsProperty f hX hY
    (chartPropertyAscendsAlongAffineEtale_finiteTypeOnReductions B S hS)
    (chartPropertyDescendsAlongFiniteAffineEtaleCover_finiteTypeOnReductions B S hS) href h
  tfae_have 2 → 4 := by
    rintro ⟨J, V, v, hVcover, hinner⟩
    refine hredcover f ⟨J, V, v, hVcover, fun j ↦ ?_⟩
    obtain ⟨I, U, w, hUcover, hUproperty⟩ := hinner j
    refine ⟨I, U, w, hUcover, fun i ↦ ?_⟩
    have hsnd : IsRepresentableEtale B S hS (w i ≫ pullback.snd (v j) f) :=
      IsRepresentableEtale.comp B S hS (hUcover.2.1 i)
        (isRepresentableEtale_pullback_snd B S hS (v j) f (hVcover.2.1 j))
    exact (hbridge (w i ≫ pullback.fst (v j) f) (hUcover.1 i) (hVcover.1 j)
      (h0AKX X hX (U i) (w i ≫ pullback.snd (v j) f) (hUcover.1 i) hsnd)
      (h0AKX Y hY (V j) (v j) (hVcover.1 j) (hVcover.2.1 j))).2 (hUproperty i)
  tfae_have 4 → 1 := by
    intro hf U V a b t hU hV ha hb hsq
    exact (hbridge t hU hV (h0AKX X hX U a hU ha) (h0AKX Y hY V b hV hb)).1
      (hredsquare f a b t hU hV ha hb hsq hf)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
