module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Flat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautMorphismRepresentabilityRefined
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.CoveringSetOfObjects
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletionOverNoetherian
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatLocalPropertyRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SourceCoverImpliesEveryDiagram

/-!
# Flatness of morphisms of locally Noetherian formal algebraic spaces: refined forms

Strengthened forms of declarations of
`StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterization`, under primed names (the
originals keep their statements there), together with the new lemmas they need.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

/-- Every ring of `WAdm^{Noeth}` is weakly admissible with a countable fundamental system of
open ideals: weak admissibility is `TopologicalRing.IsAdic.isWeaklyAdmissible`, and the powers
of an ideal of definition are a countable basis of the neighbourhoods of zero. This is the `hCwa`
input of `FormalSpace.hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap` at
the class of Stacks 0ANI. -/
theorem isWeaklyAdmissible_and_isCountablyGenerated_of_isNoetherianAdic (R : Type u)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : IsNoetherianAdic R) :
    IsWeaklyAdmissible R ∧ (nhds (0 : R)).IsCountablyGenerated :=
  ⟨hR.1.isWeaklyAdmissible, Rig.countablyGenerated_nhds_of_isAdicRing hR.1⟩

/-- `WAdm^{Noeth}` is closed under the completion of **Stacks 0AN6** along an étale ring map.
This is the `hCcomp` input of the two locality-axiom theorems of Stacks 0ANG at the class of
Stacks 0ANI. The clause of **Stacks 0ANB** for that class,
`TopologicalRing.completionOver_isNoetherianAdic`, asks the ring being completed to be
Noetherian, and that is where étaleness enters: an étale algebra is of finite presentation,
hence of finite type, so it is Noetherian over a Noetherian base. -/
theorem isNoetherianAdic_completionOver_of_etale {X Y : Type u} [CommRing X]
    [TopologicalSpace X] [IsTopologicalRing X] [IsLinearTopology X X] [CommRing Y]
    (φ : X →+* Y) (het : φ.Etale) (hX : IsNoetherianAdic X) :
    IsNoetherianAdic (CompletionOver φ) := by
  have hXn : IsNoetherianRing X := hX.2
  let : Algebra X Y := φ.toAlgebra
  have hetale : Algebra.Etale X Y := het
  have : Algebra.FinitePresentation X Y := hetale.finitePresentation
  exact completionOver_isNoetherianAdic φ hX (Algebra.FiniteType.isNoetherianRing X Y)

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (C : ∀ (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLinearTopology R R], Prop)
  (P : ∀ {R₁ R₂ : Type u} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂], (R₁ →+* R₂) → Prop)

/-! ### The locality axioms of Situation 0CBA for flatness on `WAdm^{Noeth}` -/

/-- **Axiom (1) of Situation 0CBA for flatness, read on affine formal algebraic spaces.**
Flatness is a local property of arrows of `WAdm^{Noeth}` by **Stacks 0GC9**, and `WAdm^{Noeth}`
is closed under the completion of Stacks 0AN6 along an étale ring map by **Stacks 0ANB**; those
are the two inputs of `hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap`. -/
theorem chartPropertyAscendsAlongAffineEtale_flat :
    ChartPropertyAscendsAlongAffineEtale' B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom :=
  fun _ _ _ _ _ _ _ _ _ _ _ hloc ht ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleLocalizationOfChartMap B S hS _ _
      TopologicalRing.flat_isLocalNoetherian'.{u}.toPropertyIsLocal
      TopologicalRing.flat_isLocalNoetherian'.{u}.isomorphismInvariant
      (fun φ _ het hC ↦ TopologicalRing.isNoetherianAdic_completionOver_of_etale φ het hC) hloc ht

/-- **Axioms (2) and (3) of Situation 0CBA for flatness, read on affine formal algebraic
spaces.** The three inputs of
`hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap` are the locality of
**Stacks 0GC9**, membership of `WAdm^{Noeth}` implying weak admissibility with countably
generated neighbourhoods of zero, and the closure of `WAdm^{Noeth}` under the completion of
Stacks 0AN6 by **Stacks 0ANB**. -/
theorem chartPropertyDescendsAlongFiniteAffineEtaleCover_flat :
    ChartPropertyDescendsAlongFiniteAffineEtaleCover' B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom :=
  fun t _ _ _ _ W Z _ m _ _ _ _ _ hcover hPm ↦
    hasPropertyOnAffineChartMap_of_isCompletedEtaleFiniteCoverOfChartMap B S hS _ _
      TopologicalRing.flat_isLocalNoetherian'.{u}.toPropertyIsLocal
      TopologicalRing.flat_isLocalNoetherian'.{u}.isomorphismInvariant
      (fun R _ _ _ _ hC ↦
      TopologicalRing.isWeaklyAdmissible_and_isCountablyGenerated_of_isNoetherianAdic R hC)
      (fun φ _ het hC ↦ TopologicalRing.isNoetherianAdic_completionOver_of_etale φ het hC)
      t W Z m hcover hPm

/-- **Stacks 0GCD.** For a morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
over `S`, flatness of `f` in the sense of Definition 0GCC, the condition that every affine
representable étale square over `f` carry a flat map of Noetherian adic topological rings, the
existence of an affine étale covering of `Y` together with affine étale coverings of the fibre
products of its members with `X` on which that condition holds, and the existence of an affine
étale covering of `X` whose members factor flatly through affine representable étale charts of
`Y`, are all equivalent.

The first two conditions agree by Definition 0GCC, as in the source's own proof; the last three
are the three conditions of Stacks 0ANG for the class of Noetherian adic topological rings and
flatness, which is a local property of such arrows by Stacks 0GC9.

Stacks 0AJ3, that the fibre product of a chart of `Y` with `f` is a formal algebraic space, is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`,
and the locality axioms of Situation 0CBA for flatness, read on affine formal algebraic spaces
through Stacks 0AN8 and Stacks 0AN9, are
`AlgebraicGeometry.FormalSpace.chartPropertyAscendsAlongAffineEtale_flat` and
`AlgebraicGeometry.FormalSpace.chartPropertyDescendsAlongFiniteAffineEtaleCover_flat`; none of
the three is a hypothesis. The one input still carried is `href`, the presented étale
refinement of a covering of the source.

The two ends of `f` are asked only to be *locally countably indexed*, which is weaker than the
source's locally Noetherian — a locally Noetherian formal algebraic space is locally countably
indexed by items (1), (2), (3) and (5) of Stacks 0AIK — and is the standing hypothesis that the
variant of Stacks 0ANG for the Noetherian class, Remark 0ANI, inherits from Stacks 0ANG itself
and that `href` consumes. -/
theorem isFlat_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (href : HasEtaleRefinementOfSourceCover' B S hS TopologicalRing.IsNoetherianAdic f) :
    List.TFAE
      [IsFlat B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f] := by
  tfae_have 1 ↔ 2 := isFlat_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  tfae_have 3 → 4 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f h
  tfae_have 4 → 2 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom f hX hY
    (chartPropertyAscendsAlongAffineEtale_flat B S hS)
    (chartPropertyDescendsAlongFiniteAffineEtaleCover_flat B S hS) href h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
