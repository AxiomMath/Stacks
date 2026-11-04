module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleStabilityRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined

/-!
# Characterising rig-étale morphisms of formal algebraic spaces on affine charts: the refined forms

The strengthened and newly added declarations of the 2026-10 chapter-87 round that
belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleCharacterization`. A declaration
of that module whose statement the round strengthened keeps its original statement there; its
strengthened form lives here under a primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopologicalRing

end TopologicalRing

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GCZ.** For a morphism `f : X ⟶ Y` of locally Noetherian formal algebraic spaces
over `S`, rig-étaleness of `f` in the sense of Definition 0AQM, the condition that every
affine representable étale square over `f` carry a rig-étale arrow of `WAdm^{Noeth}`, the
existence of an affine étale covering of `Y` together with affine étale coverings of the fibre
products of its members with `X` on which that condition holds, and the existence of an affine
étale covering of `X` whose members factor rig-étalely through affine representable étale
charts of `Y`, are all equivalent.

The first two conditions agree by Definition 0AQM, as in the source's own proof; the last
three are the three conditions of Stacks 0ANG for the class of Noetherian adic topological
rings and rig-étaleness, which is a local property of such arrows by Stacks 0AQL read in the
Noetherian form of Remark 0ANI. Stacks 0AJ3, that the fibre product of a chart of `Y` with `f`
is a formal algebraic space, is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace`
and is no longer a hypothesis. The hypotheses `href`, `hasc` and `hdesc` carry the covering
refinement of Stacks 0AJ2 at the class `WAdm^{Noeth}` and the locality axioms of Situation
0CBA read through Stacks 0AN8 and Stacks 0AN9. The library's only producer of the refinement,
`AlgebraicGeometry.FormalSpace.hasEtaleRefinementOfSourceCover_isCountablyWeaklyAdmissible`,
is at `WAdm^{count}`, and the library's Stacks 0AQL, `Rig.rigEtale_isLocalNoetherian'`, is
itself conditional on the locality of the annihilation half of rig-étaleness, so neither can
be used here.

The two ends of `f` are asked only to be *locally countably indexed*, which is weaker than the
source's locally Noetherian — a locally Noetherian formal algebraic space is locally countably
indexed by items (1), (2), (3) and (5) of Stacks 0AIK — and is the standing hypothesis that the
variant of Stacks 0ANG for the Noetherian class, Remark 0ANI, inherits from Stacks 0ANG itself
and that `href` consumes. -/
theorem isRigEtale_tfae' {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsLocallyCountablyIndexed B S hS Y)
    (hasc : ChartPropertyAscendsAlongAffineEtale' B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (hdesc : ChartPropertyDescendsAlongFiniteAffineEtaleCover' B S hS
      TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom)
    (href : HasEtaleRefinementOfSourceCover' B S hS TopologicalRing.IsNoetherianAdic f) :
    List.TFAE
      [IsRigEtale B S hS f,
        HasPropertyOnEveryAffineEtaleDiagram B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f,
        HasPropertyAfterTargetCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f,
        HasPropertyAfterSourceCover B S hS
          TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f] := by
  tfae_have 1 ↔ 2 := isRigEtale_iff_hasPropertyOnEveryAffineEtaleDiagram B S hS f
  tfae_have 2 → 3 := fun h ↦ hasPropertyAfterTargetCover_of_everyAffineEtaleDiagram B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f hY.1
    (fun _V v' hV' _ ↦ isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS
      v' f hY.1 hV' hX.1) h
  tfae_have 3 → 4 := fun h ↦ hasPropertyAfterSourceCover_of_afterTargetCover B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f h
  tfae_have 4 → 2 := fun h ↦ hasPropertyOnEveryAffineEtaleDiagram_of_afterSourceCover' B S hS
    TopologicalRing.IsNoetherianAdic TopologicalRing.IsRigEtaleHom f hX hY hasc hdesc href h
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
