module

public import StacksFrontier.RingTheory.TwistedSquareZeroSystem
public import StacksFrontier.Topology.Algebra.AdicTopology.QuotientDirectedLimit

/-!
# The weakly admissible ring behind the twisted system

The target of the morphism of Stacks 0CBE — the second sense of the warning of Stacks 0AN7 — is
the formal spectrum of a weakly admissible topological ring. This file produces that ring from
the system of stage rings of `StacksFrontier.RingTheory.TwistedSquareZeroSystem`.

The input is exactly what that file proves about the target: one fixed ring `Lam I` surjects
compatibly onto every stage ring `StageRing b`, and the transition maps of the stage rings have
locally nilpotent — indeed square-zero — kernels. Feeding those to
`TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family` gives a weakly admissible
ring `A`, in the same universe as the stage rings, whose projections to the stages are
surjective and whose kernels are weak ideals of definition forming a fundamental system of
neighbourhoods of `0`.

Two consequences of that last clause are what the geometry needs. The kernels of the
projections are **cofinal** among the weak ideals of definition of `A`, so a quasi-compact point
of `Spf A` factors through one of the stages that the source of the morphism is indexed by; and
the stage of `Spf A` at `RingHom.ker (π b)` is `Spec (StageRing b)`, so the two presentations
run over the same rings.

Surjectivity of the projections is also exactly McQuillan's criterion for the target, read at
the level of rings: a single ring surjects onto every stage of the presentation. The geometric
form of that statement is
`AlgebraicGeometry.FormalSpace.hasSurjectiveSectionProjections_of_surjective_family`, which
needs a site and so belongs with the construction of the two formal spaces rather than here.

## Main results

* `Stacks.Coherent.exists_isWeaklyAdmissible_stageRing`: the inverse limit of the stage rings is
  a weakly admissible topological ring with surjective projections onto the stages, whose
  kernels are weak ideals of definition basing the topology.

## Implementation notes

The index of the limit is not `I` but the set of kernels of the given surjections, which is why
the ring produced lives in the universe of `Lam I` rather than in that of `I`; this is the whole
point of `TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family` and it matters
here because the geometry needs the stage rings to be small for the site.

Nothing about the twist enters. The twist is carried by the *source* of the morphism, whose
stage rings are the dual numbers over these, and the target is McQuillan precisely because no
twist obstructs the surjections out of `Lam I`.
-/

@[expose] public noncomputable section

namespace Stacks.Coherent

universe u

variable {I : Type u} [LinearOrder I] [WellFoundedLT I]

/-- **The target ring.** The inverse limit of the stage rings is a weakly admissible topological
ring in their own universe, with surjective projections onto the stages whose kernels are weak
ideals of definition forming a fundamental system of neighbourhoods of zero.

The hypotheses are discharged by the target half of
`StacksFrontier.RingTheory.TwistedSquareZeroSystem`: the transitions of the stage rings have
square-zero kernels, and one fixed ring surjects compatibly onto every stage. -/
theorem exists_isWeaklyAdmissible_stageRing [Nonempty I] :
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsLinearTopology A A) (π : ∀ b : I, A →+* StageRing b),
      TopologicalRing.IsWeaklyAdmissible A ∧
        (∀ b : I, Function.Surjective (π b)) ∧
        (∀ ⦃b a : I⦄ (h : b ≤ a) (x : A), stageRingMap h (π a x) = π b x) ∧
        (∀ b : I, TopologicalRing.IsWeakIdealOfDefinition (RingHom.ker (π b))) ∧
        (nhds (0 : A)).HasBasis (fun _ : I ↦ True)
          (fun b ↦ (RingHom.ker (π b) : Set A)) :=
  TopologicalRing.exists_isWeaklyAdmissible_proj_of_surjective_family
    (τ := fun {_ _} h ↦ stageRingMap h) (ρ := lamProj)
    (fun {_ _} h ↦ locallyNilpotent_ker_stageRingMap h) lamProj_surjective
    fun {_ _} h x ↦ stageRingMap_comp_lamProj h x

end Stacks.Coherent

end
