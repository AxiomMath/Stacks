module

public import StacksFrontier.Topology.Sheaves.Cohomology.SheafedSpaceLimits.AbelianLimitCone
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.VanishingFromCechAcyclicity
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitDegreeInduction.InjectiveEmbedding
public import StacksFrontier.Topology.Sheaves.Cohomology.SpectralLimitVertex.SectionsOnTheVertex

/-!
# The effacing system of the degree induction of Tag 0A37

The degree induction of Stacks 0A37 — "arguing exactly as in the proof of Lemma 01FF" — compares
two δ-functors on systems of abelian sheaves over a fixed cofiltered diagram of spectral spaces:
the stage side `𝒜 ↦ colimₐ Hᵖ(fₐ⁻¹Uᵢ, 𝒜ₐ)` and the limit side `𝒜 ↦ Hᵖ(pᵢ⁻¹Uᵢ, colimⱼ pⱼ⁻¹𝒜ⱼ)`.
`CategoryTheory.DeltaFunctor.isIso_app_of_isIso_app_zero`
(`StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.Comparison`) runs that induction on two inputs:
an isomorphism in degree zero, and, for every system, a monomorphism into a system that **both**
sides kill in every positive degree.

**This file supplies the second input**, assembled from three existing statements:

* `SpectralAbelianSheafSystem.exists_mono_injectiveSystem` embeds a system in a stagewise
  injective one over the *same* diagram of spaces;
* `Stacks.Cohomology.AbelianBasis.isZero_H'_succ_of_injective` kills the stage side, since
  positive-degree cohomology of an injective abelian sheaf vanishes over every open, hence after
  taking the colimit;
* `SpectralAbelianSheafSystem.isZero_H'_succ_conePoint_of_injective'` kills the limit side — the
  genuinely non-formal half, Čech acyclicity of the sheaf on the vertex.

The limiting cone of the envelope system is produced by
`SpectralDiagram.AbelianSystem.isLimit`, which is why the envelope has to be an `AbelianSystem`
over the fixed diagram rather than a second bundled system: the two cones then lie over one cone
of spaces, and the quasi-compact stage open and its preimage are shared with no transport.

## Main results

* `SpectralAbelianSheafSystem.exists_effacingSystem`: the effacing system, its limiting cone, and
  the two vanishing statements.

## Implementation notes

The statement is phrased in the envelope's own spelling — opens of
`G.toSpectralAbelianSheafSystem.E.obj j`, and the open
`(G.toSpectralAbelianSheafSystem.stageOpenCone cG i U).pt` on the vertex of `cG` — rather than in
the original system's. Nothing is lost and nothing has to be transported: the two systems have
the same diagram of spaces by `rfl`
(`toSpectralAbelianSheafSystem_baseDiagram_eq`), the vertex of `cG` carries the same space as the
vertex of `c` because `cG` lies over `(SheafedSpace.forget _).mapCone c`
(`SpectralDiagram.AbelianSystem.mapCone_forget_cone`), and the projections agree by `rfl`
(`SpectralDiagram.AbelianSystem.cone_base`), so the two opens `pᵢ⁻¹U` coincide on the nose.  What
differs between the two systems is only the sheaves, which is the point.

The universes are all equal, as in every statement of this development that mentions
`SpectralAbelianSheafSystem.typeSystem`; the narrowing is inherited from the inputs. See the
universe verdict in the implementation notes of
`StacksDraft.Ch20.Sec16.Tag0A37ColimitComparison`.

## References

* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

open Stacks.Cohomology Stacks.Cohomology.SpectralLimit

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- **The effacing system of the degree induction of Stacks 0A37.**  For a bundled system `S`, a
limiting cone `c` of its spaces-with-sheaves, a stage `i` and a quasi-compact open `U` of that
stage, there is a system `G` over the same diagram of spaces, a monomorphism of systems
`S ⟶ G`, and a limiting cone `cG` over `G` lying over the same cone of spaces, such that

* every stage sheaf of `G` is injective;
* the positive-degree cohomology of every stage sheaf of `G` vanishes over every open, which
  kills the stage side of the comparison;
* the positive-degree cohomology of the sheaf on the vertex of `cG` vanishes over `pᵢ⁻¹U`, which
  kills the limit side.

This is the effaceability input of
`CategoryTheory.DeltaFunctor.isIso_app_of_isIso_app_zero`. -/
theorem exists_effacingSystem (c : Cone S.E) (hc : IsLimit c)
    (i : J) (U : Opens (S.E.obj i)) (hU : IsCompact (U : Set (S.E.obj i))) :
    ∃ (G : S.typeSystem.diagram.AbelianSystem) (α : S.toAbelianSystem ⟶ G)
      (cG : Cone G.toSpectralAbelianSheafSystem.E), Nonempty (IsLimit cG) ∧ Mono α ∧
      (∀ j : J, Injective (G.toSpectralAbelianSheafSystem.E.obj j).sheaf) ∧
      (∀ (j : J) (V : Opens (G.toSpectralAbelianSheafSystem.E.obj j)) (n : ℕ),
        IsZero (Sheaf.H'.{u, u, u} (G.toSpectralAbelianSheafSystem.E.obj j).sheaf (n + 1) V)) ∧
      ∀ n : ℕ, IsZero (Sheaf.H'.{u, u, u} cG.pt.sheaf (n + 1)
        (G.toSpectralAbelianSheafSystem.stageOpenCone cG i U).pt) := by
  obtain ⟨G, α, hα, _, hinj⟩ := S.exists_mono_injectiveSystem
  have hc₀ : IsLimit ((SheafedSpace.forget AddCommGrpCat.{u}).mapCone c) :=
    SheafedSpaceLimit.isLimit_mapCone_forget hc
  refine ⟨G, α, G.cone _, ⟨G.isLimit _ hc₀⟩, hα, hinj, ?_, ?_⟩
  · exact fun j V n => AbelianBasis.isZero_H'_succ_of_injective _ (hinj j) V n
  · exact fun n => G.toSpectralAbelianSheafSystem.isZero_H'_succ_conePoint_of_injective'
      (G.cone _) (G.isLimit _ hc₀) hinj i U hU n

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end
