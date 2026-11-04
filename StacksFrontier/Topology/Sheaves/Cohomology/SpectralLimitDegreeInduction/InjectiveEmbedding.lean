module

public import StacksFrontier.Topology.Sheaves.Limits.AbelianSystemInjective

/-!
# A bundled system of abelian sheaves embeds in a stagewise injective one

A bundled system `S : SpectralAbelianSheafSystem J` of abelian sheaves over a cofiltered diagram of
spectral spaces admits a monomorphism into a system over the same diagram of spaces all of whose
stage sheaves are injective, in the form `∀ j, Injective (S.E.obj j).sheaf`.

The construction is the coinduced system of
`StacksFrontier/Topology/Sheaves/Limits/AbelianSystemInjective.lean`, read through the comparison of
the two encodings of a system: a bundled system is a system over its own underlying diagram of
spaces, and a system over a fixed diagram is a bundled system whose base diagram is that diagram
on the nose.

## Main results

* `SpectralDiagram.AbelianSystem.toSpectralAbelianSheafSystem_E_obj_sheaf` and
  `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.toAbelianSystem_sheaf`: the stage
  sheaves agree under both comparisons, by definition.
* `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.exists_mono_injectiveSystem`: a
  bundled system admits a monomorphism of systems into one that is injective at each stage, over
  the same diagram of spaces.
* `Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.exists_injectiveStages`: the same
  conclusion with the embedding forgotten: over the diagram of spaces of every bundled system
  there is a bundled system whose stage sheaves are all injective.

## Implementation notes

The injectivity hypothesis is stated for `(S.E.obj j).sheaf`, which is the sheaf extracted from a
sheafed space, while the embedding produces a system whose data is a sheaf at each stage.  The two
are the same term: `AlgebraicGeometry.SheafedSpace.sheaf` pairs the presheaf with the sheaf
condition, and that is what `SpectralDiagram.AbelianSystem.space` was built from.  So both
comparisons are `rfl`, and the conclusion can be stated directly in the hypothesis's spelling
with no transport.

The base diagram is preserved on the nose in both directions —
`SpectralDiagram.AbelianSystem.toSpectralAbelianSheafSystem_baseDiagram` and
`Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem.typeSystem_diagram_F` — which is what
makes the open cones, the cone of spaces and the quasi-compactness hypotheses of the comparison
shared between a system and its injective envelope rather than transported along an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open AlgebraicGeometry

universe u

noncomputable section

namespace SpectralDiagram.AbelianSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J] {D : SpectralDiagram.{u, u} J}

/-- The stage sheaves of the bundled reading `A.toSpectralAbelianSheafSystem` of a system `A` are
the sheaves `A.sheaf j`. -/
theorem toSpectralAbelianSheafSystem_E_obj_sheaf (A : D.AbelianSystem) (j : J) :
    (A.toSpectralAbelianSheafSystem.E.obj j).sheaf = A.sheaf j := rfl

end SpectralDiagram.AbelianSystem

namespace Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

variable {J : Type u} [SmallCategory J] [IsCofiltered J]
  (S : SpectralAbelianSheafSystem.{u, u, u} J)

/-- The sheaves of the unbundled reading `S.toAbelianSystem` of a bundled system `S` are its stage
sheaves. -/
theorem toAbelianSystem_sheaf (j : J) : S.toAbelianSystem.sheaf j = (S.E.obj j).sheaf := rfl

/-- A system `G` over the diagram of spaces underlying a bundled system `S` has, read as a bundled
system, the base diagram of `S`. -/
theorem toSpectralAbelianSheafSystem_baseDiagram_eq
    (G : S.typeSystem.diagram.AbelianSystem) :
    G.toSpectralAbelianSheafSystem.baseDiagram = S.baseDiagram := rfl

/-- A bundled system of abelian sheaves admits a monomorphism into a system over the same diagram
of spaces that is injective at each stage. Injectivity is stated both for the sheaves `G.sheaf j`
of that system and for the stage sheaves of its bundled reading. -/
theorem exists_mono_injectiveSystem :
    ∃ (G : S.typeSystem.diagram.AbelianSystem) (α : S.toAbelianSystem ⟶ G),
      Mono α ∧ (∀ j : J, Injective (G.sheaf j)) ∧
        ∀ j : J, Injective (G.toSpectralAbelianSheafSystem.E.obj j).sheaf := by
  obtain ⟨G, α, hα, hinj⟩ := S.toAbelianSystem.exists_mono_stageInjective
  exact ⟨G, α, hα, hinj, hinj⟩

/-- Over the diagram of spaces underlying a bundled system `S` there is a bundled system `S'` with
the same base diagram all of whose stage sheaves are injective. -/
theorem exists_injectiveStages :
    ∃ S' : SpectralAbelianSheafSystem.{u, u, u} J,
      S'.baseDiagram = S.baseDiagram ∧ ∀ j : J, Injective (S'.E.obj j).sheaf := by
  obtain ⟨G, _, _, _, hinj⟩ := S.exists_mono_injectiveSystem
  exact ⟨G.toSpectralAbelianSheafSystem, S.toSpectralAbelianSheafSystem_baseDiagram_eq G, hinj⟩

end Stacks.Cohomology.SpectralLimit.SpectralAbelianSheafSystem

end

end
