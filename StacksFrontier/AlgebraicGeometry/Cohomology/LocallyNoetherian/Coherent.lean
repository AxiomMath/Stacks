module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.StructureSheafCoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentIffFinitePresentation
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Coherent modules on a locally Noetherian scheme

On a locally Noetherian scheme, coherence, finite presentation, and quasi-coherence together with
finite type are equivalent, and either condition may be tested by finite modules on all affine
opens or on a single affine open covering. The structure sheaf and every finite locally free
module are coherent.

The five conditions are listed in the order of the source. Conditions (4) and (5) are phrased
with `Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn`, which says that the restriction of
the module to an affine open `U` is the sheaf associated with a finite `Γ(X, U)`-module, read
through the canonical isomorphism `U ≅ Spec Γ(X, U)`. An affine covering is a family of affine
opens whose supremum is the whole scheme.

## Main results

* `Stacks.AlgebraicGeometry.CoherentTFAE.coherent_tfae`: the five equivalent conditions.
* `Stacks.AlgebraicGeometry.CoherentTFAE.structureSheaf_isCoherent`: the structure sheaf is
  coherent.
* `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isFiniteLocallyFree`: a finite locally free
  module is coherent.

## Implementation notes

The implications proved are `1 → 3`, `3 → 2`, `2 → 4`, `4 → 5`, `5 → 2` and `2 → 1`; together
they make the implication graph strongly connected, which is what `tfae_finish` needs. All but
the last hold over an arbitrary scheme, so the Noetherian hypothesis enters exactly once,
through `Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isQuasicoherent_of_isFiniteType`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01BW](https://stacks.math.columbia.edu/tag/01BW)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.AlgebraicGeometry.CoherentTFAE

/-- **Stacks Project, Tag 01XZ.** The five characterizations of a coherent module on a locally
Noetherian scheme. -/
@[stacks 01XZ "five equivalent conditions"]
theorem coherent_tfae (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) :
    List.TFAE [
      F.IsCoherent,
      F.IsQuasicoherent ∧ F.IsFiniteType,
      F.IsFinitePresentation,
      ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU,
      ∃ (ι : Type u) (U : ι → X.Opens),
        IsOpenCover U ∧ ∀ i, ∃ hU : IsAffineOpen (U i), IsFiniteTildeOn F (U i) hU
    ] := by
  classical
  tfae_have 1 → 3 := fun _ => isFinitePresentation_of_isCoherent' F
  tfae_have 3 → 2 := fun h => isQuasicoherent_isFiniteType_of_isFinitePresentation F h
  tfae_have 2 → 4 := by
    rintro ⟨_, _⟩ U hU
    exact isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType F U hU
  tfae_have 4 → 5 := fun h => exists_affineOpenCover_isFiniteTildeOn F h
  tfae_have 5 → 2 := fun h => isQuasicoherent_isFiniteType_of_cover_isFiniteTildeOn F h
  tfae_have 2 → 1 := by
    rintro ⟨_, _⟩
    exact isCoherent_of_isQuasicoherent_of_isFiniteType X F
  tfae_finish

/-- **Stacks Project, Tag 01XZ.** On a locally Noetherian scheme the structure sheaf is
coherent. -/
@[instance, stacks 01XZ "the structure sheaf is coherent"]
theorem structureSheaf_isCoherent (X : Scheme.{u}) [IsLocallyNoetherian X] :
    (SheafOfModules.unit X.ringCatSheaf).IsCoherent := isCoherent_unit X

/-- **Stacks Project, Tag 01XZ.** A finite locally free module on a locally Noetherian scheme is
coherent. -/
@[instance, stacks 01XZ "finite locally free modules are coherent"]
theorem isCoherent_of_isFiniteLocallyFree (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens X) (J := Opens.grothendieckTopology X) F] :
    F.IsCoherent := by
  obtain ⟨q, hlocal, hfinite⟩ :=
    (inferInstance : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (C := Opens X) (J := Opens.grothendieckTopology X) F).exists_isFiniteLocallyFreeData
  have : q.IsLocallyFreeData := hlocal
  have hquasicoherent : F.IsQuasicoherent := q.quasiCoherentData.isQuasicoherent
  have hqcft : F.IsQuasicoherent ∧ F.IsFiniteType := by
    refine ⟨hquasicoherent, ?_⟩
    exact SheafOfModules.IsFiniteType.mk.{u, u, u}
      (show ∃ σ : SheafOfModules.LocalGeneratorsData.{u, u, u, u} F,
        σ.IsFiniteType from ⟨q, hfinite⟩)
  exact ((coherent_tfae X F).out 2 1).mp hqcft

end Stacks.AlgebraicGeometry.CoherentTFAE

end
