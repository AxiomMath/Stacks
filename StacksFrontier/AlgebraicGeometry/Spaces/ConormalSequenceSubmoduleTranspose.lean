module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceDifferentials

/-!
# The first arrow of the conormal sequence through the general constructions

The first arrow `𝒞_{Z/X} ⟶ i^*Ω_{X/B}` of Stacks 05ZA, for a closed subspace `Z` of an
algebraic space `X`, is built in three steps, each an instance of a construction for an
arbitrary sheaf of ideals `𝓘 ⊆ 𝒪_X` or an arbitrary morphism of algebraic spaces:
`AlgebraicGeometry.Space.submoduleDerivationHom`, `AlgebraicGeometry.Space.submoduleTranspose`
and `AlgebraicGeometry.Space.pullbackUnitDerivation`.  This file proves that, at the defining
ideal sheaf of a closed subspace and its inclusion, the constructions of Stacks 05ZA are these
general ones.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `conormalSequenceIdealPullbackMap_eq_submoduleTranspose`,
  `conormalSequenceIdealHom_eq_submoduleDerivationHom`,
  `conormalSequenceIdealDifferential_eq_submoduleDerivationHom` and
  `conormalSequenceUnitDerivation_eq_pullbackUnitDerivation`: at the defining ideal sheaf of a
  closed subspace and its inclusion, the constructions of Stacks 05ZA are the general ones.

## References

* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.RingedToposModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section ClosedSubspace

variable {X Bb : AlgebraicSpaces B S hS}

/-- At the inclusion of a closed subspace, `AlgebraicGeometry.Space.pullbackUnitDerivation` is the
`B`-derivation `AlgebraicGeometry.Space.conormalSequenceUnitDerivation` that induces the first
arrow of Stacks 05ZA. -/
theorem conormalSequenceUnitDerivation_eq_pullbackUnitDerivation (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) :
    conormalSequenceUnitDerivation B S hS Z b =
      pullbackUnitDerivation B S hS (subspaceInclusion B S hS X Z) b := by
  unfold conormalSequenceUnitDerivation pullbackUnitDerivation
  rfl

/-- At the defining ideal sheaf of a closed subspace,
`AlgebraicGeometry.Space.submoduleDerivationHom` is
`AlgebraicGeometry.Space.conormalSequenceIdealHom`. -/
theorem conormalSequenceIdealHom_eq_submoduleDerivationHom (Z : ClosedSubspaces B S hS X.1)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ : A ⟶ (smallEtaleRingedTopos B S hS X).O}
    (N : Modules.{u, u} B S hS X.1 X.2) (D : N.val.Derivation' φ.hom)
    (hann : ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ)
      (a : (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj U),
      a ∈ definingIdealAt B S hS X Z U → ∀ m : N.val.obj U, a • m = 0) :
    conormalSequenceIdealHom B S hS Z N D hann =
      submoduleDerivationHom B S hS (definingIdealSheaf B S hS X Z) N D hann :=
  rfl

/-- **The adjoint form of the first arrow of Stacks 05ZA, through the general constructions**:
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential` is the restriction
`AlgebraicGeometry.Space.submoduleDerivationHom` of
`AlgebraicGeometry.Space.pullbackUnitDerivation` at the inclusion to the defining ideal sheaf. -/
theorem conormalSequenceIdealDifferential_eq_submoduleDerivationHom
    (Z : ClosedSubspaces B S hS X.1) (b : X ⟶ Bb) :
    conormalSequenceIdealDifferential B S hS Z b =
      submoduleDerivationHom B S hS (definingIdealSheaf B S hS X Z) _
        (pullbackUnitDerivation B S hS (subspaceInclusion B S hS X Z) b)
        (fun U a ha m ↦ definingIdealAt_smul_modulePushforward_eq_zero B S hS Z _ U a ha m) := by
  unfold conormalSequenceIdealDifferential
  rw [conormalSequenceIdealHom_eq_submoduleDerivationHom,
    conormalSequenceUnitDerivation_eq_pullbackUnitDerivation]

/-- **The first arrow of Stacks 05ZA is a transposition by
`AlgebraicGeometry.Space.submoduleTranspose`**: at the inclusion of a closed subspace and its
defining ideal sheaf, `AlgebraicGeometry.Space.submoduleTranspose` of
`AlgebraicGeometry.Space.conormalSequenceIdealDifferential` is
`AlgebraicGeometry.Space.conormalSequenceIdealPullbackMap`. -/
theorem conormalSequenceIdealPullbackMap_eq_submoduleTranspose (Z : ClosedSubspaces B S hS X.1)
    (b : X ⟶ Bb) :
    conormalSequenceIdealPullbackMap B S hS Z b =
      submoduleTranspose B S hS (subspaceInclusion B S hS X Z) (definingIdealSheaf B S hS X Z)
        ((modulePullback B S hS (subspaceInclusion B S hS X Z)).obj
          (sheafOfDifferentials B S hS b))
        (conormalSequenceIdealDifferential B S hS Z b) := by
  unfold conormalSequenceIdealPullbackMap submoduleTranspose
  congr 1

end ClosedSubspace

end AlgebraicGeometry.Space

end
