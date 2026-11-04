module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceInclusionParameter
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceMiddleExactnessAt

/-!
# The conormal sequence of a formally unramified morphism, without the clauses of Stacks 05ZA

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramified.lean` constructs the two
arrows of the sequence `𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y} ⟶ 0` of Stacks 060F for a universal first
order thickening `Z ⊂ Z'` over `h' : Z' ⟶ X`, and proves the vanishing of the composite and the
exactness at the middle term, `AlgebraicGeometry.Space.thickeningConormalSequence_exact`, from
the isomorphism `he` of Stacks 060E and two hypotheses `hzero` and `h05ZA`: the same two clauses
for the sequence of Stacks 05ZA at the closed subspace `Z ⊂ Z'` over `Y`.

This file discharges `hzero` and `h05ZA`.  Both clauses of Stacks 05ZA are proved in this
library at an explicitly parameterized inclusion
(`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceInclusionParameter.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceMiddleExactness.lean`); instantiating them
at the inclusion `ι = AlgebraicGeometry.Space.universalThickeningInclusion` avoids the costly
conversion between `ι` and `AlgebraicGeometry.Space.subspaceInclusion` underneath
`AlgebraicGeometry.Space.sheafOfDifferentials`.

## Main results

* `AlgebraicGeometry.Space.thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero`
  and `AlgebraicGeometry.Space.thickeningConormalSequenceAt_exact`: the two clauses of
  Stacks 05ZA for `Z ⊂ Z'` over `Y`, at the inclusion `ι`.
* `AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningConormalSecondMap_eq_zero`:
  the composite of the two arrows of Stacks 060F is zero.
* `AlgebraicGeometry.Space.thickeningConormalSequence_exact_of_isIso`: the composite is zero and
  the short complex is exact at the middle term, assuming only `he`.

## Why nothing here is registered

Every statement about the arrows of Stacks 060F takes `he : IsIso
(thickeningSheafOfDifferentialsMap B S hS hZ p)`, the isomorphism of Stacks 060E, because the
first arrow is defined through its inverse.  This library proves Stacks 060E only under the
étale localization `hetale` of
`AlgebraicGeometry.Space.isIso_thickeningSheafOfDifferentialsMap`, so these statements are not
the tag at the source's hypotheses and carry no `@[stacks]` attribute.  The registrations of
Stacks 060F stay where they are, in `ConormalSequenceFormallyUnramified.lean`.
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-! ### The two clauses of Stacks 05ZA for the thickening -/

/-- The structure map of the inclusion `ι : Z ⟶ Z'` of a universal first-order thickening kills
the defining ideal of `Z` in `Z'`.  This is `AlgebraicGeometry.Space.mem_definingIdealAt_iff` at
`AlgebraicGeometry.Space.thickeningClosedSubspace`, read at the spelling `ι` of the inclusion;
it is the one hypothesis
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero`
needs, and the only place where the two spellings of the inclusion have to be reconciled. -/
theorem thickeningStructureSharpKillsDefiningIdeal
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') :
    StructureSharpKillsDefiningIdeal B S hS (thickeningClosedSubspace B S hS hZ)
      (universalThickeningInclusion B S hS hZ) :=
  fun U a ha ↦
    (mem_definingIdealAt_iff B S hS Z' (thickeningClosedSubspace B S hS hZ) U a).1 ha

/-- **Stacks 05ZA, the composite of the two arrows is zero, for the thickening `Z ⊂ Z'`.**
Unconditional: the clause of Stacks 05ZA proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceCompositeZero.lean`, instantiated through
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero` at
the inclusion `ι` rather than at `AlgebraicGeometry.Space.subspaceInclusion`, which
is what makes it applicable here with no conversion. -/
theorem thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    conormalSequenceFirstMapAt B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p)
        (universalThickeningInclusion B S hS hZ)
        (thickeningStructureSharpKillsDefiningIdeal B S hS hZ) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) = 0 :=
  conormalSequenceFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS
    (thickeningClosedSubspace B S hS hZ) (h' ≫ p)
    (universalThickeningInclusion B S hS hZ)
    (thickeningStructureSharpKillsDefiningIdeal B S hS hZ)

/-- **Stacks 05ZA, exactness at the middle term, for the thickening `Z ⊂ Z'`.**
Unconditional: `AlgebraicGeometry.Space.conormalSequenceAt_exact` instantiated at the inclusion
`ι` of this file.  Its three hypotheses are discharged here —
`AlgebraicGeometry.Space.thickeningStructureSharpKillsDefiningIdeal` and
`AlgebraicGeometry.Space.structureSharpKernelLeDefiningIdeal_subspaceInclusion` are the two
halves of `AlgebraicGeometry.Space.mem_definingIdealAt_iff`, which together say the kernel of
`ι♯` is the defining ideal sheaf, and
`AlgebraicGeometry.Space.isClosedImmersion_subspaceInclusion` is part (4) of Stacks 02YU.

This is the clause that `AlgebraicGeometry.Space.thickeningConormalSequence_exact` and the
statements built on it take as the hypothesis `h05ZA`, and what discharges it in
`AlgebraicGeometry.Space.thickeningConormalSequence_exact_of_isIso` below. -/
theorem thickeningConormalSequenceAt_exact
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y) :
    (ShortComplex.mk _ _
      (thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero
        B S hS hZ p)).Exact :=
  conormalSequenceAt_exact B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p)
    (universalThickeningInclusion B S hS hZ)
    (thickeningStructureSharpKillsDefiningIdeal B S hS hZ)
    (structureSharpKernelLeDefiningIdeal_subspaceInclusion B S hS
      (thickeningClosedSubspace B S hS hZ))
    (isClosedImmersion_subspaceInclusion B S hS Z' (thickeningClosedSubspace B S hS hZ))

/-- The comparison of Stacks 060E, read at `conormalSequenceFirstMapAt` of the inclusion `ι`. -/
private theorem thickeningConormalFirstMap_comp_eq_conormalSequenceFirstMapAt
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    thickeningConormalFirstMap B S hS hZ p he ≫
      thickeningSheafOfDifferentialsMap B S hS hZ p =
      conormalSequenceFirstMapAt B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p)
        (universalThickeningInclusion B S hS hZ)
        (thickeningStructureSharpKillsDefiningIdeal B S hS hZ) :=
  thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap B S hS hZ p he

/-- **Stacks 060F, the composite of the two arrows is zero**, assuming only the isomorphism `he`
of Stacks 060E, through which the first arrow is defined.

Nothing of Stacks 05ZA is assumed: this is the clause that
`AlgebraicGeometry.Space.thickeningConormalSequence_exact` takes as `hzero`. The proof reads
`AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningSheafOfDifferentialsMap` at
`AlgebraicGeometry.Space.conormalSequenceFirstMapAt` of the inclusion `ι` of this file (`key`),
and concludes with the first clause of Stacks 05ZA,
`AlgebraicGeometry.Space.thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero`. -/
theorem thickeningConormalFirstMap_comp_thickeningConormalSecondMap_eq_zero
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    thickeningConormalFirstMap B S hS hZ p he ≫
      thickeningConormalSecondMap B S hS hZ p = 0 := by
  simp only [thickeningConormalSecondMap, ← Category.assoc]
  rw [thickeningConormalFirstMap_comp_eq_conormalSequenceFirstMapAt B S hS hZ p he]
  exact thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS hZ p

/-- **Stacks 060F, the two remaining clauses, granted only the isomorphism of Stacks 060E**: the
composite of the two arrows is zero, and the resulting short complex
`𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is exact at the middle term.

This is `AlgebraicGeometry.Space.thickeningConormalSequence_exact` with its two hypotheses about
Stacks 05ZA discharged, and the transport is the same: the isomorphism of Stacks 060E carries the
sequence of Stacks 05ZA at the closed subspace `Z ⊂ Z'` over `Y` across.  The short complex of
the conclusion is isomorphic to the short complex of Stacks 05ZA, by the identity on the two
outer terms and that isomorphism on the middle one, so
`CategoryTheory.ShortComplex.exact_iff_of_iso` transfers exactness.

Nothing about Stacks 05ZA is granted here.  That the composite of its two arrows is zero is
`AlgebraicGeometry.Space.thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero`, and
its middle exactness — carried as the hypothesis `h05ZA` until Stacks 05ZA was closed — is
`AlgebraicGeometry.Space.thickeningConormalSequenceAt_exact`; both are unconditional.  The
composite of the two arrows of *this* tag is
`AlgebraicGeometry.Space.thickeningConormalFirstMap_comp_thickeningConormalSecondMap_eq_zero`,
also proved, so the existential's witness is supplied rather than assumed.  Exactness at the
right term is not granted either: it is proved, by
`AlgebraicGeometry.Space.epi_thickeningConormalSecondMap`. -/
theorem thickeningConormalSequence_exact_of_isIso
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    ∃ hc : thickeningConormalFirstMap B S hS hZ p he ≫
        thickeningConormalSecondMap B S hS hZ p = 0,
      (ShortComplex.mk _ _ hc).Exact := by
  have : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p) := he
  have hzero :=
    thickeningConormalFirstMapAt_comp_pullbackDifferentialsMap_eq_zero B S hS hZ p
  have hc :=
    thickeningConormalFirstMap_comp_thickeningConormalSecondMap_eq_zero B S hS hZ p he
  -- the comparison, read at `conormalSequenceFirstMapAt` so that the square below is
  -- about the same short complex as `hzero`; this ascription is the one cheap conversion
  refine ⟨hc, ?_⟩
  have hiso : ShortComplex.mk _ _ hc ≅ ShortComplex.mk _ _ hzero :=
    ShortComplex.isoMk (Iso.refl _)
      (asIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) (Iso.refl _)
      ((Category.id_comp _).trans
        (thickeningConormalFirstMap_comp_eq_conormalSequenceFirstMapAt B S hS hZ p he).symm)
      (by simp [thickeningConormalSecondMap])
  exact (ShortComplex.exact_iff_of_iso hiso).mpr
    (thickeningConormalSequenceAt_exact B S hS hZ p)

end AlgebraicGeometry.Space

end
