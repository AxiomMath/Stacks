module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceFormallyUnramified
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceThickeningDescent

/-!
# Stacks 060F with the two clauses of Stacks 05ZA supplied

`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceFormallyUnramified.lean` proves the two
halves of Stacks 060F for a universal first-order thickening `Z ⊂ Z'` of `h : Z ⟶ X` over `Y`:
exactness at the right term granted local surjectivity of `ι♯ : ι⁻¹𝒪_{Z'} ⟶ 𝒪_Z` as `hsharp`,
and the composite-zero and middle exactness clauses granted the same two clauses of Stacks 05ZA
at `Z ⊂ Z'` as `hzero` and `h05ZA`.  This file supplies those inputs.

* `hsharp` holds because `ι` is a closed immersion — the inclusion of a thickening is one by the
  definition of `AlgebraicGeometry.Space.IsThickening` — so
  `AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionStructureSharpInverseImage.lean` applies.
* `h05ZA` is `AlgebraicGeometry.Space.exact_conormalSequence` of
  `StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningDescent.lean`, the middle
  clause of Stacks 05ZA for an arbitrary closed subspace, respelled at `Z ⊂ Z'`.
* `hzero` is still a binder, and it is proved —
  `AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap` — it is
  carried only because writing it out costs more elaboration than passing it.

## Main results

* `AlgebraicGeometry.Space.exact_conormalSequence_universalThickening`: exactness at the middle
  term of the sequence of Stacks 05ZA at `Z ⊂ Z'`, in the spelling of the inclusion the
  statements of Stacks 060F use.
* `AlgebraicGeometry.Space.epi_thickeningConormalSecondMap'`: Stacks 060F, exactness at the right
  term, granted only the isomorphism `he` of Stacks 060E.
* `AlgebraicGeometry.Space.thickeningConormalSequence_exact'`: Stacks 060F, the composite of the
  two arrows is zero and the short complex is exact at the middle term, granted `he` and the
  proved `hzero`.

## References

* [Stacks Project, Tag 060F](https://stacks.math.columbia.edu/tag/060F)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB), whose surjectivity clause
  gives the local surjectivity of `ι♯` that exactness at the right term rests on.
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z' : AlgebraicSpaces B S hS} {Z : Subfunctor Z'.obj} {h' : Z' ⟶ X}

/-- **Exactness at the middle term of the sequence of Stacks 05ZA at the universal first-order
thickening**, with the inclusion written
`AlgebraicGeometry.Space.universalThickeningInclusion` as the statements of Stacks 060F spell it.

This is `AlgebraicGeometry.Space.exact_conormalSequence` of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalSequenceThickeningDescent.lean` at the closed
subspace `AlgebraicGeometry.Space.thickeningClosedSubspace`; the two spellings of the inclusion
are the same morphism `ObjectProperty.homMk Z.ι`.

This is what `AlgebraicGeometry.Space.thickeningConormalSequence_exact` carries as `h05ZA`.  The
tag is not registered here but on the general `AlgebraicGeometry.Space.exact_conormalSequence`,
which holds for an arbitrary closed subspace; this is only its respelling at the universal
thickening, which is the shape every consumer here needs. -/
theorem exact_conormalSequence_universalThickening
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (hzero : conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) = 0) :
    (ShortComplex.mk _ _ hzero).Exact :=
  exact_conormalSequence B S hS (h' ≫ p) (thickeningClosedSubspace B S hS hZ)

/-- **Stacks 060F, exactness at the right term, granted only the isomorphism of Stacks 060E.**
The second arrow `h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is an epimorphism.

This is `AlgebraicGeometry.Space.epi_thickeningConormalSecondMap` with its hypothesis `hsharp`
discharged: local surjectivity of `ι♯` holds because `ι` is a closed immersion, the inclusion of
a thickening being one by definition, so
`AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage` applies. -/
theorem epi_thickeningConormalSecondMap'
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p)) :
    Epi (thickeningConormalSecondMap B S hS hZ p) :=
  epi_thickeningConormalSecondMap B S hS hZ p he
    (isLocallySurjective_structureSharpInverseImage B S hS
      (universalThickeningInclusion B S hS hZ)
      (IsNthOrderThickening.isThickening B S hS hZ.firstOrder).1.2)

/-- **Stacks 060F, the two remaining clauses, with exactness of Stacks 05ZA at the middle term
supplied**: the composite of the two arrows is zero, and the resulting short complex
`𝒞_{Z/X} ⟶ h^*Ω_{X/Y} ⟶ Ω_{Z/Y}` is exact at the middle term.

This is `AlgebraicGeometry.Space.thickeningConormalSequence_exact` with its hypothesis `h05ZA`
discharged by `AlgebraicGeometry.Space.exact_conormalSequence_universalThickening` above.  Only
`hzero`, the vanishing of the composite, is still a binder, and it is proved —
`AlgebraicGeometry.Space.conormalSequenceFirstMap_comp_pullbackDifferentialsMap`.  Exactness at
the right term is separate, `AlgebraicGeometry.Space.epi_thickeningConormalSecondMap'`. -/
theorem thickeningConormalSequence_exact'
    (hZ : IsUniversalFirstOrderThickening B S hS Z h') (p : X ⟶ Y)
    (he : IsIso (thickeningSheafOfDifferentialsMap B S hS hZ p))
    (hzero : conormalSequenceFirstMap B S hS (thickeningClosedSubspace B S hS hZ) (h' ≫ p) ≫
      pullbackDifferentialsMap B S hS (universalThickeningInclusion B S hS hZ) (h' ≫ p) = 0) :
    ∃ hc : thickeningConormalFirstMap B S hS hZ p he ≫
        thickeningConormalSecondMap B S hS hZ p = 0,
      (ShortComplex.mk _ _ hc).Exact :=
  thickeningConormalSequence_exact B S hS hZ p he hzero
    (exact_conormalSequence_universalThickening B S hS hZ p hzero)

end AlgebraicGeometry.Space

end
