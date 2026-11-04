module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersionEtaleRestriction

/-!
# The conormal module of an immersion, at the inclusion of a closed subspace

`AlgebraicGeometry.Space.conormalModule` is the conormal module `𝒞_{Z/X}` of a *closed* subspace
`Z ⊆ X` of [Stacks Project, Tag 04CN]: the inverse image along the inclusion of the defining
ideal sheaf of [Stacks Project, Tag 03MB].  `AlgebraicGeometry.Space.immersionConormalModule`
is the conormal module of an arbitrary *immersion* `i : Z ⟶ X`, built through the closed
factorisation of [Stacks Project, Tag 04CE] via the ambient open `X ∖ ∂Z`.

For the inclusion of a closed subspace both apply, and this file identifies them.  That
identification is the one the module documentation of
`StacksFrontier/AlgebraicGeometry/Spaces/ConormalModule.lean` names — "the general case is that
declaration, and `AlgebraicGeometry.Space.conormalAlgebra_piece_one_eq_conormalModule` together
with `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` identify the two for the
inclusion of a closed subspace" — but which no declaration in the development carried: the two
named ingredients are an equality and an isomorphism between *different* pairs of objects, so
identifying the two spellings is their composite and had to be built.

## Why it is an isomorphism and not an equality

`AlgebraicGeometry.Space.conormalAlgebra_piece_one_eq_conormalModule` is an equality, but it is
an equality about `AlgebraicGeometry.Space.conormalAlgebra` of the inclusion — the conormal
algebra of the morphism itself — while `AlgebraicGeometry.Space.immersionConormalModule` is the
degree-one piece of `AlgebraicGeometry.Space.conormalAlgebraOfImmersion`, the conormal algebra of
the closed factorisation through `X ∖ ∂Z`.  Those two algebras are not equal; they are compared
by `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso`, which is the
étale-localization isomorphism of [Stacks Project, Tag 09RR] at the cartesian square of
`AlgebraicGeometry.Space.isPullback_immersionClosedFactorization`.  So the passage through the
ambient open is *not* an identity even when `Z` is already closed, and the comparison below is
an isomorphism.

The passage itself needs nothing extra:
`AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` is defined for an arbitrary immersion
with no hypothesis beyond the immersion, so no cartesianness, affineness or representability is
assumed here either.

## Main definitions

* `AlgebraicGeometry.Space.conormalModuleOfImmersionSubspaceIso`: **the conormal module of a
  closed subspace is the conormal module of its inclusion read as an immersion.**

## Main results

* `AlgebraicGeometry.Space.isImmersion_subspaceInclusion`: the inclusion of a closed subspace is
  an immersion, which is the hypothesis `AlgebraicGeometry.Space.immersionConormalModule` needs
  in order to be written at it at all.

## Relation to the other spellings

`AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` compares
`AlgebraicGeometry.Space.immersionConormalModule` with the inverse image of
`AlgebraicGeometry.Space.kernelIdealSheafZPow` in degree one, and
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` with the inverse image of
`AlgebraicGeometry.Space.kernelIdealSheaf`.  The comparison here is the remaining spelling, the
one at `AlgebraicGeometry.Space.conormalModule` itself, which is the spelling the conormal module
of a closed subspace is written at throughout the étale-restriction and chart-comparison files;
naming it pays for the passage through the ambient open once.

No `@[stacks]` attribute is claimed: Tags 04CN, 04CE, 04CO and 09RR are registered where the
constructions they name are built, and what is proved here is the agreement of two of those
constructions on their common ground.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CE](https://stacks.math.columbia.edu/tag/04CE)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 09RR](https://stacks.math.columbia.edu/tag/09RR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of a closed subspace is an immersion.**  It is a closed immersion by part (4)
of [Stacks Project, Tag 02YU], read off the bundled `AlgebraicGeometry.Space.ClosedSubspaces` as
`AlgebraicGeometry.Space.isClosedImmersion_subspaceInclusion` does, and a closed immersion is an
immersion.

This is what lets `AlgebraicGeometry.Space.immersionConormalModule` be written at the
inclusion of a closed subspace. -/
theorem isImmersion_subspaceInclusion (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1) :
    IsImmersion B S hS (subspaceInclusion B S hS X Z).hom :=
  isImmersion_of_isClosedImmersion B S hS Z.2.2

/-- **The conormal module of a closed subspace is the conormal module of its inclusion read as an
immersion.**  For a closed subspace `Z ⊆ X` the conormal module `𝒞_{Z/X}` of
[Stacks Project, Tag 04CN] — the inverse image along the inclusion of the defining ideal sheaf —
agrees with the conormal module of the inclusion taken as an immersion, that is with the
degree-one piece of the conormal algebra of its closed factorisation through `X ∖ ∂Z`.

The comparison is `AlgebraicGeometry.Space.conormalAlgebraOfImmersionPieceIso` in degree one,
whose source is the degree-one piece of the conormal algebra of the inclusion itself, precomposed
with the identification of that piece with the conormal module,
`AlgebraicGeometry.Space.conormalAlgebra_piece_one_eq_conormalModule`.

The immersion hypothesis is taken as an argument rather than discharged so that the statement is
available at whichever proof of it a consumer already holds; the canonical one is
`AlgebraicGeometry.Space.isImmersion_subspaceInclusion`. -/
noncomputable def conormalModuleOfImmersionSubspaceIso (X : AlgebraicSpaces B S hS)
    (Z : ClosedSubspaces B S hS X.1)
    (hi : IsImmersion B S hS (subspaceInclusion B S hS X Z).hom) :
    conormalModule B S hS X Z ≅
      immersionConormalModule B S hS (subspaceInclusion B S hS X Z) hi :=
  eqToIso (conormalAlgebra_piece_one_eq_conormalModule B S hS X Z).symm ≪≫
    conormalAlgebraOfImmersionPieceIso B S hS (subspaceInclusion B S hS X Z) hi 1

end AlgebraicGeometry.Space

end
