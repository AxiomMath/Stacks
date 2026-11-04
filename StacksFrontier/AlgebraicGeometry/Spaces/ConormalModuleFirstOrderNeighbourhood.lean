module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFlatBaseChange
public import StacksFrontier.CategoryTheory.Sites.ClosedImmersion.ConormalAlgebra

/-!
# The conormal module of a first order infinitesimal neighbourhood

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S` contained in a big fppf
site `B`, with defining ideal sheaf `𝓘 ⊆ 𝒪_X` on the small étale site of `X`, and let
`Z ⊆ Z' ⊆ X` be the first order infinitesimal neighbourhood of `Z` in `X`, that is the closed
subspace of `X` whose defining ideal sheaf is `𝓘²`. The square
```
Z --→ Z'
|     |
Z --→ X
```
is a fibre product square, and it induces a map of conormal modules `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}`. This
file proves that this map is an epimorphism, and that it is an isomorphism if and only if it is a
monomorphism. The neighbourhood is not constructed: `Z'` is a closed subspace of `X` given
together with the hypothesis `AlgebraicGeometry.Space.IsFirstOrderNeighbourhood`, and `Z` is
regarded as a closed subspace of `Z'` through its inverse image
`AlgebraicGeometry.Space.preimageSubspace` along the inclusion `Z' ⟶ X`.

## Main definitions

* `AlgebraicGeometry.Space.IsFirstOrderNeighbourhood`: the property, of a pair of closed
  subspaces of an algebraic space, that the second is the first order infinitesimal
  neighbourhood of the first, that is that its defining ideal sheaf is the square of the
  defining ideal sheaf of the first.

## Main results

* `AlgebraicGeometry.Space.le_of_isFirstOrderNeighbourhood`: a closed subspace is contained in
  its first order infinitesimal neighbourhood.
* `AlgebraicGeometry.Space.epi_conormalMap_firstOrderNeighbourhood`: the comparison map
  `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` for the first order infinitesimal neighbourhood is an epimorphism.
* `AlgebraicGeometry.Space.isIso_conormalMap_firstOrderNeighbourhood_iff_mono`: that comparison
  map is an isomorphism if and only if it is a monomorphism.

## References

* [Stacks Project, Tag 05ZX](https://stacks.math.columbia.edu/tag/05ZX)
* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 06BD](https://stacks.math.columbia.edu/tag/06BD)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

open Stacks.IdealPowerSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The first order infinitesimal neighbourhood of a closed subspace -/

/-- The closed subspace `Z'` of `X` is the first order infinitesimal neighbourhood of the closed
subspace `Z`: the defining ideal sheaf of `Z'` is the square of the defining ideal sheaf of `Z`. -/
def IsFirstOrderNeighbourhood (X : AlgebraicSpaces B S hS)
    (Z Z' : ClosedSubspaces B S hS X.1) : Prop :=
  definingIdealSheaf B S hS X Z' = idealPow (definingIdealSheaf B S hS X Z) 2

/-- A closed subspace is contained in its first order infinitesimal neighbourhood. -/
theorem le_of_isFirstOrderNeighbourhood (X : AlgebraicSpaces B S hS)
    (Z Z' : ClosedSubspaces B S hS X.1) (h : IsFirstOrderNeighbourhood B S hS X Z Z') :
    Z.1 ≤ Z'.1 :=
  le_of_definingIdealSheaf_le B S hS X Z Z'
    (h.trans_le ((idealPow_succ_le (definingIdealSheaf B S hS X Z) 1).trans_eq
      (idealPow_one (definingIdealSheaf B S hS X Z))))

/-! ### The comparison map of the neighbourhood -/

/-- Let `Z` be a closed subspace of an algebraic space `X` and let `Z'` be the first order
infinitesimal neighbourhood of `Z` in `X`. The map of conormal modules `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}`
induced by the fibre product square formed by `Z ⊆ Z'` and the inclusion `Z' ⟶ X` is an
epimorphism. -/
@[stacks 05ZX "surjectivity of the comparison map of conormal modules"]
theorem epi_conormalMap_firstOrderNeighbourhood (X : AlgebraicSpaces B S hS)
    (Z Z' : ClosedSubspaces B S hS X.1) (h : IsFirstOrderNeighbourhood B S hS X Z Z') :
    Epi (conormalMap B S hS
      (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
      (subspaceInclusion B S hS X Z')
      (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
      (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)) :=
  epi_conormalMap_closedSubspaces B S hS Z' Z (le_of_isFirstOrderNeighbourhood B S hS X Z Z' h)

/-- For closed subspaces `Z` and `Z'` of an algebraic space `X`, the map of conormal modules
`𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` induced by the inclusion `Z' ⟶ X` and the inverse image of `Z` in `Z'` is
an isomorphism if and only if it is a monomorphism. -/
theorem isIso_conormalMap_firstOrderNeighbourhood_iff_mono (X : AlgebraicSpaces B S hS)
    (Z Z' : ClosedSubspaces B S hS X.1) :
    IsIso (conormalMap B S hS
        (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
        (subspaceInclusion B S hS X Z')
        (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)) ↔
      Mono (conormalMap B S hS
        (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
        (subspaceInclusion B S hS X Z')
        (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
        (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)) :=
  isIso_conormalMap_iff_mono_of_epi_idealSheafMap B S hS
    (preimageSubspace B S hS (subspaceInclusion B S hS X Z') Z) Z
    (subspaceInclusion B S hS X Z')
    (preimageProjection B S hS (subspaceInclusion B S hS X Z') Z)
    (conormalEtaleRestrictionSquare B S hS (subspaceInclusion B S hS X Z') Z)
    (epi_idealSheafMap B S hS (subspaceInclusion B S hS X Z') Z)

end AlgebraicGeometry.Space

end
