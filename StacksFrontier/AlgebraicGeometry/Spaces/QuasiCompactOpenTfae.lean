module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealOfQuasiCompactOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenOfFiniteTypeIdeal

/-!
# Quasi-compact open subspaces of a quasi-compact quasi-separated algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and `U ⊆ X` an
open subspace.  Stacks 0855 asserts that the following are equivalent:

1. the inclusion `U → X` is quasi-compact;
2. `U` is quasi-compact;
3. there is a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` of finite type with
   `|X| ∖ |U| = |V(ℐ)|`.

This file assembles the three implications into the equivalence.

## Main results

* `AlgebraicGeometry.Space.tfae_isQuasiCompact_openSubspace`: **Stacks 0855.**

## Implementation notes

The three implications are
`AlgebraicGeometry.Space.isQuasiCompact_iff_isQuasiCompactSpace_openSubspace` for (1) ⟺ (2),
`AlgebraicGeometry.Space.hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace` for
(2) ⟹ (3), which goes through Stacks 0853, and
`AlgebraicGeometry.Space.isQuasiCompactSpace_of_hasFiniteTypeQuasicoherentIdealZeroLocus` for
(3) ⟹ (2).  Condition (3) is `AlgebraicGeometry.Space.HasFiniteTypeQuasicoherentIdealZeroLocus`.

## References

* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0855.** Let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U ⊆ X` be an open subspace.  The following are equivalent:

1. the inclusion `U → X` is quasi-compact,
2. `U` is quasi-compact, and
3. there exists a finite type quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` such that
   `|X| ∖ |U| = |V(ℐ)|`. -/
@[stacks 0855]
theorem tfae_isQuasiCompact_openSubspace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (U : Subfunctor X.1) (hU : IsOpenSubspace B S hS U) :
    List.TFAE [IsQuasiCompact B S hS U.ι, IsQuasiCompactSpace B S hS U.toFunctor,
      HasFiniteTypeQuasicoherentIdealZeroLocus B S hS X U] := by
  tfae_have 1 ↔ 2 :=
    isQuasiCompact_iff_isQuasiCompactSpace_openSubspace B S hS hZ X hXqc hXqs ⟨U, hU⟩
  tfae_have 2 → 3 :=
    hasFiniteTypeQuasicoherentIdealZeroLocus_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs hU
  tfae_have 3 → 2 :=
    isQuasiCompactSpace_of_hasFiniteTypeQuasicoherentIdealZeroLocus B S hS X hXqc hU
  tfae_finish

end AlgebraicGeometry.Space

end
