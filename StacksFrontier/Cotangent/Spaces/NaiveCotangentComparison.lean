module

public import StacksFrontier.Cotangent.Spaces.CotangentComplex
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.AlgebraicGeometry.Spaces.NaiveCotangentComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentULift

/-!
# `H⁻¹` of the naive cotangent complex of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  The naive cotangent complex
`NL_{X/Y}` of Stacks 0D0V is formed from the structure map `f⁻¹𝒪_Y ⟶ 𝒪_X` of the small étale
ringed topoi, whose sections lie in the universe of the base scheme, while the cotangent complex
`L_{X/Y}` of Stacks 08VD is formed from the universe lift of that structure map.  This file shows
that `H⁻¹(NL_{X/Y})` vanishes exactly when `H⁻¹(L_{X/Y})` does.

The two steps are the independence of the vanishing of `H⁻¹(NL)` from the universe of the
sections, `Stacks.SheafOfModules.isZero_homology_negOne_naiveCotangentComplex_iff_sheafULift`, and
the identification of the naive cotangent complex with `τ_{≥ -1}` of the cotangent complex of
Stacks 08US, `CategoryTheory.Sheaf.canonicalNaiveComparison_isIso_homologyMap`, for the lifted
structure map.

## Main results

* `AlgebraicGeometry.Space.isZero_homology_negOne_naiveCotangentComplex_iff_cotangentComplex`:
  `H⁻¹(NL_{X/Y}) = 0` if and only if `H⁻¹(L_{X/Y}) = 0`.

## Implementation notes

`CategoryTheory.Sheaf.hasWeakSheafifyCommRingCat`, an instance for an arbitrary site at a
coefficient universe containing the universe of its objects, is demoted in this file, as in
`StacksFrontier/AlgebraicGeometry/Spaces/NaiveCotangentEtaleRestriction.lean`: tried first at the
universe of the structure rings it poses a universe constraint instance search cannot solve.

## References

* [Stacks Project, Tag 0D0V](https://stacks.math.columbia.edu/tag/0D0V)
* [Stacks Project, Tag 08VD](https://stacks.math.columbia.edu/tag/08VD)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 1] Sheaf.hasWeakSheafifyCommRingCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **`H⁻¹(NL_{X/Y})` vanishes exactly when `H⁻¹(L_{X/Y})` does**, for a morphism of algebraic
spaces `f : X ⟶ Y` over `S`. -/
theorem isZero_homology_negOne_naiveCotangentComplex_iff_cotangentComplex (f : X ⟶ Y) :
    IsZero ((naiveCotangentComplex B S hS f).homology (-1)) ↔
      IsZero ((cotangentComplex B S hS f).homology (-1)) := by
  refine (Stacks.SheafOfModules.isZero_homology_negOne_naiveCotangentComplex_iff_sheafULift.{u,
    u + 1, u, u, u + 1} (smallEtaleRingedTopos B S hS X).J _ _
    (smallEtaleRingedToposHom B S hS f).fSharpInverseImage).trans ?_
  have := Sheaf.canonicalNaiveComparison_isIso_homologyMap.{u + 1, u, u}
    (smallEtaleRingedTopos B S hS X).J
    ((SheafOfModules.sheafULift.{u, u + 1, u} (smallEtaleRingedTopos B S hS X).J).map
      (smallEtaleRingedToposHom B S hS f).fSharpInverseImage) (-1) le_rfl
  exact (asIso (HomologicalComplex.homologyMap (Sheaf.canonicalNaiveComparison
    (smallEtaleRingedTopos B S hS X).J ((SheafOfModules.sheafULift.{u, u + 1, u}
      (smallEtaleRingedTopos B S hS X).J).map
        (smallEtaleRingedToposHom B S hS f).fSharpInverseImage)) (-1))).isZero_iff.symm

end AlgebraicGeometry.Space

end
