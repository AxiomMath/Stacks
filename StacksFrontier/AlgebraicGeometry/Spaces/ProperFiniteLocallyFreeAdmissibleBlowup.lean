module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperFiniteLocallyFreeOverOpenBlowup

/-!
# Stacks 0B4K: a proper morphism finite locally free over an open, after an admissible blowup

Let `S` be a scheme, let `f : X ⟶ B` be a morphism of algebraic spaces over `S` and let `U ⊆ B`
be an open subspace.  Assume that `B` is quasi-compact and quasi-separated, that `U` is
quasi-compact, that `f` is proper and that `f⁻¹(U) ⟶ U` is finite locally free.  Then there is
a `U`-admissible blowup `B' ⟶ B` such that the strict transform `X'` of `X` is finite locally
free over `B'` ([Stacks, Tag 0B4K]).

## Main results

* `AlgebraicGeometry.Space.exists_admissibleBlowup_isFiniteLocallyFree_strictTransform`:
  [Stacks, Tag 0B4K].

## Implementation notes

The proof is
`Space.exists_isBlowupAlong_isFiniteLocallyFree_strictTransformSpaceToBlowUp_of_isProper`
(in the namespace `AlgebraicGeometry`), which follows the source: flattening by blowing up
(Stacks 087E), a further admissible blowup making `U` scheme-theoretically dense, Stacks 0B4J for
finiteness and Stacks 0416 for finite local freeness.  That theorem carries the fact that the
big fppf site contains the terminal scheme as a hypothesis, needed to state absolute
quasi-separatedness; here it is discharged by `AlgebraicGeometry.BigFppfSite.contains_terminal`,
so the statement has exactly the source's hypotheses.

A `U`-admissible blowup (`AlgebraicGeometry.Space.IsAdmissibleBlowup`, Stacks 086B) is the
blowup in a closed subspace `Z` of finite presentation whose points avoid those of `U`.  The
strict transform depends on the centre `Z` and not only on the morphism `B' ⟶ B`, so the
conclusion names `Z` and spells out the three clauses of `IsAdmissibleBlowup` for it; the strict
transform is taken with respect to the exceptional divisor, the inverse image of `Z`.

## References

* [Stacks Project, Tag 0B4K](https://stacks.math.columbia.edu/tag/0B4K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Let `f : X ⟶ A` be a morphism of algebraic spaces over `S` and let `U ⊆ A` be an open
subspace.  Assume that
1. `A` is quasi-compact and quasi-separated,
2. `U` is quasi-compact,
3. `f` is proper, and
4. `f⁻¹(U) ⟶ U` (the restriction `X ×_A U ⟶ U`) is finite locally free.

Then there is a `U`-admissible blowup `b : A' ⟶ A` -- the blowup of `A` in a closed subspace `Z`
of finite presentation whose points avoid those of `U` -- such that the strict transform
`X' ⟶ A'` of `X` with respect to `b` is finite locally free. -/
@[stacks 0B4K]
theorem exists_admissibleBlowup_isFiniteLocallyFree_strictTransform
    {A X : AlgebraicSpaces B S hS} (f : X ⟶ A) (U : OpenSubspaces B S hS A.1)
    (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hf : IsProper B S hS f.hom) (hflf : IsFiniteLocallyFree B S hS (restrictOverHom f U)) :
    ∃ (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A) (Z : ClosedSubspaces B S hS A.1),
      IsFinitePresentation B S hS Z.1.ι ∧
        Disjoint (subspacePointSet B S hS A.1 U.1) (subspacePointSet B S hS A.1 Z.1) ∧
          IsBlowupAlong B S hS Z b ∧
            IsFiniteLocallyFree B S hS
              (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)) :=
  exists_isBlowupAlong_isFiniteLocallyFree_strictTransformSpaceToBlowUp_of_isProper
    B.contains_terminal f U hAqc hAqs hUqc hf hflf

end AlgebraicGeometry.Space

end
