module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.ChartStrictHenselization
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.DistinctDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationCrossingsStrict
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.NormalizationEquivalenceForward

/-!
# Normal crossings divisors and the normalization criterion

Let `X` be a locally Noetherian scheme and `D ⊂ X` a closed subscheme. Then `D` is a normal
crossings divisor in `X` if and only if `D` is reduced, the normalization `ν : D^ν ⟶ D` is
unramified, and for every `n ≥ 1` the scheme

  `Z_n = D^ν ×_D ⋯ ×_D D^ν ∖ {(p_1, …, p_n) ∣ p_i = p_j for some i ≠ j}`

is regular and the morphism `Z_n ⟶ X` is a local complete intersection morphism whose conormal
sheaf is locally free of rank `n`.

## Main results

* `Stacks.Divisors.isNormalCrossingsDivisor_of_isNormalizationCrossingsDivisor`: a closed
  subscheme satisfying `Stacks.Divisors.IsNormalizationCrossingsDivisor` is a normal crossings
  divisor.
* `Stacks.Divisors.isNormalCrossingsDivisor_iff_isNormalizationCrossingsDivisor`: a closed
  subscheme is a normal crossings divisor if and only if it satisfies
  `Stacks.Divisors.IsNormalizationCrossingsDivisor`.
* `Stacks.Divisors.isNormalCrossingsDivisor_iff_reduced_unramified_normalization`: the same
  equivalence with the conditions on the normalization written out.

## References

* [Stacks Project, Tag 0CBR](https://stacks.math.columbia.edu/tag/0CBR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Divisors

/-- On a locally Noetherian scheme, a closed subscheme satisfying
`IsNormalizationCrossingsDivisor` is a normal crossings divisor. -/
theorem isNormalCrossingsDivisor_of_isNormalizationCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) (h : IsNormalizationCrossingsDivisor D) :
    IsNormalCrossingsDivisor D := by
  have : Unramified (divisorNormalization D) := h.2.choose
  refine isNormalCrossingsDivisor_of_forall_etaleChart D fun y => ?_
  obtain ⟨U, f, hU, hf, u, hu, m, A, ε, hopen, hclosed, hcover, hdisj, hiso⟩ :=
    exists_etaleChart_closedCover_divisorNormalization D (D.subschemeι y)
  have := hU
  have := hf
  exact ⟨U, f, hU, hf, ⟨u, hu⟩,
    isStrictNormalCrossingsDivisor_of_isNormalizationCrossingsDivisor_of_closedCover
      (D.comap f) (isNormalizationCrossingsDivisor_comap f D h) ε hopen hclosed hcover hdisj
      hiso⟩

/-- On a locally Noetherian scheme, a closed subscheme is a normal crossings divisor if and only if
it satisfies `IsNormalizationCrossingsDivisor`. -/
theorem isNormalCrossingsDivisor_iff_isNormalizationCrossingsDivisor {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) :
    IsNormalCrossingsDivisor D ↔ IsNormalizationCrossingsDivisor D :=
  ⟨isNormalizationCrossingsDivisor_of_isNormalCrossingsDivisor D,
    isNormalCrossingsDivisor_of_isNormalizationCrossingsDivisor D⟩

/-- Let `X` be a locally Noetherian scheme and let `D ⊂ X` be a
closed subscheme. The following are equivalent:

1. `D` is a normal crossings divisor in `X`;
2. `D` is reduced, the normalization `ν : D^ν ⟶ D` is unramified, and for every `n ≥ 1` the
   scheme `Z_n`, obtained from the `n`-fold fibre power of `ν` over `D` by deleting the fat
   diagonal, is regular and the morphism `Z_n ⟶ X` is a local complete intersection morphism
   whose conormal sheaf is locally free of rank `n`. -/
@[stacks 0CBR]
theorem isNormalCrossingsDivisor_iff_reduced_unramified_normalization {X : Scheme.{u}}
    [IsLocallyNoetherian X] (D : X.IdealSheafData) :
    IsNormalCrossingsDivisor D ↔
      (IsReduced D.subscheme ∧
        ∃ hν : Unramified (divisorNormalization D), ∀ n : ℕ, 1 ≤ n →
          AlgebraicGeometry.IsRegular (normalizationDistinct D n) ∧
            IsLocalCompleteIntersectionMorphism (normalizationDistinctToAmbient D n) ∧
              (letI : Unramified (divisorNormalization D) := hν
               haveI := formallyUnramified_normalizationDistinctToAmbient D n
               SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
                 (Stacks.Thickenings.universalConormalSheaf
                   (normalizationDistinctToAmbient D n)) n)) :=
  isNormalCrossingsDivisor_iff_isNormalizationCrossingsDivisor D

end Stacks.Divisors

end
