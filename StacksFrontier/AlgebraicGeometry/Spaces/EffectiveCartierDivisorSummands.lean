module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Summands
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv

/-!
# The summands of an effective Cartier divisor on an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`Z, Y ⊆ X` be closed subspaces with defining ideal sheaves `ℐ` and `𝒥`.  Following Stacks 083W,
if the product `ℐ𝒥` cuts out an effective Cartier divisor `D ⊆ X`, then `Z` and `Y` are
themselves effective Cartier divisors and `D` is the sum `Z + Y` of Stacks 083U.

## Main results

* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_left_of_sumClosedSubspaces` and
  `AlgebraicGeometry.Space.isEffectiveCartierDivisor_right_of_sumClosedSubspaces`: the two
  effectivity assertions of **Stacks 083W**.
* `AlgebraicGeometry.Space.eq_sumClosedSubspaces_of_definingIdealAt_eq_mul`: the identification
  `D = Z + Y` of **Stacks 083W**.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_definingIdealAt_eq_mul`:
  **Stacks 083W**, the three assertions together.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_mul_chartKer_of_sumClosedSubspaces`: on the
  étale scheme chart on which the sum is formed, the product of the chart ideal sheaves of the
  two closed subspaces is an effective Cartier ideal sheaf.
* `AlgebraicGeometry.Space.isEffectiveCartierDivisor_of_chartKer_atlasHom`: conversely, a closed
  subspace whose chart ideal sheaf on that chart is an effective Cartier ideal sheaf is an
  effective Cartier divisor.

## Implementation notes

The reduction to schemes is the equivalence of parts (1), (2) and (3) of Stacks 083C.  The sum
`Z + Y` is formed on the surjective étale scheme chart `AlgebraicGeometry.Space.atlasHom`, and
on that chart its ideal sheaf is the product of the chart ideal sheaves of `Z` and `Y` by
`AlgebraicGeometry.Space.chartKer_sumClosedSubspaces`.  Part (3) of Stacks 083C turns effective
Cartier-ness of `Z + Y` into effective Cartier-ness of that product on the chart, the
scheme-level Stacks 07ZV splits the product, and part (2) of Stacks 083C — for which the one
chart `atlasHom` suffices, being surjective — carries each factor back to `X`.

The hypothesis "`ℐ𝒥` defines `D`" is taken in the chartwise form: on every *affine* étale chart
lying over `atlasHom`, the defining ideal of `D` is the product of the defining ideals of `Z`
and `Y`.  This is how the library has to say it, because it has no construction of a closed
subspace from an ideal sheaf on `X` itself — that is the surjectivity half of Stacks 03MB, see
the section "What is not proved" of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedSubspaceIdealBijection.lean`.  The form is not
weaker: by `AlgebraicGeometry.Space.eq_sumOfChart_of_definingIdealAt` that chartwise formula
pins `D` down among all closed subspaces of `X`, so it says exactly that `D` is the closed
subspace cut out by `ℐ𝒥`, and the identification `D = Z + Y` follows from it with no hypothesis
on `D` beyond it.

## References

* [Stacks Project, Tag 083W](https://stacks.math.columbia.edu/tag/083W)
* [Stacks Project, Tag 083U](https://stacks.math.columbia.edu/tag/083U)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 07ZV](https://stacks.math.columbia.edu/tag/07ZV)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (Z Y D : ClosedSubspaces B S hS X.1)

/-- **The sum read on the chart on which it is formed.** If the sum `Z + Y` is an effective
Cartier divisor on `X`, then on the surjective étale scheme chart
`AlgebraicGeometry.Space.atlasHom` the product of the chart ideal sheaves of `Z` and `Y` is an
effective Cartier ideal sheaf: that product is the chart ideal sheaf of the sum, and part (3)
of Stacks 083C computes the latter. -/
theorem isEffectiveCartierDivisor_mul_chartKer_of_sumClosedSubspaces
    (h : IsEffectiveCartierDivisor B S hS X (sumClosedSubspaces B S hS X Z Y)) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (chartKer B S hS X Z (atlasHom B S hS X) *
        chartKer B S hS X Y (atlasHom B S hS X)) := by
  have hchart : Stacks.Divisors.IsEffectiveCartierDivisor
      (chartKer B S hS X (sumClosedSubspaces B S hS X Z Y) (atlasHom B S hS X)) :=
    (isSchemeEffectiveCartierPullback_iff B S hS X _ _ _).1
      (hasEffectiveCartierEtalePullbacks_of_isEffectiveCartier B S hS X _ h _ _
        (isEtale_of_presheaf_etale B S hS (atlasHom_etale B S hS X)))
  rwa [chartKer_sumClosedSubspaces] at hchart

/-- **Effective Cartier-ness is read off the chart of an atlas.** A closed subspace whose chart
ideal sheaf on the surjective étale scheme chart `AlgebraicGeometry.Space.atlasHom` is an
effective Cartier ideal sheaf is an effective Cartier divisor on `X`; this is part (2) of
Stacks 083C at that one chart. -/
theorem isEffectiveCartierDivisor_of_chartKer_atlasHom
    (hZ : Stacks.Divisors.IsEffectiveCartierDivisor (chartKer B S hS X Z (atlasHom B S hS X))) :
    IsEffectiveCartierDivisor B S hS X Z :=
  isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS X Z
    ⟨atlasObj B S hS X, atlasHom B S hS X,
      isEtale_of_presheaf_etale B S hS (atlasHom_etale B S hS X),
      sumAtlasChart_isSurjective B S hS X,
      (isSchemeEffectiveCartierPullback_iff B S hS X Z _ _).2 hZ⟩

/-- **Stacks 083W.** If the sum `Z + Y` of two closed subspaces of an algebraic space is an
effective Cartier divisor, then so is the first summand `Z`. -/
@[stacks 083W "effectivity of the first closed subspace"]
theorem isEffectiveCartierDivisor_left_of_sumClosedSubspaces
    (h : IsEffectiveCartierDivisor B S hS X (sumClosedSubspaces B S hS X Z Y)) :
    IsEffectiveCartierDivisor B S hS X Z :=
  isEffectiveCartierDivisor_of_chartKer_atlasHom B S hS X Z
    (isEffectiveCartierDivisor_left_of_mul _ _
      (isEffectiveCartierDivisor_mul_chartKer_of_sumClosedSubspaces B S hS X Z Y h))

/-- **Stacks 083W.** If the sum `Z + Y` of two closed subspaces of an algebraic space is an
effective Cartier divisor, then so is the second summand `Y`. -/
@[stacks 083W "effectivity of the second closed subspace"]
theorem isEffectiveCartierDivisor_right_of_sumClosedSubspaces
    (h : IsEffectiveCartierDivisor B S hS X (sumClosedSubspaces B S hS X Z Y)) :
    IsEffectiveCartierDivisor B S hS X Y :=
  isEffectiveCartierDivisor_of_chartKer_atlasHom B S hS X Y
    (isEffectiveCartierDivisor_right_of_mul _ _
      (isEffectiveCartierDivisor_mul_chartKer_of_sumClosedSubspaces B S hS X Z Y h))

/-- **Stacks 083W.** A closed subspace `D` of an algebraic space whose defining ideal is, on
every affine étale chart lying over the chart carrying the sum, the product of the defining
ideals of `Z` and `Y` is the sum `Z + Y` of Stacks 083U: that chartwise formula is what
`AlgebraicGeometry.Space.definingIdealAt_sumClosedSubspaces_of_isAffine` asserts of the sum, and
it determines a closed subspace. -/
@[stacks 083W "identification with the sum"]
theorem eq_sumClosedSubspaces_of_definingIdealAt_eq_mul
    (hD : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ sumAtlasChart B S hS X) →
        definingIdealAt B S hS X D (op A) =
          definingIdealAt B S hS X Z (op A) * definingIdealAt B S hS X Y (op A)) :
    D = sumClosedSubspaces B S hS X Z Y := by
  refine eq_sumOfChart_of_definingIdealAt B S hS X (atlasHom_surjective B S hS X)
    (atlasHom_etale B S hS X) Z Y D fun A hA m => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj A.1.left) := hA
  exact ((hD A hA m).trans
    (definingIdealAt_sumClosedSubspaces_of_isAffine B S hS X Z Y A m).symm).trans
    (definingIdealAt_sumClosedSubspaces B S hS X Z Y A m)

/-- **Stacks 083W.** Let `Z, Y` be two closed subspaces of an algebraic space `X` with defining
ideal sheaves `ℐ` and `𝒥`.  If `ℐ𝒥` defines an effective Cartier divisor `D ⊆ X`, then `Z` and
`Y` are effective Cartier divisors and `D = Z + Y`. -/
@[stacks 083W]
theorem isEffectiveCartierDivisor_of_definingIdealAt_eq_mul
    (hD : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) →
      (A ⟶ sumAtlasChart B S hS X) →
        definingIdealAt B S hS X D (op A) =
          definingIdealAt B S hS X Z (op A) * definingIdealAt B S hS X Y (op A))
    (h : IsEffectiveCartierDivisor B S hS X D) :
    IsEffectiveCartierDivisor B S hS X Z ∧ IsEffectiveCartierDivisor B S hS X Y ∧
      D = sumClosedSubspaces B S hS X Z Y := by
  have hsum : D = sumClosedSubspaces B S hS X Z Y :=
    eq_sumClosedSubspaces_of_definingIdealAt_eq_mul B S hS X Z Y D hD
  rw [hsum] at h
  exact ⟨isEffectiveCartierDivisor_left_of_sumClosedSubspaces B S hS X Z Y h,
    isEffectiveCartierDivisor_right_of_sumClosedSubspaces B S hS X Z Y h, hsum⟩

end AlgebraicGeometry.Space

end
