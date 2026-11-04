module

public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.Picard.DegreeAtLeastGenus
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic

/-!
# The Euler characteristic of the sheaf of an effective divisor on a curve

Let `X` be a proper integral scheme of dimension at most one over a field `k` with
`Γ(X, 𝒪_X) = k`, of genus `g`, and let `D ⊂ X` be an effective Cartier divisor whose ring of
functions has dimension `d` over `k`. Then

`dim_k H⁰(X, 𝒪_X(D)) - dim_k H¹(X, 𝒪_X(D)) = d + 1 - g`.

## Main results

* `AlgebraicGeometry.euler_divisorSheaf_eq`: the Euler characteristic of `𝒪_X(D)` is `d + 1 - g`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Stacks.Divisors (divisorSheaf IsEffectiveCartierDivisor)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Let `X` be a proper integral scheme of dimension at most one over a field `k` with
`Γ(X, 𝒪_X) = k`, of genus `g`, and `D ⊂ X` an effective Cartier divisor. Then
`dim_k H⁰(X, 𝒪_X(D)) - dim_k H¹(X, 𝒪_X(D)) = dim_k Γ(D, 𝒪_D) + 1 - g`. -/
theorem euler_divisorSheaf_eq [IsProper f] [IsIntegral X] (hdim : topologicalKrullDim X ≤ 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    (Module.finrank k (cohomologyOverField k f (divisorSheaf D) 0) : ℤ) -
        Module.finrank k (cohomologyOverField k f (divisorSheaf D) 1) =
      Module.finrank k Γ(D.subscheme, ⊤) + 1 - genus f := by
  have hL := Stacks.Divisors.isInvertible_divisorSheaf D
  have hdeg := invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections k f hdim D
  have hsub := @invertibleCurveDegree_eq_sub_of_isZero k _ X f _ hdim (divisorSheaf D) hL
    (isZero_cohomologyOverField_of_two_le' k f hdim _)
    (isZero_cohomologyOverField_of_two_le' k f hdim _)
  rw [finrank_cohomologyOverField_unit_zero_eq_one f,
    ← genus_eq_finrank_cohomologyOverField_unit_one' k f] at hsub
  omega

end AlgebraicGeometry
