module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TotalQuotient

/-!
# What "the total quotient presheaf is a sheaf" would say

Stacks Tag 0EMF (Lemma 31.24.6) describes the sheaf `𝒦_X` of meromorphic functions on a scheme
whose weakly associated points are generic points of irreducible components and whose
quasi-compact opens have finitely many irreducible components. In the source, and in
`AlgebraicGeometry.totalQuotientSheaf`, `𝒦_X` is by definition the *sheafification* of the
objectwise localization `TopCat.Presheaf.totalQuotientPresheaf`; the source nowhere asserts that
the presheaf is already a sheaf. Part (5) of the tag asserts that the presheaf and the sheaf
agree on *affine* opens.

This file records what the additional assertion "the total quotient presheaf is a sheaf" would
buy, namely part (5) for *every* open: `isLocalization_totalQuotientSheaf_obj_of_isSheaf`.

## Main results

* `isIso_toSheafify_of_isSheaf`: if the total quotient presheaf is a sheaf then the
  sheafification unit is an isomorphism, so nothing is added by sheafifying.
* `isLocalization_totalQuotientSheaf_obj_of_isSheaf`: consequently, for *every* open `U`, the
  ring `𝒦_X(U)` of meromorphic functions on `U` is a localization of `Γ(X, U)` at the sections
  whose germ at every point of `U` is a nonzerodivisor.

## Implementation notes

The two results are unconditional in `X`: no hypothesis of Tag 0EMF is used, because the
implication is formal. They are stated so that the strengthening can be examined against the
source, which asserts the localization statement only for affine opens.

The localization statement is false for every scheme with "too few" global functions: for
`X = ℙ¹_k` and `U = ⊤` the submonoid is `k \ {0}`, whose localization of `Γ(X, ⊤) = k` is `k`,
whereas `𝒦_X(⊤) = R(X) = k(t)` by part (6) of the same tag. So no scheme-level hypothesis of
Tag 0EMF can make the total quotient presheaf a sheaf: `ℙ¹_k` is integral, hence has `k` as its
only weakly associated point and that point is the generic point of its unique irreducible
component, and it is Noetherian, so both hypotheses of the tag hold.

## References

* [The Stacks Project, Lemma 31.24.6 (Tag 0EMF)](https://stacks.math.columbia.edu/tag/0EMF)
* [The Stacks Project, Tag 02AR](https://stacks.math.columbia.edu/tag/02AR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

open scoped nonZeroDivisors
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicCardResidues

variable (X : Scheme.{u})

/-- The submonoid of sections over an open set whose germ at each of its points is a
nonzerodivisor: the denominators of the total quotient presheaf. -/
abbrev germNonZeroDivisors (U : X.Opens) : Submonoid Γ(X, U) :=
  (X.presheaf.submonoidPresheafOfStalk
    (fun x ↦ (X.presheaf.stalk x)⁰)).obj (op U)

/-- If the total quotient presheaf of a scheme is a sheaf, then on *every* open set `U` the ring
`𝒦_X(U)` of meromorphic functions is a localization of `Γ(X, U)` at the sections whose germ at
every point of `U` is a nonzerodivisor.

Stacks Tag 0EMF asserts this only for `U` affine, which is its part (5). -/
theorem isLocalization_totalQuotientSheaf_obj_of_isSheaf
    (h : Presheaf.IsSheaf (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf) (U : X.Opens) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.presheaf.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    IsLocalization (germNonZeroDivisors X U)
      (X.totalQuotientSheaf.presheaf.obj (op U)) := by
  let algP : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    inferInstanceAs (Algebra Γ(X, U)
      ((X.presheaf.submonoidPresheafOfStalk
        fun x ↦ (X.presheaf.stalk x)⁰).localizationPresheaf.obj (op U)))
  have hlocP : IsLocalization (germNonZeroDivisors X U)
      (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    inferInstanceAs (IsLocalization (germNonZeroDivisors X U)
      ((X.presheaf.submonoidPresheafOfStalk
        fun x ↦ (X.presheaf.stalk x)⁰).localizationPresheaf.obj (op U)))
  have := isIso_toSheafify _ h
  exact (IsLocalization.isLocalization_iff_of_ringEquiv (germNonZeroDivisors X U)
    ((asIso ((toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op U))).commRingCatIsoToRingEquiv)).mp hlocP

end Stacks.AlgebraicGeometry.MeromorphicCardResidues

end
