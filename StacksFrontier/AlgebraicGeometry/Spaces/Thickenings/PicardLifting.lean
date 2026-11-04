module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PicardSequence

/-!
# Lifting Picard classes along a first-order thickening of algebraic spaces

Let `X ⊂ X'` be a first-order thickening of algebraic spaces with ideal sheaf `𝓘`. The exact
sequence of Stacks 0DNM, `Pic(X') → Pic(X) → H²(X, 𝓘)`, shows that every class on `X` lifts to
`X'` as soon as `H²(X, 𝓘)` vanishes.

## Main results

* `AlgebraicGeometry.Space.surjective_picardRestriction_of_subsingleton`: if `H²(X, 𝓘)` is
  trivial, then `Pic(X') → Pic(X)` is surjective.

## References

* [Stacks Project, Tag 0DNM](https://stacks.math.columbia.edu/tag/0DNM)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}
  (hG : IsFirstOrderThickening B S hS X G)

/-- **Picard classes lift along a first-order thickening when `H²(X, 𝓘) = 0`**: then the
restriction `Pic(X') → Pic(X)` is surjective. -/
theorem surjective_picardRestriction_of_subsingleton
    (h : Subsingleton (Sheaf.H.{u + 1}
      (thickeningUnitsShortComplex B S hS hG).X₁ 2)) :
    Function.Surjective (picardRestriction B S hS hG) := fun c =>
  ((exact_picardRestriction B S hS hG) c).mp (Subsingleton.elim _ _)

end AlgebraicGeometry.Space

end
