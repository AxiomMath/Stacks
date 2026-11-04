module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeRow

/-!
# The right-hand side of the degree-`n` row at the twist `d = -n-1`

Let `S` be a scheme and `n = m + 1 ≥ 1`. The degree-`n` row of the display of
[Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`,

and at the twist `d = -n - 1` the complementary degree `-n - 1 - d` is zero. The degree-zero part
of a polynomial algebra is its ring of constants, so the sheaf on the right is `𝒪_S` and the row
reads

`Rⁿ f_* 𝒪(-n-1) = 𝒪_S`.

This file identifies that right-hand side: the degree-zero multidegrees in `n + 1` variables form
a one-element set — the zero multidegree is the only one of total degree zero — so
`(𝒪_S[T₀, …, Tₙ])_0` is the free `𝒪_S`-module on one generator, which is `𝒪_S`, and its dual is
`𝒪_S` again.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `baseDegreeSheafZeroIso`: **`(𝒪_S[T₀, …, Tₙ])_0 ≅ 𝒪_S`.**
* `dualBaseDegreeSheafZeroIso`: **the right-hand side of the degree-`n` row at `d = -n - 1` is
  `𝒪_S`.**

## Main results

* `unique_monomialIndex_zero`: the zero multidegree is the only multidegree of total degree zero.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

/-! ### The degree-zero multidegrees -/

/-- **The zero multidegree is the only multidegree of total degree zero.** -/
instance unique_monomialIndex_zero (n : ℕ) : Unique (MonomialIndex.{u} n 0) where
  default := ⟨0, by simp⟩
  uniq a := Subtype.ext ((Finsupp.degree_eq_zero_iff a.1).1 (by exact_mod_cast a.2))

/-- **`(𝒪_S[T₀, …, Tₙ])_0 ≅ 𝒪_S`**: the degree-zero part of a polynomial algebra is its ring of
constants. -/
def baseDegreeSheafZeroIso (n : ℕ) (S : Scheme.{u}) :
    baseDegreeSheaf n S 0 ≅ SheafOfModules.unit S.ringCatSheaf :=
  Stacks.SheafOfModules.Invertible.freeUniqueIso (MonomialIndex.{u} n 0)

/-- **The right-hand side of the degree-`n` row of [Stacks, Tag 01XW] at the twist `d = -n - 1` is
`𝒪_S`**: the dual of `(𝒪_S[T₀, …, Tₙ])_0` is `𝒪_S`. -/
def dualBaseDegreeSheafZeroIso (n : ℕ) (S : Scheme.{u}) :
    dualSheaf (baseDegreeSheaf n S 0) ≅ SheafOfModules.unit S.ringCatSheaf :=
  dualBaseDegreeSheafIso n S 0 ≪≫ baseDegreeSheafZeroIso n S

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
