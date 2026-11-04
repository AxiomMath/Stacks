module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFreeFinite
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.BaseDegreeSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeVanishing

/-!
# The right-hand side of the degree-`n` row, and the row where it vanishes

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism of projective `n`-space over `S`. The degree-`n` row of the display of
[Stacks, Tag 01XW] reads

`Rⁿ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`.

This file identifies the right-hand side,

`Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_e, 𝒪_S) = (𝒪_S[T₀, …, Tₙ])_e`,

where `(𝒪_S[T₀, …, Tₙ])_e` is the free `𝒪_S`-module on the degree-`e` multidegrees in `n + 1`
variables, and both sides are zero in a negative degree. It proves the row in the range
`-n - 1 < d`, over an arbitrary base, and for every twist over an affine base.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `dualBaseDegreeSheafIso`: the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_e` is `(𝒪_S[T₀, …, Tₙ])_e`.
* `rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_lt`: the degree-`n` row of [Stacks, Tag 01XW]
  in the range `-n - 1 < d`, over an arbitrary base.
* `rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_isAffine`: the degree-`n` row of
  [Stacks, Tag 01XW] over an affine base, for every twist.

## Main results

* `finite_monomialIndex`: there are finitely many multidegrees of a given total degree in
  `n + 1` variables.
* `isZero_dualSheaf_baseDegreeSheaf_of_neg`: the right-hand side of the row is the zero sheaf
  when `-n - 1 - d < 0`.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ReflexiveModules
  (dualSheaf dualSheafFreeIso isZero_dualSheaf_of_isZero)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- There are finitely many multidegrees of a given total degree in `n + 1` variables. -/
instance finite_monomialIndex (n : ℕ) (e : ℤ) : Finite (MonomialIndex.{u} n e) := by
  rcases lt_or_ge e 0 with he | he
  · have : IsEmpty (MonomialIndex.{u} n e) := isEmpty_monomialIndex n he
    infer_instance
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le he
    have : Finite {x : ULift.{u} (Fin (n + 1)) →₀ ℕ | x.degree = k} :=
      (Finsupp.finite_of_degree_eq k).to_subtype
    exact Finite.of_equiv _ (MonomialIndex.natEquiv.{u} n k).symm

/-- The `𝒪_S`-dual `Hom_{𝒪_S}(-, 𝒪_S)` of `(𝒪_S[T₀, …, Tₙ])_e` is `(𝒪_S[T₀, …, Tₙ])_e`. -/
def dualBaseDegreeSheafIso (n : ℕ) (S : Scheme.{u}) (e : ℤ) :
    dualSheaf (baseDegreeSheaf n S e) ≅ baseDegreeSheaf n S e :=
  dualSheafFreeIso S (MonomialIndex.{u} n e)

/-- The `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_e` is the zero sheaf when `e < 0`. -/
theorem isZero_dualSheaf_baseDegreeSheaf_of_neg (n : ℕ) (S : Scheme.{u}) {e : ℤ} (he : e < 0) :
    IsZero (dualSheaf (baseDegreeSheaf n S e)) :=
  isZero_dualSheaf_of_isZero S (isZero_baseDegreeSheaf_of_neg n S he)

/-- **The degree-`n` row of [Stacks, Tag 01XW] in the range `-n - 1 < d`**: for the structure
morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S`, for `n = m + 1 ≥ 1` and for an integer `d`
with `-n - 1 < d`,

`Rⁿ f_* 𝒪(d) ≅ Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`. -/
def rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_lt (m : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd : -((m + 1 : ℕ) : ℤ) - 1 < d) :
    (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) S d)) ≅
      dualSheaf (baseDegreeSheaf (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1 - d)) :=
  (isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m S hd).isoZero ≪≫
    (isZero_dualSheaf_baseDegreeSheaf_of_neg (m + 1) S
      (show -((m + 1 : ℕ) : ℤ) - 1 - d < 0 by omega)).isoZero.symm

/-- **The degree-`n` row of [Stacks, Tag 01XW] over an affine base**, in its whole range of
twists: for `W` affine, for `n = m + 1 ≥ 1` and for every integer `d`,

`Rⁿ f_* 𝒪(d) ≅ Hom_{𝒪_W}((𝒪_W[T₀, …, Tₙ])_{-n-1-d}, 𝒪_W)`. -/
def rightDerivedPlusTopIsoDualBaseDegreeSheaf_of_isAffine (m : ℕ) (W : Scheme.{u}) [IsAffine W]
    (d : ℤ) :
    (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) W ↘ W)).rightDerivedPlus
        ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) W d)) ≅
      dualSheaf (baseDegreeSheaf (m + 1) W (-((m + 1 : ℕ) : ℤ) - 1 - d)) :=
  rightDerivedPlusPushforwardTwistOverTopIso m W d ≪≫
    (dualBaseDegreeSheafIso (m + 1) W (-((m + 1 : ℕ) : ℤ) - 1 - d)).symm

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
