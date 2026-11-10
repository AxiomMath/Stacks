module

public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.DimensionShifting
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeVanishing

/-!
# The twists of projective space that are acyclic for the structure morphism

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism. The display of [Stacks, Tag 01XW] leaves `Rᵠ f_* 𝒪(d)` possibly nonzero only
in the degrees `q = 0`, where the answer is `(𝒪_S[T₀, …, Tₙ])_d`, and `q = n`, where it is the
`𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`. Both of those index sets are empty in the band

`-n ≤ d ≤ -1`,

the first because `d` is negative and the second because `-n - 1 - d` is. So in that band **every**
higher direct image of `𝒪(d)` vanishes: the twist is acyclic for `f_*`. That is the content of
this file; all three cases are already proved, and what is added is their combination into the one
hypothesis that a resolution argument uses.

Together with the dimension-shifting isomorphism of
`StacksFrontier/AlgebraicGeometry/HigherDirectImage/DimensionShifting.lean` this gives: a short
exact sequence whose middle term is a twist in that band carries the degree-`q` higher direct image
of its right-hand term isomorphically onto the degree-`(q+1)` higher direct image of its left-hand
term. The Koszul resolution

`0 ⟶ 𝒪(-n-1) ⟶ 𝒪(-n)^{⊕ binom(n+1,n)} ⟶ ⋯ ⟶ 𝒪(-1)^{⊕ (n+1)} ⟶ 𝒪 ⟶ 0`

of the structure sheaf has all of its intermediate terms in that band, which is why its
dimension shifts compute `Rⁿ f_* 𝒪(-n-1)` from `f_* 𝒪`.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main results

* `isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic`: **`Rᵠ f_* 𝒪(d) = 0` in every degree
  `q`, for `-n ≤ d ≤ -1`**, over an arbitrary base.

## Main definitions

* `rightDerivedPlusShiftIsoOfTwistMiddle`: **the dimension shift across a short exact sequence
  whose middle term is such a twist**, `Rᵠ f_* ℱ₃ ≅ R ᵠ⁺¹ f_* ℱ₁`.

## Implementation notes

The three cases are `isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt` at `q = n`, where
`-n ≤ d` is exactly the hypothesis `-n - 1 < d`;
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing`
`.isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg` at `q = 0`, where `d < 0` is the
hypothesis; and
`…MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne` elsewhere, which needs no
hypothesis on `d` at all. The hypothesis `n ≥ 1` is the one the degree-zero case carries: on
`ℙ⁰_S = S` the two rows of the display coincide and no twist is acyclic.

The middle term of the short exact sequence is given up to isomorphism rather than on the nose,
which is the form a resolution produces it in: the terms of a complex are direct sums, and a
direct sum over a one-element index type is only isomorphic to its summand.

`CategoryTheory.HasDerivedCategory.standard` is installed as a local instance at priority `2000`,
as in the modules whose statements are composed here.

No `stacks` attribute is attached: the vanishing row of [Stacks, Tag 01XW] carries its attribute
on `…MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne`, and what is below is a
combination of that row with the two already-proved cases of the other two rows.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance 2000] HasDerivedCategory.standard

/-- **Every higher direct image of `𝒪(d)` vanishes in the band `-n ≤ d ≤ -1`**, for the structure
morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S` and for `n = m + 1 ≥ 1`: both rows of the
display of [Stacks, Tag 01XW] that could be nonzero are indexed by an empty set of monomials
there, the degree-zero row because `d < 0` and the degree-`n` row because `-n - 1 - d < 0`. -/
theorem isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic (m : ℕ) (S : Scheme.{u})
    {d : ℤ} (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d) (hd₂ : d < 0) (q : ℤ) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
      q).obj (twistOver (m + 1) S d)) := by
  by_cases hq : q = ((m + 1 : ℕ) : ℤ)
  · subst hq
    exact isZero_rightDerivedPlus_pushforward_twistOver_top_of_lt m S (by omega)
  · by_cases hq0 : q = 0
    · subst hq0
      exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg (m + 1)
        (Nat.succ_pos m) S d hd₂
    · exact MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S d q
        hq0 hq

/-- **The dimension shift across a short exact sequence whose middle term is an acyclic twist.**
For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of sheaves of modules on `ℙⁿ_S` whose middle
term is isomorphic to `𝒪(d)` with `-n ≤ d ≤ -1`, the connecting morphism of the long exact
sequence of the higher direct images is an isomorphism

`Rᵠ f_* ℱ₃ ≅ R ᵠ⁺¹ f_* ℱ₁`

in every degree `q`. -/
def rightDerivedPlusShiftIsoOfTwistMiddle (m : ℕ) (S : Scheme.{u}) {d : ℤ}
    (hd₁ : -((m + 1 : ℕ) : ℤ) ≤ d) (hd₂ : d < 0)
    {T : ShortComplex (projectiveSpaceOver (m + 1) S).Modules} (hT : T.ShortExact)
    (e : T.X₂ ≅ twistOver (m + 1) S d) (q : ℕ) :
    ((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        (q : ℤ)).obj T.X₃ ≅
      ((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        ((q + 1 : ℕ) : ℤ)).obj T.X₁ :=
  HigherDirectImage.rightDerivedPlusShiftIso (projectiveSpaceOver (m + 1) S ↘ S) hT q
    ((isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic m S hd₁ hd₂ (q : ℤ)).of_iso
      (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        (q : ℤ)).mapIso e))
    ((isZero_rightDerivedPlus_pushforward_twistOver_of_acyclic m S hd₁ hd₂
        ((q + 1 : ℕ) : ℤ)).of_iso
      (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
        ((q + 1 : ℕ) : ℤ)).mapIso e))

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
