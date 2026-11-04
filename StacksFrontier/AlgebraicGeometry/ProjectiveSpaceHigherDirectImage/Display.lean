module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZeroRow
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeRowGeneral
import StacksCore.Tactic.StacksAttribute

/-!
# The display of the higher direct images of the twists on projective space

Let `S` be a scheme, let `n = m + 1 ≥ 1`, let `d` be an integer and let `f : ℙⁿ_S ⟶ S` be the
structure morphism of projective `n`-space over `S`. The display of [Stacks, Tag 01XW] reads

`Rᵠ f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d`                              if `q = 0`,
`Rᵠ f_* 𝒪(d) = 0`                                               if `q ≠ 0, n`,
`Rᵠ f_* 𝒪(d) = Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`        if `q = n`,

and this module states the three rows at once, in
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage`
`.rightDerivedPlusPushforwardTwistOverDisplay`. The two identifications are isomorphisms of
`𝒪_S`-modules and the vanishing is quantified over all the degrees `q` it speaks about, so the
three cases of the source are the three components of the statement. No hypothesis is placed on
`S` or on `d`.

## Why the statement is at `n ≥ 1`

The display is inconsistent at `n = 0`, and not as an artefact of the formalisation. On
`ℙ⁰_S = Proj 𝒪_S[T₀]` the variable `T₀` is invertible, so `𝒪(d) ≅ 𝒪_S` for every `d`, the
structure morphism is an isomorphism, and `f_* 𝒪(d) ≅ 𝒪_S` in every twist. The degrees `q = 0`
and `q = n` of the display coincide there, so its first and third rows both apply to that one
sheaf, and they disagree: the
first gives `(𝒪_S[T₀])_d`, which is free of rank one for `d ≥ 0` and zero for `d < 0`, while the
third gives `Hom_{𝒪_S}((𝒪_S[T₀])_{-1-d}, 𝒪_S)`, which is free of rank one for `d ≤ -1` and zero
for `d ≥ 0`. Neither row is correct in both ranges. This is recorded in the library at
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MiddleVanishing`
`.isZero_rightDerivedPlus_pushforward_twistOver_zero_of_neg`, whose hypothesis `n ≥ 1` cannot be
dropped, and at
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.isIso_toPushforwardTwistOver`, whose
hypothesis is `0 ≤ d ∨ 0 < n`. So `n ≥ 1` is the range in which the source's display is a
consistent assertion, and stating it there is a faithful reading rather than a weakening.

That hypothesis `0 ≤ d ∨ 0 < n` of the degree-zero row is then discharged by `Or.inr`, so the
statement below needs no assumption on the twist `d`: all three rows hold for every integer
twist, negative ones included.

## Main definitions

* `rightDerivedPlusPushforwardTwistOverDisplay`: **the display of [Stacks, Tag 01XW]**, its
  three rows in one statement, for every scheme `S`, every `n = m + 1 ≥ 1` and every twist `d`.

## Implementation notes

The three rows are proved in the sibling modules
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/DegreeZeroRow.lean`,
`…/MiddleVanishing.lean` and `…/TopDegreeRowGeneral.lean`; this module only assembles them, and
contains no mathematics not already in them.

The three rows are conjoined with `PProd` rather than `Prod`: the two identifications are
isomorphisms, hence data, while the vanishing is a proposition, and `Prod` does not accept a
factor in `Prop` beside a factor in `Type`. Nothing is lifted or bundled behind an abbreviation,
so the whole display is the type of the one declaration below.

`HasDerivedCategory.standard` is installed at priority `2000`, as in those three modules, so that
`CategoryTheory.Functor.rightDerivedPlus` below is read in the same model of the derived category
as in each of them; at the default priority the globally declared locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is preferred instead, whose morphisms live
one universe lower, and the three rows are then statements about three different functors.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf)

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance 2000] HasDerivedCategory.standard

/-- **The display of [Stacks, Tag 01XW].** For the structure morphism `f : ℙⁿ_S ⟶ S` of
projective `n`-space over an arbitrary scheme `S`, with `n = m + 1 ≥ 1`, and for every integer
twist `d`:

* `R⁰ f_* 𝒪(d) ≅ (𝒪_S[T₀, …, Tₙ])_d`, the degree-`d` part of the polynomial algebra on the base;
* `Rᵠ f_* 𝒪(d) = 0` for every integer `q` with `q ≠ 0` and `q ≠ n`;
* `Rⁿ f_* 𝒪(d) ≅ Hom_{𝒪_S}((𝒪_S[T₀, …, Tₙ])_{-n-1-d}, 𝒪_S)`.

The three components are `baseDegreeSheafIsoRightDerivedPushforwardTwistOver`, whose hypothesis
`0 ≤ d ∨ 0 < n` is discharged by `n = m + 1 ≥ 1`, then
`MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne`, then
`rightDerivedPlusTopIsoDualBaseDegreeSheaf`.

The source's display is inconsistent at `n = 0`, where its first and third rows apply to the same
degree and disagree, so `n ≥ 1` is the range in which it asserts something; see the module
docstring. -/
@[stacks 01XW "the display whole, at n = m + 1 >= 1, for every scheme S and every integer twist \
d: R^0 f_* O(d) = (O_S[T_0, ..., T_n])_d, R^q f_* O(d) = 0 for every q /= 0, n, and R^n f_* O(d) \
= Hom_{O_S}((O_S[T_0, ..., T_n])_{-n-1-d}, O_S). At n = 0 the display's first and third rows \
speak about the same degree and disagree, so n >= 1 is the range in which it is a consistent \
assertion"]
def rightDerivedPlusPushforwardTwistOverDisplay (m : ℕ) (S : Scheme.{u}) (d : ℤ) :
    PProd (baseDegreeSheaf (m + 1) S d ≅
        ((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus 0).obj
          (twistOver (m + 1) S d))
      (PProd (∀ q : ℤ, q ≠ 0 → q ≠ ((m + 1 : ℕ) : ℤ) →
            IsZero (((Scheme.Modules.pushforward
              (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus q).obj
                (twistOver (m + 1) S d)))
        (((Scheme.Modules.pushforward (projectiveSpaceOver (m + 1) S ↘ S)).rightDerivedPlus
              ((m + 1 : ℕ) : ℤ)).obj (twistOver (m + 1) S d) ≅
          dualSheaf (baseDegreeSheaf (m + 1) S (-((m + 1 : ℕ) : ℤ) - 1 - d)))) :=
  ⟨baseDegreeSheafIsoRightDerivedPushforwardTwistOver (m + 1) S (d := d)
      (Or.inr (Nat.succ_pos m)),
    fun q hq0 hqn =>
      MiddleVanishing.isZero_rightDerivedPlus_pushforward_twistOver_of_ne (m + 1) S d q hq0 hqn,
    rightDerivedPlusTopIsoDualBaseDegreeSheaf m S d⟩

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
