module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupTwistSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Twisting by small multiples of the exceptional divisor does not change `Rb_*`

Fix a ring `R`, `S = Spec R`, integers `m ≥ 0` and `n ≥ 1`, the coordinate closed immersion
`Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the blowing up `b : L ⟶ X` of `X` along `Z` and its exceptional
divisor `E`. This file proves [Stacks, Tag 0G5H]: for a locally free `𝒪_X`-module `ℰ` and
`0 ≤ i ≤ n - 1` the canonical map

`ℰ ⟶ Rb_*(b^*ℰ ⊗_{𝒪_L} 𝒪_L(iE))`

is an isomorphism in `D(𝒪_X)`.

`ℰ` is locally free in the sense of `SheafOfModules.IsLocallyFree`: locally a free module on a set
of generators of arbitrary cardinality, as in the source.

The map is `Stacks.DeRham.TwistDerived.twistDerivedMap`: the unit `ℰ ⟶ Rb_*b^*ℰ` followed by
`Rb_*` of the inclusion `b^*ℰ ⟶ b^*ℰ ⊗ 𝒪_L(iE)` given by the canonical section of `𝒪_L(iE)`.

## The proof

As in the source, the projection formula reduces the statement to `ℰ = 𝒪_X`
(`Stacks.DeRham.TwistDerived.isIso_twistDerivedMap_of_isLocallyFree_of_bijective`: locally on
`X` the module `ℰ` is free, and the direct images commute with direct sums since `b` is
quasi-compact and quasi-separated), and since `X` is affine the
case `ℰ = 𝒪_X` is the statement that

* `a ↦ b^♯(a) · 1_{iE}` is a bijection from the functions on `X` onto the global sections of
  `𝒪_L(iE)` — `Stacks.DeRham.CoordinateCech.bijective_globalTwist`, and
* `H^q(L, 𝒪_L(iE)) = 0` for `q > 0` —
  `Stacks.DeRham.CoordinateCech.isZero_rightDerived_twistSheaf`.

Both are computed on the Čech complex of the `n` standard charts of `L`, inside the Laurent
polynomials in the `y`'s, which is where `0 ≤ i ≤ n - 1` is used. The source computes the same
cohomology through the line bundle `L ⟶ P = 𝐏^{n-1}_Z` and the cohomology of the twists on `P`
([Stacks, Tag 01XT]); the Čech complex of the charts of `L` is the direct sum over the twists of
the Čech complexes of the charts of `P`, and the vanishing used is the same.

## Main results

* `Stacks.DeRham.isIso_coordinateBlowupTwistDerivedMap`: **[Stacks, Tag 0G5H].**

## Implementation notes

The tensor product is written `b^*ℰ ⊗ 𝒪_L(iE)` in the source's order, and `𝒪_L(iE)` is
`Stacks.Divisors.invertibleSheaf'` of the `i`-th power of the exceptional ideal sheaf, the
ideal sheaf of the divisor `iE`.

## References

* [Stacks Project, Tag 0G5H](https://stacks.math.columbia.edu/tag/0G5H)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **Stacks Project, Tag 0G5H.** Let `b : L ⟶ X = 𝐀^{m+n}_R` be the blowing up of affine space
along the coordinate subspace `𝐀^m_R`, `n ≥ 1`, with exceptional divisor `E`. For every locally
free `𝒪_X`-module `ℰ`, of any rank, and every `0 ≤ i ≤ n - 1` the canonical map
`ℰ ⟶ Rb_*(b^*ℰ ⊗ 𝒪_L(iE))` is an isomorphism in `D(𝒪_X)`. -/
@[stacks 0G5H]
theorem isIso_coordinateBlowupTwistDerivedMap (hn : 1 ≤ n) (i : ℕ) (hi : i ≤ n - 1)
    (E : (coordinateAmbient R m n).Modules) [SheafOfModules.IsLocallyFree.{u, u, u} E] :
    IsIso (TwistDerived.twistDerivedMap (coordinateBlowupToAmbient R m n)
      (coordinateExceptional R m n ^ i) E) := by
  have hn' : 0 < n := hn
  have hi' : i < n := by omega
  have : Stacks.Divisors.IsEffectiveCartierDivisor (coordinateExceptional R m n ^ i) :=
    Stacks.Divisors.isEffectiveCartierDivisor_pow inferInstance i
  exact TwistDerived.isIso_twistDerivedMap_of_isLocallyFree_of_bijective _ _
    (CoordinateCech.bijective_globalTwist R m n hn' i hi')
    (fun q hq => CoordinateCech.isZero_rightDerived_twistSheaf R m n hn' i hi' q hq) E

end Stacks.DeRham

end
