module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsChartMono
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsPoleBound
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorTwistedRetraction

/-!
# The second canonical map on forms of the coordinate blowup, and the composite

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDifferentialFormsComparison` —
a ring `R`, `S = Spec(R)`, the coordinate closed immersion `Z = 𝐀^m_S ⟶ 𝐀^{m+n}_S = X`, the
blowup `b : L ⟶ X` of `X` along `Z` and its exceptional divisor `E ⊆ L` — [Stacks, Tag 0G5G]
asserts the existence of two canonical maps

`b^*Ω^a_{X/S} ⟶ Ω^a_{L/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)`

whose composite is the map induced by the inclusion `𝒪_L ⊆ 𝒪_L((n-1)E)`.  The first map is
`Stacks.DeRham.blowupFormsPullbackMap`, and it is a monomorphism by
`Stacks.DeRham.mono_blowupFormsPullbackMap`.

**This file constructs the second map and identifies the composite**, completing the tag.  Both
rest on the pole bound

`ℐ_{(n-1)E} · Ω^a_{L/S} ⊆ b^*Ω^a_{X/S}`,

which is `Stacks.DeRham.exceptionalPoleBound`: the containment lets the ideal sheaf act on
`Ω^a_{L/S}` with values in `b^*Ω^a_{X/S}`, and untwisting that action by the evaluation pairing
of `𝒪_L((n-1)E)` with `ℐ_{(n-1)E}` is `Stacks.Divisors.twistedRetraction`, whose composite with
the first map is computed by `Stacks.Divisors.comp_twistedRetraction`.

## Main definitions

* `Stacks.DeRham.blowupFormsTwistedComparison`: **the second canonical map**
  `Ω^a_{L/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)` of [Stacks, Tag 0G5G].

## Main results

* `Stacks.DeRham.blowupFormsPullbackMap_comp_twistedComparison`: **the composite of the two
  canonical maps is the map induced by the inclusion `𝒪_L ⊆ 𝒪_L((n-1)E)`.**

## Which blowup this is

`Stacks.DeRham.coordinateBlowup` is `AlgebraicGeometry.blowUp`, and
`Stacks.DeRham.coordinateExceptional` is the **reducible** `AlgebraicGeometry.exceptionalIdeal`
(`StacksFrontier/AlgebraicGeometry/Blowup/ReesAlgebra/BlowUp.lean`, line 76).  The library has a
second constant `Stacks.Blowup.exceptionalIdeal`
(`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, line 326) with the same body, and
two further blowup models, `Stacks.Blowup.blowUp` and `Stacks.Blowup.blowUpSpec`, with no
isomorphism to `AlgebraicGeometry.blowUp`.  Nothing stated for those applies here, and in
particular `Stacks.Blowup.negativeTwist'OverChartIso` is about `blowUpSpec`.

## References

* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DeRham

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- **Stacks Project, Tag 0G5G, the second canonical map.** The map
`Ω^a_{L/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)`.

This is `Stacks.Divisors.twistedRetraction` at the effective Cartier divisor `(n-1)E` and the
monomorphism `Stacks.DeRham.blowupFormsPullbackMap`: the pole bound
`Stacks.DeRham.exceptionalPoleBound` says that `ℐ_{(n-1)E} · Ω^a_{L/S} ⊆ b^*Ω^a_{X/S}`, which
lets the ideal sheaf act on `Ω^a_{L/S}` with values in `b^*Ω^a_{X/S}`, and untwisting that action
by the evaluation pairing of `𝒪_L((n-1)E)` with `ℐ_{(n-1)E}` gives a map into the twist. -/
@[stacks 0G5G "the second canonical map Ω^a_{L/S} ⟶ b^*Ω^a_{X/S} ⊗_{𝒪_L} 𝒪_L((n-1)E)"]
noncomputable def blowupFormsTwistedComparison (a : ℕ) :
    Scheme.Hom.relativeDifferentialForms (coordinateBlowupToBase R m n) a ⟶
      blowupFormsExceptionalTwist R m n a :=
  haveI := mono_blowupFormsPullbackMap R m n a
  Stacks.Divisors.twistedRetraction (coordinateExceptional R m n ^ (n - 1))
    (blowupFormsPullbackMap R m n a) (exceptionalPoleBound R m n a)

/-- **Stacks Project, Tag 0G5G, the composite of the two canonical maps.** The composite of
`Stacks.DeRham.blowupFormsPullbackMap` with `Stacks.DeRham.blowupFormsTwistedComparison` is the
map induced by the inclusion `𝒪_L ⊆ 𝒪_L((n-1)E)`.

That induced map is `Stacks.DeRham.blowupFormsCanonicalSection`, multiplication by the canonical
section of `𝒪_L((n-1)E)`; the identity is `Stacks.Divisors.comp_twistedRetraction`. -/
@[stacks 0G5G "the composite of the two maps is induced by the inclusion 𝒪_L ⊆ 𝒪_L((n-1)E)"]
theorem blowupFormsPullbackMap_comp_twistedComparison (a : ℕ) :
    blowupFormsPullbackMap R m n a ≫ blowupFormsTwistedComparison R m n a =
      blowupFormsCanonicalSection R m n a :=
  have := mono_blowupFormsPullbackMap R m n a
  Stacks.Divisors.comp_twistedRetraction (coordinateExceptional R m n ^ (n - 1))
    (blowupFormsPullbackMap R m n a) (exceptionalPoleBound R m n a)

end Stacks.DeRham

end
