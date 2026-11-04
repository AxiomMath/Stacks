module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.SectionRange

/-!
# The two distinguished divisors of a family over the projective line

Let `f : X ⟶ S` be a morphism of schemes and let `W ⊆ X ×_S ℙ¹_S` be a closed subscheme of the
family of projective lines over `X`. The zero section and the infinity section of
`X ×_S ℙ¹_S ⟶ X` have closed images `D₀` and `D_∞`, and cutting `W` with them gives two closed
subschemes `W₀ = W ∩ D₀` and `W_∞ = W ∩ D_∞` of `W`.

Stacks Tag 02S4 says that when `W` is integral and is contained in neither image, `W₀` and
`W_∞` are effective Cartier divisors on `W`, that the cycles they determine on `X` are
rationally equivalent, and that locally finite sums of such differences are exactly the cycles
rationally equivalent to zero. This file contains the two divisors themselves and the
elementary properties of their supports: in particular, that such a divisor is the whole of `W`
precisely when `W` is swallowed by the image of the section, which is the degenerate case the
tag excludes.

## Main definitions

* `Stacks.Chow.familyBase`: the structure morphism `W ⟶ S` of a closed subscheme of
  `X ×_S ℙ¹_S` over the base.
* `Stacks.Chow.zeroDivisor` and `Stacks.Chow.infinityDivisor`: the closed subschemes of `W` cut
  out by the closures of the images of the zero and the infinity section.

## Main results

* `Stacks.Chow.coe_support_zeroDivisor` and `Stacks.Chow.coe_support_infinityDivisor`: the
  support of either divisor is the part of `W` lying in the image of the corresponding section.
* `Stacks.Chow.zeroDivisor_eq_bot_iff` and `Stacks.Chow.infinityDivisor_eq_bot_iff`: for
  reduced `W`, the divisor is the whole of `W` exactly when `W` is contained in the image of
  the section.
* `Stacks.Chow.zeroDivisor_ne_bot` and `Stacks.Chow.infinityDivisor_ne_bot`: contrapositively,
  the nondegeneracy hypothesis of Tag 02S4 says precisely that the divisor is a *proper*
  closed subscheme of `W`. This is the first step of part (1) of the tag.

## Implementation notes

The image of a section is cut out with its reduced structure, by
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`, and restricted to `W` by
`AlgebraicGeometry.Scheme.IdealSheafData.comap`. When `W` is reduced — in particular when it is
integral, as in Tag 02S4 — this agrees with cutting by the coordinate of the chart, because the
elements of the vanishing ideal that are not multiples of the coordinate have nilpotent
constant term and so die in `W`.

The definitions take the closure of the range of a section, as the construction of a reduced
closed subscheme needs a closed set. That closure is the range itself, by
`Stacks.Chow.isClosed_range_zeroSection`, so the statements below are phrased with the range,
which is the form Tag 02S4 uses.

The conclusion of part (1), that these divisors are effective Cartier, is proved in
`StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.LocallyPrincipal`, as
`Stacks.Chow.zeroDivisor_isEffectiveCartierDivisor` and
`Stacks.Chow.infinityDivisor_isEffectiveCartierDivisor`, via the affine-local description of
the ideal of a section together with Tag 01WS, both of which are proved in the library.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The structure morphism over the base `S` of a closed subscheme of the family
`X ×_S ℙ¹_S`. -/
public abbrev familyBase {X S : Scheme.{u}} (f : X ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) : W.subscheme ⟶ S :=
  W.subschemeι ≫ pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f

/-- The zero divisor of a closed subscheme `W` of `X ×_S ℙ¹_S`: the closed subscheme of `W` cut
out by the closure of the image of the zero section. -/
public def zeroDivisor {X S : Scheme.{u}} (f : X ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) :
    W.subscheme.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (Set.range (zeroSection f)), isClosed_closure⟩).comap W.subschemeι

/-- The infinity divisor of a closed subscheme `W` of `X ×_S ℙ¹_S`: the closed subscheme of `W`
cut out by the closure of the image of the infinity section. -/
public def infinityDivisor {X S : Scheme.{u}} (f : X ⟶ S)
    (W : (projectiveLineProduct f).IdealSheafData) :
    W.subscheme.IdealSheafData :=
  (Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (Set.range (infinitySection f)), isClosed_closure⟩).comap W.subschemeι

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (W : (projectiveLineProduct f).IdealSheafData)

/-- The zero divisor is supported on the part of `W` lying in the image of the zero
section. -/
@[simp]
theorem coe_support_zeroDivisor :
    ((zeroDivisor f W).support : Set W.subscheme) =
      W.subschemeι ⁻¹' Set.range (zeroSection f) := by
  simp [zeroDivisor, (isClosed_range_zeroSection f).closure_eq]

/-- The infinity divisor is supported on the part of `W` lying in the image of the infinity
section. -/
@[simp]
theorem coe_support_infinityDivisor :
    ((infinityDivisor f W).support : Set W.subscheme) =
      W.subschemeι ⁻¹' Set.range (infinitySection f) := by
  simp [infinityDivisor, (isClosed_range_infinitySection f).closure_eq]

/-- For reduced `W`, the zero divisor is the whole of `W` exactly when `W` is contained in the
image of the zero section. -/
theorem zeroDivisor_eq_bot_iff [IsReduced W.subscheme] :
    zeroDivisor f W = ⊥ ↔
      Set.range W.subschemeι ⊆ Set.range (zeroSection f) := by
  simp [← Scheme.IdealSheafData.support_eq_top_iff, ← Closeds.coe_eq_univ]

/-- For reduced `W`, the infinity divisor is the whole of `W` exactly when `W` is contained in
the image of the infinity section. -/
theorem infinityDivisor_eq_bot_iff [IsReduced W.subscheme] :
    infinityDivisor f W = ⊥ ↔
      Set.range W.subschemeι ⊆ Set.range (infinitySection f) := by
  simp [← Scheme.IdealSheafData.support_eq_top_iff, ← Closeds.coe_eq_univ]

/-- **First step of Stacks Tag 02S4 (1).** Under the nondegeneracy hypothesis of the tag, the
zero divisor is a proper closed subscheme of `W`. -/
theorem zeroDivisor_ne_bot [IsReduced W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f)) :
    zeroDivisor f W ≠ ⊥ :=
  fun hb => h ((zeroDivisor_eq_bot_iff f W).mp hb)

/-- **First step of Stacks Tag 02S4 (1).** Under the nondegeneracy hypothesis of the tag, the
infinity divisor is a proper closed subscheme of `W`. -/
theorem infinityDivisor_ne_bot [IsReduced W.subscheme]
    (h : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    infinityDivisor f W ≠ ⊥ :=
  fun hb => h ((infinityDivisor_eq_bot_iff f W).mp hb)

end Stacks.Chow

end
