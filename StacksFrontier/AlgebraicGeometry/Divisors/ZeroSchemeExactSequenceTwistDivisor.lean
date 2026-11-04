module

public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeCanonicalSection
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeExactSequenceTwist

/-!
# The twisted exact sequence at an effective Cartier divisor

Let `X` be a scheme, `D ⊆ X` an effective Cartier divisor with inclusion `i`, and `M` an
invertible `𝒪_X`-module. Tensoring the sequence of [Stacks, Tag 0C6K] with `M` gives the short
exact sequence

`0 ⟶ M ⟶ M ⊗ 𝒪_X(D) ⟶ i_* i^* (M ⊗ 𝒪_X(D)) ⟶ 0`,

whose first map is multiplication by the canonical section `1_D` in the second factor and whose
second map is the unit of the pullback–pushforward adjunction. This is
`AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection` read at the canonical section
of `𝒪_X(D)`, whose zero scheme is `D` itself
(`Stacks.Divisors.zeroScheme_canonicalSections`), so that the closed immersion appearing in the
sequence is the inclusion of `D` rather than the inclusion of a zero scheme.

It is this sequence, at `M` a twist of the structure sheaf of a blowup, that computes the
cohomology of the twists along the filtration by the powers of the exceptional ideal sheaf.

## Main definitions

* `AlgebraicGeometry.IsShortExactTwistSequence`: the assertion of the twisted sequence with the
  closed subscheme as a separate argument, so that it can be rewritten. This is to
  `AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection` what
  `AlgebraicGeometry.IsShortExactUnitSequence` is to
  `AlgebraicGeometry.shortExact_zeroScheme_of_isRegularSection`.

## Main results

* `AlgebraicGeometry.isShortExactTwistSequence_zeroScheme`: the twisted sequence at the zero
  scheme of a regular section, in the rewritable shape.
* `Stacks.Divisors.isShortExactTwistSequence_canonicalSections`: **the twisted sequence at an
  effective Cartier divisor.**

## Implementation notes

The closed immersion `i` occurs inside the *types* of the two maps of the sequence, so rewriting
`zeroScheme X L (s.eval (op ⊤)) = D` in the conclusion of the twisted-sequence theorem needs the
subscheme to be the head of an application; that is what naming the assertion with the subscheme
as a parameter buys, exactly as for the untwisted sequence in
`StacksFrontier/AlgebraicGeometry/Divisors/ZeroSchemeCanonicalSection.lean`.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] schemeModulesMonoidal schemeModulesSymmetric

variable {X : Scheme.{u}}

/-- **The assertion of the twisted form of [Stacks, Tag 0C6K] with the closed subscheme as a
parameter.** For a closed subscheme `I ⊆ X` with inclusion `i` and `𝒪_X`-modules `L`, `M` with a
global section `s` of `L`, the sequence

`0 ⟶ M ⟶ M ⊗ L ⟶ i_* i^* (M ⊗ L) ⟶ 0`

is short exact, the first map being multiplication by `s` in the second factor and the second the
unit of the pullback–pushforward adjunction.

This is verbatim the conclusion of
`AlgebraicGeometry.shortExact_zeroScheme_twist_of_isRegularSection`, except that the subscheme is
an argument instead of being `zeroScheme X L (s.eval (op ⊤))`. -/
def IsShortExactTwistSequence (I : X.IdealSheafData) (L M : X.Modules) (s : L.sections) : Prop :=
  let i := I.subschemeι
  let f : M ⟶ M ⊗ L := (ρ_ M).inv ≫ M ◁ L.unitHomEquiv.symm s
  let g : (M ⊗ L : X.Modules) ⟶ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj (M ⊗ L)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app (M ⊗ L)
  ∃ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact

/-- **The twisted form of [Stacks, Tag 0C6K], second assertion, as
`AlgebraicGeometry.IsShortExactTwistSequence`.** -/
theorem isShortExactTwistSequence_zeroScheme (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (hs : IsRegularSection X.sheaf.obj X.ringCatSheaf.property s) (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    IsShortExactTwistSequence (zeroScheme X L (s.eval (op ⊤))) L M s :=
  shortExact_zeroScheme_twist_of_isRegularSection X L s hs M

end AlgebraicGeometry

namespace Stacks.Divisors

open _root_.AlgebraicGeometry

attribute [local instance] _root_.AlgebraicGeometry.schemeModulesMonoidal
  _root_.AlgebraicGeometry.schemeModulesSymmetric

variable {X : Scheme.{u}} (D : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]

/-- **The twisted sequence of [Stacks, Tag 0C6K] at an effective Cartier divisor.** For an
effective Cartier divisor `D ⊆ X` with inclusion `i` and an invertible `𝒪_X`-module `M`, the
sequence

`0 ⟶ M ⟶ M ⊗ 𝒪_X(D) ⟶ i_* i^* (M ⊗ 𝒪_X(D)) ⟶ 0`

is short exact, the first map being multiplication by the canonical section `1_D` in the second
factor.

The closed immersion is the inclusion of `D` itself, not of the zero scheme of the canonical
section: the two agree by `Stacks.Divisors.zeroScheme_canonicalSections`. At `M = 𝒪_X` this is
`Stacks.Divisors.isShortExactUnitSequence_canonicalSections`, up to the unitor identifying
`𝒪_X ⊗ 𝒪_X(D)` with `𝒪_X(D)`. -/
theorem isShortExactTwistSequence_canonicalSections (M : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M] :
    IsShortExactTwistSequence D (modulesInvertibleSheaf D) M (canonicalSections D) := by
  have key := isShortExactTwistSequence_zeroScheme (modulesInvertibleSheaf D)
    (canonicalSections D) (isRegularSection_canonicalSections D) M
  rwa [zeroScheme_canonicalSections D] at key

end Stacks.Divisors

end
