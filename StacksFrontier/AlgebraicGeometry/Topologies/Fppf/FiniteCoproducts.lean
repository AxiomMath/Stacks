module

public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct

/-!
# Finite coproducts in big fppf sites

The size cutoff of a big fppf site is closed under finite coproducts of schemes. Hence the
underlying category of a big fppf site and the big fppf category over `S` admit finite
coproducts, and the big fppf category over `S` is a finitary extensive category: its finite
coproducts are disjoint and van Kampen, hence universal.

## Main results

* `AlgebraicGeometry.schemeSizeBelow_isClosedUnderFiniteCoproducts`: the size cutoff of a big
  fppf site is closed under finite coproducts of schemes, in the form Mathlib uses to equip a
  full subcategory with finite coproducts.
* `AlgebraicGeometry.hasFiniteCoproducts_bigFppfSite` and
  `AlgebraicGeometry.hasFiniteCoproducts_bigFppfOver`: the underlying category of a big fppf
  site and the big fppf category over `S` admit finite coproducts, in particular an initial
  object.
* `AlgebraicGeometry.finitaryExtensive_bigFppfOver`: the big fppf category over `S` is finitary
  extensive.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 021R](https://stacks.math.columbia.edu/tag/021R)
* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry

/-- **The size cutoff of a big fppf site is closed under finite coproducts of schemes**, in
the form Mathlib uses to equip a full subcategory with finite coproducts. -/
public instance schemeSizeBelow_isClosedUnderFiniteCoproducts (B : BigFppfSite.{u}) :
    (schemeSizeBelow B.cutoff).IsClosedUnderFiniteCoproducts := by
  refine ObjectProperty.IsClosedUnderFiniteCoproducts.of_isClosedUnderColimitsOfShape ?_
  intro J _
  exact schemeSizeBelow_isClosedUnderColimitsOfShape_discrete B.aleph0_lt_cutoff
    B.aleph0_lt_cutoff_cof Cardinal.mk_le_aleph0

/-- The underlying category of a big fppf site admits finite coproducts, and in particular an
initial object: the empty scheme. -/
public instance hasFiniteCoproducts_bigFppfSite (B : BigFppfSite.{u}) :
    HasFiniteCoproducts B.Schemes :=
  inferInstance

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The big fppf category over `S` admits finite coproducts, and in particular an initial
object: the empty scheme over `S`. -/
public instance hasFiniteCoproducts_bigFppfOver :
    HasFiniteCoproducts (BigFppfOver B S hS) :=
  inferInstance

/-- **The big fppf category over `S` is finitary extensive.** Its finite coproducts are
disjoint and van Kampen, hence universal. -/
public instance finitaryExtensive_bigFppfOver :
    FinitaryExtensive (BigFppfOver B S hS) :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism (BigFppfOver.toScheme B S hS)

end AlgebraicGeometry

end
