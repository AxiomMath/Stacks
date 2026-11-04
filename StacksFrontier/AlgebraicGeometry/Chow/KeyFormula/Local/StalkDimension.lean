module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass.PrimeDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.ReciprocityCanonical
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol.KrullDimOne
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring at a point of codimension one or two

The local inputs of the key formula Stacks 0AYC are two statements about one local ring. At a
codimension-one point `ξ` of an integral scheme `X` the stalk `B_ξ = 𝒪_{X, ξ}` is a
one-dimensional Noetherian local ring, which is what the tame symbol of Stacks 0EAH asks for; at
a codimension-two point it is two-dimensional, which is what the Key Lemma Stacks 0EAX asks for.
Both are read off the topology by [Stacks, Tag 02IZ],
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`: the Krull dimension of the stalk at a point
is the coheight of that point in the specialization order.

This file performs that reading in the two forms the key formula consumes, and assembles the
resulting tame symbol and reciprocity law. The `IsNoetherianRing` and `IsLocalRing` instances on
the stalk are the ambient ones — the first from `IsLocallyNoetherian X`, which
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` supplies for a scheme locally of
finite type over the base, the second from the locally ringed space structure — so no hypothesis
beyond the coheight of the point appears below.

Nothing here is assumed to be a domain. The stalk of a reduced scheme at a codimension-one point
need not be one, and `Stacks.Chow.tameSymbolOfKrullDimOne` does not ask it to be;
`Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero` does carry `[IsIntegral X]`, because
Stacks 0EAX itself is stated for a local *domain* of dimension two, and on an integral scheme the
stalks are domains.

## Main definitions

* `Stacks.Chow.tameSymbolAtCoheightOne` — the tame symbol
  `∂_{𝒪_{X, ξ}} : R(X)^* × R(X)^* → κ(ξ)^*` of Stacks 0EAH at a codimension-one point of an
  integral, locally Noetherian scheme. This is the argument `Stacks.Chow.tameSymbolAt` expects.

## Main results

* `Stacks.Chow.ringKrullDim_stalk_eq_one_of_coheight_eq_one` and
  `Stacks.Chow.ringKrullDim_stalk_eq_two_of_coheight_eq_two` — the two dimension statements.
* `Stacks.Chow.ringKrullDim_stalk_genericPoint_eq_one` — the first of them at the generic point of
  a prime divisor, where the coheight is one by
  `Stacks.Divisors.PrimeDivisor.coheight_genericPoint`.
* `Stacks.Chow.finsum_fracTameSymbolOrderAt_stalk_eq_zero` — **Stacks 0EAX at a codimension-two
  point of an integral scheme**: the reciprocity sum over the height-one primes of `𝒪_{X, ξ}`
  vanishes. This is the local identity to which Stacks 0AYC reduces.

## References

* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
* [Stacks Project, Tag 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-! ### The dimension of the stalk -/

/-- **The local ring at a codimension-one point is one-dimensional.** By [Stacks, Tag 02IZ] the
Krull dimension of `𝒪_{X, x}` is the coheight of `x`.

This is the hypothesis `ringKrullDim A = 1` of `Stacks.Chow.tameSymbolOfKrullDimOne`, so with the
ambient `IsNoetherianRing` and `IsLocalRing` instances on the stalk it is the whole input of
Stacks 0EAH at `x`. -/
theorem ringKrullDim_stalk_eq_one_of_coheight_eq_one {x : X} (hx : coheight x = 1) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hx]
  rfl

/-- **The local ring at a codimension-two point is two-dimensional.** By [Stacks, Tag 02IZ] the
Krull dimension of `𝒪_{X, x}` is the coheight of `x`.

This is the hypothesis `ringKrullDim A = 2` of the Key Lemma Stacks 0EAX,
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`. The points of an integral scheme of
delta-dimension `n` at which the key formula Stacks 0AYC has content are exactly these. -/
@[ega "IV 21.6.2" "p = 2"]
theorem ringKrullDim_stalk_eq_two_of_coheight_eq_two {x : X} (hx : coheight x = 2) :
    ringKrullDim (X.presheaf.stalk x) = 2 := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hx]
  rfl

/-- **The local ring at the generic point of a prime divisor is one-dimensional.** A prime
divisor has codimension one, which is `Stacks.Divisors.PrimeDivisor.coheight_genericPoint`. -/
theorem ringKrullDim_stalk_genericPoint_eq_one (Z : Stacks.Divisors.PrimeDivisor X) :
    ringKrullDim (X.presheaf.stalk Z.genericPoint) = 1 :=
  ringKrullDim_stalk_eq_one_of_coheight_eq_one Z.coheight_genericPoint

/-- The local ring at a codimension-one point has Krull dimension at most one, in the
`Ring.KrullDimLE` form that the extension of a tame symbol to the fraction field consumes. -/
theorem krullDimLE_one_stalk_of_coheight_eq_one {x : X} (hx : coheight x = 1) :
    Ring.KrullDimLE 1 (X.presheaf.stalk x) :=
  krullDimLE_one_of_ringKrullDim_eq_one (ringKrullDim_stalk_eq_one_of_coheight_eq_one hx)

/-! ### The tame symbol at a codimension-one point -/

section TameSymbol

variable [IsIntegral X] [IsLocallyNoetherian X]

/-- **The tame symbol of Stacks 0EAH at a codimension-one point.** For `ξ` of codimension one on
an integral, locally Noetherian scheme the stalk `B_ξ = 𝒪_{X, ξ}` is a one-dimensional
Noetherian local ring with fraction field the function field `R(X)`, so Stacks 0EAH gives the
tame symbol

`∂_{B_ξ} : R(X)^* × R(X)^* → κ(𝔪_ξ)^*`.

This is `Stacks.Chow.tameSymbolOfKrullDimOne` with its dimension hypothesis discharged by
`Stacks.Chow.ringKrullDim_stalk_eq_one_of_coheight_eq_one`; it is the datum that
`Stacks.Chow.tameSymbolAt` turns into the map `R(X)^* × R(X)^* → R(Z_ξ)^*` used by the key
formula. -/
def tameSymbolAtCoheightOne {x : X} (hx : coheight x = 1) :
    TameSymbol (X.presheaf.stalk x) X.functionField :=
  tameSymbolOfKrullDimOne (ringKrullDim_stalk_eq_one_of_coheight_eq_one hx) X.functionField

/-- The tame symbol at a codimension-one point of the generic point of a prime divisor. -/
abbrev tameSymbolAtGenericPoint (Z : Stacks.Divisors.PrimeDivisor X) :
    TameSymbol (X.presheaf.stalk Z.genericPoint) X.functionField :=
  tameSymbolAtCoheightOne Z.coheight_genericPoint

/-- On pairs of nonzerodivisors of `𝒪_{X, ξ}` the tame symbol at a codimension-one point is the
periodic-determinant symbol of Stacks 02PZ. -/
theorem tameSymbolAtCoheightOne_regularFractionUnit {x : X} (hx : coheight x = 1)
    (a b : nonZeroDivisors (X.presheaf.stalk x)) :
    tameSymbolAtCoheightOne hx (regularFractionUnit a) (regularFractionUnit b) =
      regularModuleSymbol (ringKrullDim_stalk_eq_one_of_coheight_eq_one hx) a b :=
  tameSymbolOfKrullDimOne_regularFractionUnit _ X.functionField a b

end TameSymbol

/-! ### The Key Lemma at a codimension-two point -/

/-- **Stacks 0EAX at a codimension-two point of an integral scheme.** Let `ξ` be a point of
coheight two on an integral, locally Noetherian scheme and let `A = 𝒪_{X, ξ}`, a two-dimensional
Noetherian local domain. For two units `f, g` of the fraction field of `A` the orders of
vanishing of the tame symbols `∂_{A_𝔮}(f, g)` along `A / 𝔮`, summed over the height-one primes
`𝔮` of `A`, give zero.

This is `Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero` with its dimension
hypothesis discharged by `Stacks.Chow.ringKrullDim_stalk_eq_two_of_coheight_eq_two`. It is the
local identity that the reduction
`Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one` leaves as the remaining
input of the key formula Stacks 0AYC: the height-one primes of `𝒪_{X, ξ}` are the
codimension-one points of `X` specializing to `ξ`, that is, the members `Z_i` of the family
through `ξ`. -/
theorem finsum_fracTameSymbolOrderAt_stalk_eq_zero [IsIntegral X] [IsLocallyNoetherian X]
    {x : X} (hx : coheight x = 2)
    (f g : (FractionRing (X.presheaf.stalk x))ˣ) :
    ∑ᶠ p : HeightOnePrime (X.presheaf.stalk x),
        fracTameSymbolOrderAt (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx) p
          (canonicalHeightOneSymbol p) f g = 0 :=
  finsum_fracTameSymbolOrderAt_canonical_eq_zero
    (ringKrullDim_stalk_eq_two_of_coheight_eq_two hx) f g

end Stacks.Chow

end
