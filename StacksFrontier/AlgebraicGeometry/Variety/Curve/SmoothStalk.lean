module

public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.RegularStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local rings of a smooth curve are discrete valuation rings

Let `k` be a field and let `X` be a curve over `k` which is moreover smooth over `k`. At every
point of `X` other than the generic point the local ring `𝒪_{X, x}` is a discrete valuation ring.

The curve hypothesis alone gives only that `𝒪_{X, x}` is a one-dimensional Noetherian local
domain, for which being a discrete valuation ring is equivalent to being regular. Smoothness is
what supplies that regularity.

## Main results

* `AlgebraicGeometry.IsCurve.isDiscreteValuationRing_stalk`: at a point of a smooth curve other
  than the generic point, the local ring is a discrete valuation ring.
* `AlgebraicGeometry.IsCurve.isDiscreteValuationRing_stalk_of_isClosed`: the same at a closed
  point.

## Implementation notes

The hypothesis on the point is `x ≠ genericPoint X` rather than closedness of `{x}`, because that
is both the weaker hypothesis on a curve and the one under which
`AlgebraicGeometry.IsCurve.ordHom` — the local content of the second map of the divisor sequence
of [Stacks, Tag 03RM] — is defined. The closed-point form is recorded separately for readers of
[Stacks, Tag 0B8Y], whose items are stated at a closed point; it is not derived from the
non-generic form, since closedness of a point of a curve is not literally the statement that it
is not the generic point, but from the three-term equivalence
`AlgebraicGeometry.isDiscreteValuationRing_stalk_tfae_of_isCurve` at a closed point.

Noetherianness of the stalk is not a hypothesis: it is derived inside the proofs from
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`, which a curve provides.

No `@[stacks]` attribute is attached. These are the implication (6) ⟹ (3) of [Stacks, Tag 0B8Y]
in the direction that needs no hypothesis on `k`; the complete statement of that tag is a
five-term equivalence whose items (4) and (5), invertibility of the ideal sheaf of `x` and `x`
being an effective Cartier divisor, are not proved here.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace IsCurve

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]

/-- **The local ring of a smooth curve at a non-generic point is a discrete valuation ring.** Let
`k` be a field, let `X` be a curve over `k` which is smooth over `k`, and let `x` be a point of
`X` other than the generic point. Then `𝒪_{X, x}` is a discrete valuation ring.

Being a curve makes `𝒪_{X, x}` a Noetherian local domain of Krull dimension one, and smoothness
makes it regular; a one-dimensional regular Noetherian local domain is a discrete valuation
ring. -/
@[ega "II 7.1.6" "special case", ega "IV 21.9.8" "special case", sga "7 IX 3.2.1" "special case"]
public theorem isDiscreteValuationRing_stalk {x : X} (hx : x ≠ genericPoint X) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hdim : ringKrullDim (X.presheaf.stalk x) = 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast IsCurve.coheight_eq_one f hx
  exact ((isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _ hdim).out 1 3).mp
    (isRegularLocalRing_stalk_of_smooth_over_field f x)

/-- **The local ring of a smooth curve at a closed point is a discrete valuation ring.** This is
the implication (6) ⟹ (3) of [Stacks, Tag 0B8Y], read off the equivalence of its items (1) and
(3) together with regularity of the local rings of a scheme smooth over a field. -/
@[sga "7 IX 3.2.1" "special case"]
public theorem isDiscreteValuationRing_stalk_of_isClosed {x : X}
    (hx : IsClosed ({x} : Set X)) : IsDiscreteValuationRing (X.presheaf.stalk x) :=
  ((isDiscreteValuationRing_stalk_tfae_of_isCurve k f hx).out 1 3).mp
    (isRegularLocalRing_stalk_of_smooth_over_field f x)

end IsCurve

end AlgebraicGeometry

end
