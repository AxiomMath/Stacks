module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen
public import StacksFrontier.RingTheory.DiscreteValuationRing.TFAE
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The local ring at a closed point of a curve

Let `k` be a field and let `X` be a curve over `k`. At a closed point `x` of `X` the local ring
`𝒪_{X,x}` is a Noetherian local domain of Krull dimension one: it is a domain because a curve is
integral, Noetherian because a curve is of finite type over a field, and one-dimensional because
the dimension of an irreducible scheme of finite type over a field is its dimension at any point
and that dimension is computed by the local ring at a closed point.

For such a ring the characterizations of a discrete valuation ring collapse to a three-term
equivalence, which is items (1), (2) and (3) of [Stacks, Tag 0B8Y]: `𝒪_{X,x}` is regular iff it is
normal iff it is a discrete valuation ring.

## Main results

* `isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one`: for a Noetherian local domain of Krull
  dimension one, regular, normal and discrete valuation ring are equivalent.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isCurve`: the local ring of a curve at a closed
  point has Krull dimension one.
* `AlgebraicGeometry.coheight_eq_one_of_isCurve`: equivalently, a closed point of a curve has
  coheight one, which is the hypothesis under which the existing
  `AlgebraicGeometry.isDiscreteValuationRing_stalk` applies.
* `AlgebraicGeometry.isDiscreteValuationRing_stalk_tfae_of_isCurve`: items (1), (2) and (3) of
  [Stacks, Tag 0B8Y].

## Implementation notes

**Only three of the five items of Tag 0B8Y are proved here**, so the attribute is clause
qualified. Items (4) and (5) — that the ideal sheaf of `x` is invertible, equivalently that `x` is
an effective Cartier divisor on `X` — need the passage from a stalkwise principal ideal to a
locally principal one, [Stacks, Tag 0AG8]. Tag 0AG8 is
`Stacks.Divisors.isLocallyPrincipal_of_forall_stalk` and
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_stalk` of
`StacksFrontier/AlgebraicGeometry/Divisors/StalkLocallyPrincipal.lean`, and items (4) and (5)
are added to the equivalence below in
`StacksFrontier/AlgebraicGeometry/CurveLocalRing/EffectiveCartier.lean`, as
`AlgebraicGeometry.isEffectiveCartierDivisor_closedPoint_tfae_of_isCurve`. The point is that the
affine-local criterion
`Stacks.Divisors.isEffectiveCartierDivisor_of_forall_exists_affineOpen` asks for a regular
generator of the ideal on an affine open around each point rather than in each stalk; Tag 0AG8 is
exactly that passage, by a Noetherian finite-generation argument. Item (6), smoothness at `x`
under the source's hypothesis that `k` be perfect or that `κ(x)/k` be separable, is added in
`StacksFrontier/AlgebraicGeometry/CurveLocalRing/Smooth.lean`, as
`AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_perfectField` and
`AlgebraicGeometry.smoothAt_closedPoint_tfae_of_isCurve_of_isSeparable`.

**"Normal" is `IsNormalRing`**, the repository's spelling of [Stacks, Tag 00GV], rather than
`IsIntegrallyClosed`. The two agree for the local ring here, through
`IsNormalRing.of_isLocalRing` and `IsNormalRing.of_isIntegrallyClosed`; `IsNormalRing` is chosen
because it is the word the source uses and does not presuppose a domain.

**Relation to `AlgebraicGeometry.isDiscreteValuationRing_stalk`.** That result
(`StacksFrontier.AlgebraicGeometry.NormalExtension.Basic`) proves the implication (2) ⟹ (3) for any
locally Noetherian integral scheme at a point of coheight one, but takes normality as a
hypothesis on the *ring of sections over every affine open*. The equivalence below instead has
normality as a hypothesis on the *single stalk*, which is what the items of Tag 0B8Y assert, and
it supplies the reverse
implications. `coheight_eq_one_of_isCurve` is what makes that result applicable to a closed
point of a curve, so the two are complementary rather than duplicates.

**Noetherianness of the stalk is derived inside the proof, not assumed.**
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` is a theorem rather than an instance,
so it is introduced with a `let`; the statement itself needs no Noetherian hypothesis because
`IsRegularLocalRing` extends `IsNoetherianRing` rather than requiring it as an instance argument.

## References

* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 00PD](https://stacks.math.columbia.edu/tag/00PD)
-/

@[expose] public section

open CategoryTheory Order

universe u

/-- **A Noetherian local domain of Krull dimension one is regular iff normal iff a discrete
valuation ring.** This is the part of [Stacks, Tag 00PD] used by [Stacks, Tag 0B8Y]: items (3),
(5) and (1) of `isDiscreteValuationRing_tfae`, with the dimension hypothesis factored out. -/
@[ega "IV 14.5.7",
  ega "IV 21.9.8",
  ega "IV 6.7.5" "Local step",
  ega "IV 7.9.1" "Dimension-one case",
  sga "3 X 8.9" "partial",
  sga "7 IX 3.2.1" "Commutative-algebra core"]
public theorem isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] [IsDomain A] (hd : ringKrullDim A = 1) :
    List.TFAE [IsRegularLocalRing A, IsNormalRing A, IsDiscreteValuationRing A] := by
  have H := isDiscreteValuationRing_tfae A
  have h31 := H.out 3 1
  have h15 := H.out 1 5
  have h53 := H.out 5 3
  tfae_have 1 → 3 := fun h => (h31.mp ⟨h, hd⟩).2
  tfae_have 3 → 2 := fun h => by
    have : IsIntegrallyClosed A := (h15.mp ⟨‹IsDomain A›, h⟩).2.2.2.1
    exact IsNormalRing.of_isIntegrallyClosed A
  tfae_have 2 → 1 := fun h =>
    (h53.mp ⟨‹IsNoetherianRing A›, ‹IsLocalRing A›, ‹IsDomain A›, h.of_isLocalRing.2, hd⟩).1
  tfae_finish

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The local ring of a curve at a closed point is one-dimensional.** A curve is irreducible, so
its dimension is its dimension at `x`, which at a closed point is the Krull dimension of the local
ring; and the dimension of a curve is one. -/
public theorem ringKrullDim_stalk_eq_one_of_isCurve [IsCurve k f] {x : X}
    (hx : IsClosed ({x} : Set X)) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f x hx,
    ← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X f x,
    IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)]

/-- **A closed point of a curve has coheight one.** This is
`ringKrullDim_stalk_eq_one_of_isCurve` read through
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, and is the form in which
`AlgebraicGeometry.isDiscreteValuationRing_stalk` takes its codimension hypothesis. -/
public theorem coheight_eq_one_of_isCurve [IsCurve k f] {x : X}
    (hx : IsClosed ({x} : Set X)) : coheight x = 1 := by
  have h := ringKrullDim_stalk_eq_one_of_isCurve k f hx
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- **Items (1), (2) and (3) of [Stacks, Tag 0B8Y].** At a closed point `x` of a curve over a
field the local ring `𝒪_{X,x}` is regular if and only if it is normal if and only if it is a
discrete valuation ring. -/
@[stacks 0B8Y "(1), (2) and (3)",
  ega "II 7.4.5",
  ega "II 7.1.6" "curve stalk case",
  ega "IV 6.7.5" "partial", sga "7 IX 3.2.1" "special case"]
public theorem isDiscreteValuationRing_stalk_tfae_of_isCurve [IsCurve k f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    List.TFAE [IsRegularLocalRing (X.presheaf.stalk x), IsNormalRing (X.presheaf.stalk x),
      IsDiscreteValuationRing (X.presheaf.stalk x)] := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isDiscreteValuationRing_tfae_of_ringKrullDim_eq_one _
    (ringKrullDim_stalk_eq_one_of_isCurve k f hx)

end AlgebraicGeometry

end
