module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Stable families of curves (Stacks 0E75)

A family of curves `f : X ⟶ S` is *stable* when it is prestable and every fibre `X_s` has
genus at least two and has neither a rational tail nor a rational bridge. Over a field this
says that the geometric fibre is connected, smooth away from finitely many nodes, of genus at
least two, and has no irreducible component isomorphic to the projective line meeting the rest
of the curve in one point or in two points; in particular a prestable family of genus zero or
one is never stable.

## Main definitions

* `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge` is the fibrewise condition:
  genus at least two, no rational tail and no rational bridge.
* `AlgebraicGeometry.IsStableCurveFamily`: **Stacks 0E75**, stability of a family of curves.

## Main results

There are no propositional results. The definition is an abbreviation, so its prestability and
fibre conditions are directly available to statements about stable families.

## Implementation notes

The shape follows `AlgebraicGeometry.IsSemistableCurveFamily` of Stacks 0E6Z, of which this is
the strengthening by one unit of genus and by the rational-bridge condition, so that the two
definitions test their fibres through the same device.

A point of the base is taken in the form in which the points of this development are defined
(Stacks 03BU): a field-valued point, that is, a field of the chosen big fppf site together
with a morphism from its spectrum to the base. Imposing the condition on every field-valued
point rather than on one representative per point of the base loses nothing: genus is
invariant under extension of the ground field, and a curve has a rational tail, respectively a
rational bridge, exactly when its base change to an algebraically closed field does.

The genus, the rational-tail and the rational-bridge conditions are notions about a *scheme*
over a field, whereas the fibre of a family of curves is a priori only an algebraic space, so
the fibre is presented by a scheme `V` of the site whose structure morphism `v` to the
spectrum of the field of the point exhibits `V` as a fibre product of the family along that
point. Requiring such a presentation to exist is not a restriction — the fibre of a family of
curves over a field is a proper algebraic space of dimension at most one, hence a scheme — and
it carries the representability of the fibre, which is not proved here; the existential form
loses nothing because two presentations of the same fibre are isomorphic over the ground
field, and all three fibre conditions are invariant under such an isomorphism.

The rational-bridge predicate takes properness of the presentation over the field of the point
as an instance, needed to produce the field structure on the global functions of a component.
Rather than assume it of the family — a hypothesis the source does not have — it is asserted
of the presentation inside the clause, so that the absence of rational bridges is stated
outright and not conditionally on properness. This adds nothing to the notion: properness of a
presentation follows from properness of the family by base change.

The source's characterization of stability by ampleness of the relative dualizing sheaf, and
the openness of the stable locus, are not proved here.

## References

* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A scheme over a field has genus at least two, no rational tail and no rational bridge: no
closed subscheme of it is a rational tail, and, the scheme being proper over the field, no
closed subscheme of it is a rational bridge. -/
abbrev HasGenusTwoNoRationalTailNoRationalBridge (k : Type u) [Field k] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k)) : Prop :=
  letI : V.Over (Spec (.of k)) := ⟨f⟩
  2 ≤ genus f ∧ (∀ C : V.IdealSheafData, ¬ IsRationalTail k V C) ∧
    ∃ hproper : IsProper (V ↘ Spec (.of k)),
      letI : IsProper (V ↘ Spec (.of k)) := hproper
      ∀ C : V.IdealSheafData, ¬ IsRationalBridge k V C

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0E75.** A family of curves is *stable* when it is prestable and, for every point
of the base, its fibre there has genus at least two and has neither a rational tail nor a
rational bridge.

The constituents. The family is an `AlgebraicGeometry.CurveFamily`: flat, proper, of finite
presentation and of relative dimension at most one, from an algebraic space to a scheme of the
site. Prestability is `AlgebraicGeometry.IsPrestableCurveFamily`. A point of the base is an
`AlgebraicGeometry.Space.FieldValuedPoint`, a field `p.carrier` together with a morphism from
its spectrum to the base, and the `CategoryTheory.IsPullback` clause exhibits the scheme `V` of
the site as the fibre of the family over that point. The conditions on the fibre are collected
in `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge`: its
`AlgebraicGeometry.genus` over `p.carrier` is at least two, no ideal sheaf of `V` satisfies
`AlgebraicGeometry.IsRationalTail`, and none satisfies
`AlgebraicGeometry.IsRationalBridge`. -/
@[stacks 0E75, sga "7 I 5.1" "special case"]
abbrev IsStableCurveFamily (X : CurveFamily B hZ) : Prop :=
  IsPrestableCurveFamily B hZ X ∧
    ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
        IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge p.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v)

end AlgebraicGeometry

end
