module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Quot.PrestableCurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Semistable families of curves (Stacks 0E6Z)

A family of curves `f : X ⟶ S` is *semistable* when it is prestable and every fibre `X_s` has
genus at least one and no rational tail. Over a field this says that the geometric fibre is
connected, smooth away from finitely many nodes, of genus at least one, and has no irreducible
component isomorphic to the projective line meeting the rest of the curve in a single point;
in particular a prestable family of genus zero is never semistable.

## Main definitions

* `AlgebraicGeometry.HasPositiveGenusNoRationalTail` is the fibrewise condition: genus at
  least one and no rational tail.
* `AlgebraicGeometry.IsSemistableCurveFamily`: **Stacks 0E6Z**, semistability of a family of
  curves.

## Main results

There are no propositional results. The definition is an abbreviation, so its prestability and
fibre conditions are directly available to statements about semistable families.

## Implementation notes

A point of the base is taken in the form in which the points of this development are defined
(Stacks 03BU): a field-valued point, that is, a field of the chosen big fppf site together
with a morphism from its spectrum to the base. Imposing the condition on every field-valued
point rather than on one representative per point of the base loses nothing: genus is
invariant under extension of the ground field, and a curve has a rational tail exactly when
its base change to an algebraically closed field does, which is the source's Algebraic Curves,
Lemma 0E3L.

The genus and the rational-tail condition are notions about a *scheme* over a field, whereas
the fibre of a family of curves is a priori only an algebraic space, so the fibre is presented
by a scheme `V` of the site whose structure morphism `v` to the spectrum of the field of the
point exhibits `V` as a fibre product of the family along that point. Requiring such a
presentation to exist is not a restriction — the fibre of a family of curves over a field is a
proper algebraic space of dimension at most one, hence a scheme — and it carries the
representability of the fibre, which is not proved here; the existential form loses nothing
because two presentations of the same fibre are isomorphic over the ground field, and both
fibre conditions are invariant under such an isomorphism. This is the same device as
`AlgebraicGeometry.IsFiniteNonSmoothLocus`.

## References

* [Stacks Project, Tag 0E6Z](https://stacks.math.columbia.edu/tag/0E6Z)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0BY7](https://stacks.math.columbia.edu/tag/0BY7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A scheme over a field has genus at least one and no rational tail: no closed subscheme of
it is a rational tail. -/
abbrev HasPositiveGenusNoRationalTail (k : Type u) [Field k] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k)) : Prop :=
  letI : V.Over (Spec (.of k)) := ⟨f⟩
  1 ≤ genus f ∧ ∀ C : V.IdealSheafData, ¬ IsRationalTail k V C

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Stacks 0E6Z.** A family of curves is *semistable* when it is prestable and, for every
point of the base, its fibre there has genus at least one and no rational tail. -/
@[stacks 0E6Z]
abbrev IsSemistableCurveFamily (X : CurveFamily B hZ) : Prop :=
  IsPrestableCurveFamily B hZ X ∧
    ∀ p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj,
      ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
        (q : yoneda.obj V ⟶ X.total.obj),
        IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) ∧
          HasPositiveGenusNoRationalTail p.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v)

end AlgebraicGeometry

end
