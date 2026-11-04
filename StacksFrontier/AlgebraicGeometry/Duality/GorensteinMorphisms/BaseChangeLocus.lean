module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.BaseChange

/-!
# The Gorenstein locus of a flat morphism locally of finite type

Let `f : X ⟶ Y` be flat and locally of finite type. [Stacks, Tag 0E0Q] asserts that formation of
the set of points at which `f` is Gorenstein commutes with arbitrary base change: for any
`g : Y' ⟶ Y`, the Gorenstein locus of the base change `X ×_Y Y' ⟶ Y'` is the inverse image of
the Gorenstein locus of `f` under the projection `X ×_Y Y' ⟶ X`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.setOf_isGorensteinAt_pullback_eq_preimage_of_locallyOfFiniteType`
  is that statement, with no hypothesis on `f` beyond flatness and being locally of finite type,
  and none at all on `g`.

## Implementation notes

Gorensteinness at a point is a predicate on a morphism *together with* a proof that its fibres
are locally Noetherian, because the local ring of the fibre has to be Noetherian for the
Gorenstein condition on it to be the intended one. The set equality
`AlgebraicGeometry.Scheme.Hom.setOf_isGorensteinAt_pullback_eq_preimage` therefore takes two such
proofs — for `f` and for its base change — as arguments. Under the hypotheses of the tag both are
theorems rather than hypotheses, and that is what is recorded here: a fibre of a morphism locally
of finite type is locally of finite type over the residue field of its base point, by the
instance `AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`, hence
locally Noetherian by `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`; and being
locally of finite type is stable under base change, so the base change of `f` has the same
property. The two proofs appear in the statement because the predicate needs them as data, but
they are supplied, not assumed, so the statement is exactly the tag's.

## References

* [Stacks Project, Tag 0E0Q](https://stacks.math.columbia.edu/tag/0E0Q)
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `f : X ⟶ Y` be flat and locally of finite type and let `g : Y' ⟶ Y` be an arbitrary
morphism of schemes. Then the set of points of `X ×_Y Y'` at which the base change of `f` along
`g` is Gorenstein is the inverse image, under the projection to `X`, of the set of points of `X`
at which `f` is Gorenstein: formation of the Gorenstein locus of `f` commutes with arbitrary base
change. The locally Noetherian fibres that the Gorenstein-at-a-point predicate needs as data are
theorems here, so nothing is assumed beyond flatness of `f` and its being locally of finite
type. -/
@[stacks 0E0Q]
public theorem setOf_isGorensteinAt_pullback_eq_preimage_of_locallyOfFiniteType
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) [Flat f] [LocallyOfFiniteType f] :
    {x' : (pullback f g : Scheme.{u}) |
        IsGorensteinAt (pullback.snd f g)
          (fun y' => LocallyOfFiniteType.isLocallyNoetherian
            ((pullback.snd f g).fiberToSpecResidueField y')) x'} =
      (pullback.fst f g).base ⁻¹'
        {x : X |
          IsGorensteinAt f
            (fun y => LocallyOfFiniteType.isLocallyNoetherian
              (f.fiberToSpecResidueField y)) x} :=
  setOf_isGorensteinAt_pullback_eq_preimage f g _ _

end AlgebraicGeometry.Scheme.Hom
