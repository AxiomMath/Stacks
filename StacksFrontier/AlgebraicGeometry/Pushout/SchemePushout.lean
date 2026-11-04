module

public import StacksFrontier.AlgebraicGeometry.Pushout.AffineGluing

/-!
# Pushouts of affine schemes along a closed immersion

A cartesian square of commutative rings becomes a cocartesian square of schemes once one of the
two maps to the base ring is surjective.  Concretely, if `p : A' ⟶ A` is surjective, `q : B ⟶ A`
is arbitrary and `B'` is the fibre product `B ×_A A'`, then

```
Spec A ---> Spec A'
  |            |
  v            v
Spec B ---> Spec B'
```

is a pushout square *in the category of all schemes*, not merely in affine schemes.  This is
the content of [Stacks Project, Tag 0ET0], and it is the affine local model underlying the two
pushout constructions of Tags 07RT and 0E25.

## Main results

* `Stacks.Pushout.isPushout_specLocallyRingedSpaceMap_of_isPullback` is Tag 0ET0 for locally
  ringed spaces.
* `Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective` is Tag 0ET0.

## Implementation notes

The fibre product of rings is not constructed here: the hypothesis is an arbitrary cartesian
square in `CommRingCat`, so the conclusion applies to any model of `B ×_A A'`, in particular to
`RingHom.pullback` as used in `StacksFrontier.AlgebraicGeometry.Pushout.Affine`.

That the square is cocartesian *in affine schemes* is merely the cartesian square of rings read
in the opposite category, and needs no surjectivity; the work is in showing that no non-affine
scheme can see a difference.  That is done in
`StacksFrontier.AlgebraicGeometry.Pushout.AffineGluing`, which establishes the pushout property for
sheafed spaces.  Here it is promoted twice: `LocallyRingedSpace.forgetToSheafedSpace` reflects
isomorphisms, hence colimits of this shape, and `Scheme.forgetToLocallyRingedSpace` is fully
faithful and reflects the pushout back to schemes.  `IsPushout.flip` only reconciles the
orientation of the square with the one in the source.

The intermediate locally ringed space statement is kept as a separate result rather than being
a step inside the proof of the scheme statement:
`AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace`
does *not* preserve colimits, so a pushout square of schemes says nothing about the underlying
locally ringed spaces, and the gluing construction of Tag 0E25 needs the pushout property one
layer down.

## References

* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

/-- **Stacks Project, Tag 0ET0, for locally ringed spaces.**  A fibre product of rings over a
surjective map is sent by `Spec` to a pushout square of locally ringed spaces.

This is the form in which the statement is used by the gluing construction of
[Stacks Project, Tag 0E25]: a pushout square of schemes carries no information about the
underlying locally ringed spaces, because `AlgebraicGeometry.Scheme.forgetToLocallyRingedSpace`
does not preserve colimits. -/
theorem isPushout_specLocallyRingedSpaceMap_of_isPullback
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p)
    (hp : Function.Surjective p) :
    IsPushout (Spec.locallyRingedSpaceMap p) (Spec.locallyRingedSpaceMap q)
      (Spec.locallyRingedSpaceMap q') (Spec.locallyRingedSpaceMap p') := by
  have : ReflectsColimitsOfShape WalkingSpan LocallyRingedSpace.forgetToSheafedSpace.{u} :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine IsPushout.flip ?_
  exact IsPushout.of_map_of_faithful LocallyRingedSpace.forgetToSheafedSpace
    (isPushout_specSheafedSpaceMap_of_isPullback p q p' q' h hp)

/-- **Stacks Project, Tag 0ET0.**  A fibre product of rings over a surjective map is sent by
`Spec` to a pushout of schemes: if `p : A' ⟶ A` is surjective and the square with sides `p'`,
`q'`, `q`, `p` is cartesian in `CommRingCat`, then its image under `Spec` is a pushout square
of schemes. -/
@[stacks 0ET0]
theorem isPushout_spec_map_of_isPullback_of_surjective
    {A A' B B' : CommRingCat.{u}} (p : A' ⟶ A) (q : B ⟶ A)
    (p' : B' ⟶ B) (q' : B' ⟶ A') (h : IsPullback p' q' q p)
    (hp : Function.Surjective p) :
    IsPushout (Spec.map p) (Spec.map q) (Spec.map q') (Spec.map p') :=
  IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace
    (isPushout_specLocallyRingedSpaceMap_of_isPullback p q p' q' h hp)

end Stacks.Pushout

end
