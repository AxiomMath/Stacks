module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.NormalMorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# Smooth morphisms are normal

A smooth morphism of schemes is normal: it is flat, and each of its fibres is geometrically
normal over the residue field of the point it lies over.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isNormal_of_smooth`: a smooth morphism is normal.

## Implementation notes

Normality of a morphism is `AlgebraicGeometry.Scheme.Hom.IsNormal` (Tag 0390), the conjunction
of flatness at the point and geometric normality of the fibre at the induced point. Flatness is
read off the stalk maps through Mathlib's `AlgebraicGeometry.Flat.iff_flat_stalkMap`, using that
a smooth morphism is flat. The fibre `f.fiber y` is by definition the pullback of `f` along
`Y.fromSpecResidueField y`, and `f.fiberToSpecResidueField y` is the second projection, so
stability of smoothness under base change makes the fibre smooth over `Spec κ(y)`; geometric
normality of the fibre is then the geometric-normality conclusion of Tag 056T.

The smoothness of the fibre has to be supplied as an explicit instance argument. Instance search
does not find it from a hypothesis stated at `f.fiberToSpecResidueField (f.base x)`, because the
instance that the application requires spells the point through the morphism's coercion rather
than through `Scheme.Hom.base`, and the two spellings are definitionally but not syntactically
equal.

## References

* [Stacks Project, Tag 056W](https://stacks.math.columbia.edu/tag/056W)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 0390](https://stacks.math.columbia.edu/tag/0390)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **Stacks Project, Tag 056W.** A smooth morphism of schemes is normal: it is flat at every
point and all of its fibres are geometrically normal. -/
@[stacks 056W, ega "IV 18.10.5" "more general"]
public theorem isNormal_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] : f.IsNormal := by
  intro x
  refine ⟨(Flat.iff_flat_stalkMap f).mp inferInstance x, ?_⟩
  have hsm : Smooth (f.fiberToSpecResidueField (f.base x)) := by
    show Smooth (pullback.snd f (Y.fromSpecResidueField (f.base x)))
    exact MorphismProperty.of_isPullback (P := @Smooth)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField (f.base x))) ‹Smooth f›
  exact (@isGeometricallyNormal_of_smooth _ _ _ _ hsm) (f.asFiber x)

end AlgebraicGeometry.Scheme.Hom

end
