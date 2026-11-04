module

public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.StacksAttribute

/-!
# Stalk maps of finite-type morphisms are essentially of finite presentation

`AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap` shows
that every stalk map of a morphism locally of finite presentation is essentially of finite
presentation, in the universe-polymorphic spelling
`RingHom.EssentiallyOfFinitePresentation`. Two adjustments make it usable as the
`essentiallyOfFinitePresentation` field of
`AlgebraicGeometry.FlatLocalKoszulDeformationSituation`, which is what [Stacks, Tag 0G0R] needs
when it applies [Stacks, Tag 0G0N] to `𝒪_{S,s} → 𝒪_{X ×_S Y, z}`:

* the field is stated with the single-universe predicate `IsEssentiallyOfFinitePresentation`, so
  the bridge `RingHom.EssentiallyOfFinitePresentation.isEssentiallyOfFinitePresentation` must be
  applied;
* the morphisms 0G0R has in hand are of *finite type*, not of finite presentation — `X ×_S Y ⟶ S`
  is proper, hence of finite type. Over a locally Noetherian base the two agree, by Mathlib's
  instance
  `AlgebraicGeometry.instLocallyOfFinitePresentationOfIsLocallyNoetherianOfLocallyOfFiniteType`,
  and the base `S` of 0G0R is of finite type over a field, hence locally Noetherian.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.isEssentiallyOfFinitePresentation_stalkMap` — for
  `f : X ⟶ Y` locally of finite type with `Y` locally Noetherian, the stalk map
  `𝒪_{Y,f x} → 𝒪_{X,x}` is essentially of finite presentation, in the single-universe spelling.

## Implementation notes

No `stacks` attribute is carried. The underlying mathematical content is [Stacks, Tag 00QM] (2)
together with the Noetherian coincidence of finite type and finite presentation, both of which
are registered where they are proved; this is the composite the local-ring criteria consume.

## References

* [Stacks Project, Tag 00QM](https://stacks.math.columbia.edu/tag/00QM)
* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry

/-- **The stalk map of a finite-type morphism over a locally Noetherian base is essentially of
finite presentation**, in the single-universe spelling `IsEssentiallyOfFinitePresentation` that
`AlgebraicGeometry.FlatLocalKoszulDeformationSituation` asks for.

Over a locally Noetherian target, locally of finite type and locally of finite presentation
coincide, so this follows from
`AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap` and the
bridge between the two spellings of [Stacks, Tag 00QM] (2). -/
theorem LocallyOfFiniteType.isEssentiallyOfFinitePresentation_stalkMap {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    IsEssentiallyOfFinitePresentation (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (f.stalkMap x).hom :=
  (LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap f
    x).isEssentiallyOfFinitePresentation

end AlgebraicGeometry

end
