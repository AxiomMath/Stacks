module

public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.DeformationDiagrams

/-!
# Properties inherited by the special fibre of a cartesian morphism of thickenings

Let

```
X --f--→ Y
|        |
i        j
↓        ↓
X' -f'-→ Y'
```

be a cartesian morphism of thickenings of algebraic spaces over `S`, so that `X` is
`Y ×_{Y'} X'`. Then `f` is the base change of `f'` along the inclusion `j`, and every property
of morphisms of algebraic spaces which is stable under base change passes from `f'` to `f`
without any further hypothesis. Collected here are four such properties on the list of
Tag 0BPJ: being a closed immersion, being an immersion, being a monomorphism and being
proper.

## Main results

* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.isPullback_spaces`:
  the cartesian square read in the category of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.CartesianLocallyFiniteTypeMorphismOfThickenings.isClosedImmersion`,
  `.isImmersion`, `.mono` and `.isProper`: each property descends from the morphism of ambient
  spaces to the morphism of closed subspaces.

## Implementation notes

The smaller spaces of the two thickenings are given as subfunctors of their ambient spaces, and
a thickening is in particular a closed subspace, hence itself an algebraic space; the two
objects of `AlgebraicGeometry.AlgebraicSpaces` carrying them are therefore built from the first
components of the two thickening hypotheses. Closed immersions, immersions and properness are
stated in that category, so the cartesian square has to be transported into it; the inclusion
functor of a full subcategory is faithful, so `CategoryTheory.IsPullback.of_map_of_faithful`
transports it. Being a monomorphism is a statement about the morphisms of presheaves themselves
and takes the square as it stands.

## References

* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 042P](https://stacks.math.columbia.edu/tag/042P)
* [Stacks Project, Tag 04WP](https://stacks.math.columbia.edu/tag/04WP)
* [Stacks Project, Tag 0BPJ](https://stacks.math.columbia.edu/tag/0BPJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

namespace CartesianLocallyFiniteTypeMorphismOfThickenings

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (T : CartesianLocallyFiniteTypeMorphismOfThickenings B S hS)

/-- The smaller source of a cartesian morphism of thickenings, as an algebraic space over
`S`. -/
abbrev sourceSpace : AlgebraicSpaces B S hS := ⟨T.X.toFunctor, T.sourceThickening.1.1⟩

/-- The smaller target of a cartesian morphism of thickenings, as an algebraic space over
`S`. -/
abbrev targetSpace : AlgebraicSpaces B S hS := ⟨T.Y.toFunctor, T.targetThickening.1.1⟩

/-- The cartesian square of a cartesian morphism of thickenings, read in the category of
algebraic spaces over `S`. -/
theorem isPullback_spaces :
    IsPullback (ObjectProperty.homMk T.X.ι : T.sourceSpace ⟶ T.X')
      (ObjectProperty.homMk T.f : T.sourceSpace ⟶ T.targetSpace)
      (ObjectProperty.homMk T.f' : T.X' ⟶ T.Y')
      (ObjectProperty.homMk T.Y.ι : T.targetSpace ⟶ T.Y') :=
  IsPullback.of_map_of_faithful
    (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F))
    T.cartesian.flip

/-- If the morphism of ambient spaces is a closed immersion, so is the morphism of the closed
subspaces: it is a base change of it. -/
theorem isClosedImmersion (hf' : IsClosedImmersion B S hS T.f') :
    IsClosedImmersion B S hS T.f :=
  isClosedImmersion_of_isPullback B S hS T.isPullback_spaces hf'

/-- If the morphism of ambient spaces is an immersion, so is the morphism of the closed
subspaces: it is a base change of it. -/
theorem isImmersion (hf' : IsImmersion B S hS T.f') : IsImmersion B S hS T.f :=
  isImmersion_of_isPullback B S hS T.isPullback_spaces hf'

/-- If the morphism of ambient spaces is proper, so is the morphism of the closed subspaces:
it is a base change of it. -/
theorem isProper (hf' : IsProper B S hS T.f') : IsProper B S hS T.f :=
  (isProper_isStableUnderBaseChange B S hS).of_isPullback T.isPullback_spaces hf'

/-- If the morphism of ambient spaces is a monomorphism, so is the morphism of the closed
subspaces: it is a base change of it. -/
theorem mono (hf' : Mono T.f') : Mono T.f :=
  (MorphismProperty.monomorphisms _).of_isPullback T.cartesian.flip hf'

end CartesianLocallyFiniteTypeMorphismOfThickenings

end AlgebraicGeometry.Space

end
