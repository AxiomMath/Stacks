module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.FunctorOfPoints
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Representability

/-!
# Composing and comparing morphisms into a relative spectrum

Let `(X, A)` be a relative-spectrum situation. By representability ([Stacks, Tag 01LV],
`Stacks.RelativeSpec.relativeSpecRepresentableBy`) a morphism `T ⟶ Spec_X(A)` is the same thing
as a relative-spectrum pair over `T`, the correspondence being
`Stacks.RelativeSpec.pairToHom` in one direction and pullback of the universal pair in the other.
Consequently:

* precomposing a morphism attached to a pair gives the morphism attached to the pulled-back pair,
  so a composite `T' ⟶ T ⟶ Spec_X(A)` is again presented by a pair; and
* two morphisms into the relative spectrum with the same pair are equal.

## Main results

* `Stacks.RelativeSpec.comp_pairToHom`:
  `m ≫ pairToHom p = pairToHom (RelativeSpecPair.pullback m p)`.
* `Stacks.RelativeSpec.pairToHom_injective`: distinct pairs give distinct morphisms.
* `Stacks.RelativeSpec.hom_ext_of_pullback_universalRelativeSpecPair`: **two morphisms into the
  relative spectrum are equal as soon as they pull the universal pair back to the same pair.**

## References

* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.RelativeSpec

variable {s : RelativeSpecSituation.{u}} {T T' : Scheme.{u}}

/-- **Precomposition of the morphism attached to a relative-spectrum pair is the morphism
attached to the pulled-back pair.** -/
theorem comp_pairToHom (m : T' ⟶ T) (p : RelativeSpecPair s T) :
    m ≫ pairToHom p = pairToHom (RelativeSpecPair.pullback m p) :=
  (pairToHom_pullback_universalRelativeSpecPair (m ≫ pairToHom p)).symm.trans
    (congrArg pairToHom
      ((RelativeSpecPair.pullback_comp m (pairToHom p) (universalRelativeSpecPair s)).trans
        (congrArg (RelativeSpecPair.pullback m)
          (pullback_universalRelativeSpecPair_pairToHom p))))

/-- **The morphism attached to a relative-spectrum pair determines the pair.** -/
theorem pairToHom_injective :
    Function.Injective (pairToHom (s := s) (T := T)) :=
  Function.LeftInverse.injective
    (g := fun m => RelativeSpecPair.pullback m (universalRelativeSpecPair s))
    pullback_universalRelativeSpecPair_pairToHom

/-- **Extensionality for morphisms into a relative spectrum**: two morphisms that pull the
universal pair back to the same relative-spectrum pair are equal. -/
theorem hom_ext_of_pullback_universalRelativeSpecPair
    (m m' : T ⟶ (gluedSpectrum s).scheme)
    (h : RelativeSpecPair.pullback m (universalRelativeSpecPair s) =
      RelativeSpecPair.pullback m' (universalRelativeSpecPair s)) : m = m' :=
  (pairToHom_pullback_universalRelativeSpecPair m).symm.trans
    ((congrArg pairToHom h).trans (pairToHom_pullback_universalRelativeSpecPair m'))

end Stacks.RelativeSpec

end
