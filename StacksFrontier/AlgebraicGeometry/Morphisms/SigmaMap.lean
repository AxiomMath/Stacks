module

public import StacksFrontier.AlgebraicGeometry.Morphisms.ProperCoproduct

/-!
# Disjoint unions and properties of morphisms local at the target

A property of morphisms of schemes which is Zariski local at the target is stable under finite
disjoint unions: if `g j : X j ⟶ Y j` has the property for every member of a finite family, then
so does the induced morphism `∐ X ⟶ ∐ Y` of coproducts.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap`: a finite disjoint union of morphisms with
  a property local at the target again has that property.

## Implementation notes

The coproduct inclusions of the target form an open cover, and the van Kampen property of finite
coproducts in `AlgebraicGeometry.Scheme`, recorded as
`AlgebraicGeometry.isPullback_sigmaMap`, identifies the base change of `∐ X ⟶ ∐ Y` along the
`j`-th inclusion with `g j`. This is the argument `AlgebraicGeometry.isProper_sigmaMap` makes for
properness; stated once for an arbitrary property it applies verbatim to every other property
local at the target.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.IsZariskiLocalAtTarget

/-- A property of morphisms of schemes which is Zariski local at the target is stable under
finite disjoint unions: the induced morphism of coproducts has the property as soon as every
member of the family does. -/
theorem sigmaMap {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P] {ι : Type v}
    [Finite ι] {X Y : ι → Scheme.{u}} (g : ∀ j, X j ⟶ Y j) (hg : ∀ j, P (g j)) :
    P (Limits.Sigma.map g) := by
  refine IsZariskiLocalAtTarget.of_openCover (P := P) (sigmaOpenCover Y) fun j => ?_
  have h : P (pullback.snd (Limits.Sigma.map g) (Sigma.ι Y j)) := by
    rw [← MorphismProperty.cancel_left_of_respectsIso P
        (isPullback_sigmaMap g j).isoPullback.hom,
      (isPullback_sigmaMap g j).isoPullback_hom_snd]
    exact hg j
  exact h

end AlgebraicGeometry.IsZariskiLocalAtTarget

end
