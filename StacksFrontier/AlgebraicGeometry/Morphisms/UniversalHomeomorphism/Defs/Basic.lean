module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Universal homeomorphisms of schemes

A morphism of schemes is a universal homeomorphism if every base change of it induces a
homeomorphism on the underlying topological spaces.

## Main definitions

* `AlgebraicGeometry.UniversalHomeomorphism` is the property of being a universal
  homeomorphism of schemes.

## Main results

* `AlgebraicGeometry.universalHomeomorphism_iff` unfolds the property in terms of all
  pullback squares.
* `AlgebraicGeometry.universalHomeomorphism_comp`: universal homeomorphisms are stable under
  composition.

## Implementation notes

The definition uses `MorphismProperty.universally`, so it is independent of a chosen pullback
object. Thus it quantifies over every pullback square presenting the base change, rather than
choosing a displayed fibre product.

## References

* [Stacks Project, Tag 04DD](https://stacks.math.columbia.edu/tag/04DD)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A morphism of schemes is a universal homeomorphism if every base change is
a homeomorphism on the underlying topological spaces. -/
@[mk_iff, stacks 04DD, ega "IV 2.4.2" "universal homeomorphism", sga "4 VIII 1.4"]
class UniversalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- Every base change of `f` is a homeomorphism on the underlying topological spaces. -/
  universally_isHomeomorph : (topologically @IsHomeomorph).universally f

open CategoryTheory in
/-- Universal homeomorphisms are stable under composition. -/
theorem universalHomeomorphism_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : UniversalHomeomorphism f) (hg : UniversalHomeomorphism g) :
    UniversalHomeomorphism (f ≫ g) := by
  have := topologically_isStableUnderComposition (P := @IsHomeomorph)
    (fun _ _ hf hg => hg.comp hf)
  exact ⟨MorphismProperty.comp_mem _ f g hf.1 hg.1⟩

end AlgebraicGeometry

end
