module

public import StacksFrontier.AlgebraicGeometry.Morphisms.RingMapProperty.Defs
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Ring maps with Noetherian target

The property of a commutative-ring homomorphism that its target is Noetherian is local in the
sense of the Stacks Project, and is stable under composition.

## Main results

* `RingHom.noetherianTarget_propertyIsLocal` states locality of the Noetherian-target property.
* `RingHom.noetherianTarget_stableUnderComposition` states stability under composition.

## Implementation notes

The property is expressed directly by `IsNoetherianRing` of the target. The locality condition
covers localization of the source and target and descent from a finite principal open cover of
the target.

## References

* [Stacks Project, Tag 01SX](https://stacks.math.columbia.edu/tag/01SX)
* [Stacks Project, Tag 01SZ](https://stacks.math.columbia.edu/tag/01SZ)
-/

@[expose] public section

universe u

namespace RingHom

/-- Having Noetherian target is local for commutative-ring homomorphisms. -/
@[stacks 01SX "noetherian_target_is_local"]
theorem noetherianTarget_propertyIsLocal :
    RingHom.StacksPropertyIsLocal
      (fun {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S) =>
        IsNoetherianRing S) :=
  ⟨by
    intro R S _ _ f r R' S' _ _ _ _ _ _ hS
    exact IsLocalization.isNoetherianRing (Submonoid.powers (f r)) S' hS,
   by
    intro R A Rf Aa _ _ _ _ f a _ _ _ _ g hA
    exact IsLocalization.isNoetherianRing (Submonoid.powers a) Aa hA,
   by
    intro R S _ _ f s hs hlocal
    exact AlgebraicGeometry.isNoetherianRing_of_away s hs hlocal⟩

/-- Having Noetherian target is stable under composition of commutative-ring
homomorphisms. -/
@[stacks 01SZ "noetherian_target_composition"]
theorem noetherianTarget_stableUnderComposition : RingHom.StableUnderComposition
    (fun {R S : Type u} [CommRing R] [CommRing S] (_ : R →+* S) => IsNoetherianRing S) := by
  intro R A B _ _ _ f g h₁ h₂; exact h₂

end RingHom
