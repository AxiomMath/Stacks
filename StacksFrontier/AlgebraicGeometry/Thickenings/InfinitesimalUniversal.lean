module

public import StacksFrontier.AlgebraicGeometry.Thickenings.Infinitesimal
public import StacksFrontier.AlgebraicGeometry.Thickenings.UniversalConormalSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal neighbourhood as a universal first-order thickening

Let `i : Z ⟶ X` be an immersion of schemes. Then `i` is formally unramified, and its first-order
infinitesimal neighbourhood is a universal first-order thickening of `i` over `X` in the sense of
`Stacks.Thickenings.IsUniversalFirstOrderThickening`.

## Main definitions

* `Stacks.Thickenings.firstOrderInfinitesimalThickening` packages the first-order infinitesimal
  neighbourhood of an immersion as a `Stacks.Thickenings.UniversalFirstOrderThickening`.
* `Stacks.Thickenings.infinitesimalConormalSheafMap` is the morphism of conormal sheaves
  `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` of [Stacks Project, Tag 04F0].

## Main results

* `Stacks.Thickenings.formallyUnramified_of_isImmersion`: an immersion is formally unramified.
* `Stacks.Thickenings.isUniversalFirstOrderThickening_nthOrderInclusion_one`: the first-order
  infinitesimal neighbourhood is a universal first-order thickening.

## Implementation notes

`Stacks.Thickenings.formallyUnramified_of_isImmersion` is a theorem rather than an instance:
Mathlib's instance for a morphism with open-immersion diagonal already applies.

## References

* [Stacks Project, Tag 04EY](https://stacks.math.columbia.edu/tag/04EY)
* [Stacks Project, Tag 04F0](https://stacks.math.columbia.edu/tag/04F0)
* [Stacks Project, Tag 04F5](https://stacks.math.columbia.edu/tag/04F5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction

universe u

namespace Stacks.Thickenings

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]

/-! ### Formal unramifiedness -/

/-- An immersion of schemes is formally unramified. -/
@[ega "IV 17.1.3" "(i), special case"]
theorem formallyUnramified_of_isImmersion : FormallyUnramified i := inferInstance

/-! ### The universal property -/

/-- The first-order infinitesimal neighbourhood of an immersion `i : Z ⟶ X` is a universal
first-order thickening of `i` over `X`. -/
theorem isUniversalFirstOrderThickening_nthOrderInclusion_one :
    IsUniversalFirstOrderThickening i (nthOrderInclusion i 1) (nthOrderToBase i 1) where
  isFirstOrderThickening := nthOrderInclusion_isFirstOrderThickening i
  inclusion_toBase := nthOrderInclusion_toBase i 1
  existsUnique_lift := existsUnique_firstOrderLift i

/-- The first-order infinitesimal neighbourhood of an immersion, packaged as a
`Stacks.Thickenings.UniversalFirstOrderThickening` of the immersion over its target. -/
def firstOrderInfinitesimalThickening : UniversalFirstOrderThickening i where
  ambient := firstOrderInfinitesimalNeighbourhood i
  inclusion := nthOrderInclusion i 1
  toBase := nthOrderToBase i 1
  isUniversal := isUniversalFirstOrderThickening_nthOrderInclusion_one i

@[simp]
theorem firstOrderInfinitesimalThickening_inclusion :
    (firstOrderInfinitesimalThickening i).inclusion = nthOrderInclusion i 1 := rfl

@[simp]
theorem firstOrderInfinitesimalThickening_toBase :
    (firstOrderInfinitesimalThickening i).toBase = nthOrderToBase i 1 := rfl

/-! ### The conormal sheaf comparison -/

/-- The commutative square of ringed spaces
```
Z  ⟶  Z₁
↓      ↓
Z  ⟶  coborderRange i
```
whose horizontal arrows are the inclusion of `Z` into its first-order infinitesimal
neighbourhood and the closed-immersion factorization of `i`, and whose right vertical arrow is
the closed immersion of the neighbourhood into the canonical open neighbourhood of the image of
`i`. -/
theorem toShHom_nthOrderInclusion_nthOrderι :
    (nthOrderInclusion i 1).toLRSHom.toShHom ≫ (nthOrderι i 1).toLRSHom.toShHom =
      𝟙 Z.toLocallyRingedSpace.toRingedSpace ≫ i.liftCoborder.toLRSHom.toShHom :=
  (congrArg (fun p : Z ⟶ i.coborderRange.toScheme => p.toLRSHom.toShHom)
    (nthOrderInclusion_nthOrderι i 1)).trans (Category.id_comp _).symm

/-- The morphism of conormal sheaves `𝒞_{Z/X} ⟶ 𝒞_{Z/Z'}` induced by the square
`Stacks.Thickenings.toShHom_nthOrderInclusion_nthOrderι` relating `Z ⊂ Z'` to the
closed-immersion factorization of `i`, where `Z'` is the first-order infinitesimal neighbourhood
of `Z` in `X`. -/
def infinitesimalConormalSheafMap :
    (modulePullback (𝟙 Z.toLocallyRingedSpace.toRingedSpace)).obj (immersionConormalSheaf i) ⟶
      schemeConormalSheaf (nthOrderInclusion i 1) :=
  Stacks.ClosedImmersion.conormalSheafMap (toShHom_nthOrderInclusion_nthOrderι i)

end Stacks.Thickenings

end
