module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Pullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous

/-!
# The base-change comparison for direct image on small étale sites

Given a commutative square of schemes
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
there is a canonical comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` between the two ways of travelling
around the square on sheaves of sets for the small étale topology. It is constructed here as the
*mate*, with respect to the two inverse-image/direct-image adjunctions along `g` and `g'`, of the
identification of the two composite direct-image functors `(g' ≫ f)_* = (f' ≫ g)_*` obtained
from the commutativity of the square and the composition isomorphism
`smallEtalePushforwardCompIso`. Being a mate is what makes it canonical: no choice enters beyond
the equality `g' ≫ f = f' ≫ g` itself.

Stacks 0EYP asserts that this comparison is an isomorphism when the square is cartesian and `f`
is integral. That assertion is *not* proved here; see the module docstring note below.

## Main definitions

* `Stacks.EtaleCohomology.baseChangeNatTrans` — the canonical comparison
  `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for a commutative square.

## Implementation notes

The target of the comparison is written with
`Stacks.EtaleCohomology.smallEtaleInverseImage`, which is definitionally the left Kan extension
followed by sheafification, i.e. Mathlib's `Functor.sheafPullbackConstruction.sheafPullback` for
the base-change site functor; that is the left adjoint appearing in the mate correspondence.

## References

* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- The canonical base-change comparison `g⁻¹ f_* ⟶ f'_* (g')⁻¹` attached to a commutative
square `g' ≫ f = f' ≫ g` of schemes, for sheaves of sets on the small étale sites. It is the
mate, along the two inverse-image/direct-image adjunctions for `g` and `g'`, of the canonical
identification of the two composite direct images around the square. -/
public def baseChangeNatTrans {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    (smallEtaleBaseChange f).sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X) ⋙
      smallEtaleInverseImage.{u, v} g ⟶
    smallEtaleInverseImage.{u, v} g' ⋙
      (smallEtaleBaseChange f').sheafPushforwardContinuous
        (Type (max (u + 1) v)) (smallEtaleTopology Y') (smallEtaleTopology X') :=
  (mateEquiv
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange g') (Type (max (u + 1) v))
        (smallEtaleTopology X) (smallEtaleTopology X'))
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange g) (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology Y'))).symm
    ((smallEtalePushforwardCompIso g' f).hom ≫
      (eqToIso (congrArg (fun k : X' ⟶ Y ↦
        (smallEtaleBaseChange k).sheafPushforwardContinuous
          (Type (max (u + 1) v)) (smallEtaleTopology Y) (smallEtaleTopology X')) h)).hom ≫
      (smallEtalePushforwardCompIso f' g).inv)

end Stacks.EtaleCohomology

end
