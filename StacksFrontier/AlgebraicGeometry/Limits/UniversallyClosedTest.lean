module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.General.Basic

/-!
# Testing universal closedness on finitely presented base changes (Stacks 05JX)

For a quasi-compact morphism of schemes `f : X ⟶ S` the following are equivalent: `f` is
universally closed; every base change of `f` along a morphism locally of finite presentation
is a closed map; and the base change of `f` to affine `n`-space over `S` is a closed map for
every natural number `n`.

## Main results

* `AlgebraicGeometry.universallyClosed_tfae`: **Stacks 05JX**.

## Implementation notes

(1) implies (2) and (1) implies (3) are instances of universal closedness.

The two substantial implications are proved in
`StacksFrontier.AlgebraicGeometry.General.Basic`, each as a statement in its own right, and this
file only assembles them into the equivalence:

* (2) implies (1) is the limit argument, in
  `Stacks.AlgebraicGeometry.Tag05JXGeneral.universallyClosed_of_forall_isClosedMap_pullbackSnd`.
  Closedness of an arbitrary base change is tested by `isClosedMap_iff_specializingMap`, and a
  specialisation with no lift is separated from the closure of the source point already over an
  affine base locally of finite presentation by **Stacks 05BD**, where hypothesis (2) applies
  and contradicts the separation.
* (3) implies (2) is Zariski local on the target, in the same namespace's
  `isClosedMap_pullbackSnd_of_forall_isClosedMap_affineSpaceMap`.
  Over an affine open of `S` and an affine open of `S'` mapping into it, a morphism locally of
  finite presentation of affine schemes is a closed immersion into affine `n`-space, because a
  finitely presented algebra is a quotient of a polynomial algebra; closedness then passes down
  along that immersion.

## References

* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
* [Stacks Project, Tag 05BD](https://stacks.math.columbia.edu/tag/05BD)
-/

public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.Tag05JXGeneral

universe u

namespace AlgebraicGeometry

/-- **Stacks 05JX.** A quasi-compact morphism is universally closed precisely when all of its
locally finitely presented base changes are closed, or equivalently when its
base changes to all finite-dimensional affine spaces are closed. -/
@[stacks 05JX]
theorem universallyClosed_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] :
    List.TFAE
      [UniversallyClosed f,
       ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
         LocallyOfFinitePresentation g → IsClosedMap (pullback.snd f g),
       ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)] := by
  tfae_have 1 → 3 := fun hf n =>
    hf.universally_isClosedMap _ _ _ (AffineSpace.isPullback_map f)
  tfae_have 3 → 2 := fun h S' g _ =>
    isClosedMap_pullbackSnd_of_forall_isClosedMap_affineSpaceMap f h S' g
  tfae_have 2 → 1 := fun h =>
    universallyClosed_of_forall_isClosedMap_pullbackSnd f h
  tfae_finish

end AlgebraicGeometry

end
