module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.UniversallyClosedTest

/-!
# Testing properness on finite type base changes

For a separated morphism of finite type `f : X ⟶ S` the following are equivalent: `f` is proper;
every base change of `f` along a morphism locally of finite type is a closed map; and the base
change of `f` to affine `n`-space over `S` is a closed map for every natural number `n`.

## Main results

* `AlgebraicGeometry.isProper_tfae`: for a separated morphism of finite type, properness is
  equivalent to closedness of its base changes along morphisms locally of finite type, and to
  closedness of its base changes to all affine spaces over the base.

## References

* [Stacks Project, Tag 0205](https://stacks.math.columbia.edu/tag/0205)
-/

public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A separated morphism of finite type is proper precisely when all of its base changes along
morphisms locally of finite type are closed, or equivalently when its base changes to all
finite-dimensional affine spaces are closed.

The second condition is the hypothesis that `X ×_S S' ⟶ S'` is a closed map for every `S' ⟶ S`
locally of finite type, and the third that `𝔸(n; X) ⟶ 𝔸(n; S)`, the base change of `f` along
`𝔸(n; S) ↘ S`, is a closed map for every `n`. -/
@[stacks 0205]
theorem isProper_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE
      [IsProper f,
       ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
         LocallyOfFiniteType g → IsClosedMap (pullback.snd f g),
       ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f)] := by
  tfae_have 1 → 2 := fun hf S' g _ =>
    hf.toUniversallyClosed.universally_isClosedMap _ _ _ (IsPullback.of_hasPullback f g).flip
  tfae_have 1 → 3 := fun hf n =>
    hf.toUniversallyClosed.universally_isClosedMap _ _ _ (AffineSpace.isPullback_map f)
  tfae_have 2 → 1 := fun h =>
    have : UniversallyClosed f :=
      ((universallyClosed_tfae f).out 2 1).mp fun S' g (_ : LocallyOfFinitePresentation g) =>
        h S' g inferInstance
    ⟨⟩
  tfae_have 3 → 1 := fun h =>
    have : UniversallyClosed f := ((universallyClosed_tfae f).out 3 1).mp h
    ⟨⟩
  tfae_finish

end AlgebraicGeometry

end
