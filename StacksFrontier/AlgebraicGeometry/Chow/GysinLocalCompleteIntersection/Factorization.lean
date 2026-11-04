module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection

/-!
# Inheriting the factorization that makes a Gysin map exist

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Stacks 0FF3 says that the
Gysin map of a local complete intersection morphism `f : X ⟶ Y` of schemes locally of finite type
over `S` exists when `f` factors as an immersion followed by a smooth morphism, a condition
recorded as `Stacks.Chow.GysinMapExists` in
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection`. This file proves that the
condition passes from a composite to its first factor: if `f : X ⟶ Y` and `g : Y ⟶ Z` are
morphisms and the Gysin map exists for `g ∘ f`, then it exists for `f`.

This is the first assertion of Stacks 0FF5, and the Stacks Project's argument for it: an immersion
`i : X ⟶ P` into a scheme `P` smooth over `Z` induces an immersion of `X` into `P ×_Z Y`, which is
smooth over `Y`. Applied to the structure morphism of a scheme smooth over the base it gives the
first assertion of Stacks 0FFB and of Stacks 0FFC, that the Gysin map exists for every morphism
whose source is smooth over the base.

## Main results

* `Stacks.Chow.GysinMapExists.left_of_comp` — the first assertion of Stacks 0FF5: the Gysin map
  exists for `f` as soon as it exists for `f ≫ g`.
* `Stacks.Chow.GysinMapExists.of_smooth_source` — the first assertion of Stacks 0FFB and of
  Stacks 0FFC: the Gysin map exists for a morphism over a base whose source is smooth over that
  base.

## Implementation notes

Neither hypothesis of Stacks 0FF5 beyond the factorization of the composite is used: `f` and `g`
need not be local complete intersection morphisms, the schemes need not be locally of finite type
over a base, and the factorization of `g` itself — which Stacks 0FF5 also assumes, for the sake of
its second assertion — is not needed. The statements below are therefore about arbitrary morphisms
of schemes, and specialize to the source's situation.

The scheme `P ×_Z Y` is the chosen categorical pullback `CategoryTheory.Limits.pullback`, the
immersion of `X` into it is `CategoryTheory.Limits.pullback.lift`, and its smooth structure
morphism to `Y` is `CategoryTheory.Limits.pullback.snd`, smooth because smoothness is stable under
base change. That the lift is an immersion is `AlgebraicGeometry.IsImmersion.of_comp`: composing
it with the projection to `P` gives back the immersion `i`.

### What is not proved

The second assertion of Stacks 0FF5, that `(g ∘ f)^! = f^! ∘ g^!`, and the identities asserted by
Stacks 0FFB and Stacks 0FFC, are not proved, and cannot be stated in this repository: the Gysin
map `f^!` itself is not constructed, for the reasons set out in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection`. Nor is the intersection
product that appears in Stacks 0FFB and Stacks 0FFC.

## References

* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
* [Stacks Project, Tag 0FFB](https://stacks.math.columbia.edu/tag/0FFB)
* [Stacks Project, Tag 0FFC](https://stacks.math.columbia.edu/tag/0FFC)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- **Stacks 0FF5, first assertion.** If the Gysin map exists for a composite `f ≫ g`, then it
exists for `f`.

Given a factorization `f ≫ g = i ≫ q` with `i : X ⟶ P` an immersion and `q : P ⟶ Z` smooth, the
morphism `X ⟶ P ×_Z Y` induced by `i` and `f` is an immersion, because composing it with the
projection to `P` returns `i`, and the projection `P ×_Z Y ⟶ Y` is smooth, being a base change of
`q`. Their composite is `f`. -/
@[stacks 0FF5 "the Gysin map exists for the first factor of the composite"]
theorem GysinMapExists.left_of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : GysinMapExists (f ≫ g)) : GysinMapExists f := by
  obtain ⟨P, i, q, hi, hq, hcomp⟩ := h
  have _ : Smooth q := hq
  refine ⟨pullback q g, pullback.lift i f hcomp, pullback.snd q g, ?_, inferInstance,
    pullback.lift_snd i f hcomp⟩
  have _ : IsImmersion (pullback.lift i f hcomp ≫ pullback.fst q g) := by
    rw [pullback.lift_fst]
    exact hi
  exact IsImmersion.of_comp _ (pullback.fst q g)

/-- **Stacks 0FFB and Stacks 0FFC, first assertion.** The Gysin map exists for a morphism
`f : X ⟶ Y` over a base `S` whose source is smooth over `S`.

Indeed `f ≫ sY` is the structure morphism `sX : X ⟶ S`, for which the Gysin map exists because a
smooth morphism is its own factorization through the identity of its source. Over a field this is
the assertion of Stacks 0FFB and of Stacks 0FFC that the Gysin map exists for a morphism of
schemes smooth over the field; smoothness of the target is not needed. -/
@[stacks 0FFB "the Gysin map exists for a morphism of schemes smooth over the base",
  stacks 0FFC "the Gysin map exists for a morphism of schemes smooth over the base"]
theorem GysinMapExists.of_smooth_source {X Y S : Scheme.{u}} (f : X ⟶ Y) (sY : Y ⟶ S)
    (sX : X ⟶ S) [Smooth sX] (hbase : f ≫ sY = sX) : GysinMapExists f := by
  refine GysinMapExists.left_of_comp f sY ?_
  rw [hbase]
  exact GysinMapExists.of_smooth sX

end Stacks.Chow

end
