module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.GysinMap
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange

/-!
# The Gysin map of a local complete intersection morphism commutes with every class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
local complete intersection morphism of schemes locally of finite type over `S` for which the
Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3 exists. **Stacks 0FF6** states that for a diagram
of cartesian squares

  `X'' ⟶ X' ⟶ X`,  `Y'' ⟶ Y' ⟶ Y`

over `f` and a class `c ∈ A^*(Y'' ⟶ Y')`, the restriction `res(f^!) ∈ A^*(X' ⟶ Y')^∧` of `f^!` to
`Y'` (Stacks 0F9Z) and `c` commute (Stacks 0FA2). As `X' = X ×_Y Y'` and `X'' = X' ×_{Y'} Y''` are
the fibre products, this says: for every `g : Y' ⟶ Y` locally of finite type, the restriction of
`f^!` along `g` commutes with every bivariant class over `Y'`, in every degree.

## Main results

* `Stacks.Chow.SmoothFactorization.completedCommutesAfterBaseChange_gysinMap` — the class
  `i^! ∘ g^*` of any factorization of `f` commutes with every class after every base change.
* `Stacks.Chow.completedCommutesWithEveryClass_completedBivariantRestriction_lciGysinMap` —
  **Stacks 0FF6**.

## Implementation notes

The proof is the one of the source. For a factorization `f = g ∘ i` with `g` smooth and `i` an
immersion, `f^! = i^! ∘ g^*`; the class `g^*` is a flat pullback, whose restrictions are flat
pullbacks and commute with every class by the definition of a bivariant class, and the class `i^!`
is, on each connected component, the composite of the class of a virtual normal bundle of
constant rank for a closed immersion with a flat pullback along an open immersion, whose
restrictions are again classes of virtual normal bundles (Stacks 0FBK with Stacks 0FBJ) and so
commute with every class by Stacks 0FBP. The bookkeeping on completed groups is
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CommutingAfterBaseChange`.

## References

* [Stacks Project, Tag 0FF6](https://stacks.math.columbia.edu/tag/0FF6)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0F9Z](https://stacks.math.columbia.edu/tag/0F9Z)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] {f : X ⟶ Y} [LocallyOfFiniteType f]
  (hf : f ≫ sY = sX)

/-- **The Gysin map of a factorization commutes with every class after every base change.** For
a factorization `f = g ∘ i` of a local complete intersection morphism, with `i` an immersion and
`g` smooth, the class `i^! ∘ g^* ∈ A^*(X ⟶ Y)^∧` of Stacks 0FF3: `i^!` and `g^*` both do, and so
does their composite. -/
theorem SmoothFactorization.completedCommutesAfterBaseChange_gysinMap (F : SmoothFactorization f)
    (hlci : IsLocalCompleteIntersectionMorphism f) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    completedCommutesAfterBaseChange C sX sY f hf (F.gysinMap C sX sY hf hlci) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian F.ambient := LocallyOfFiniteType.isLocallyNoetherian (F.proj ≫ sY)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  exact (completedCommutesAfterBaseChange_copy C sX sY _ _ _ _ _).2
    (completedCommutesAfterBaseChange_completedBivariantCompositeOfInvertible C sX (F.proj ≫ sY)
      F.imm _ sY F.proj rfl _ _
      (completedCommutesAfterBaseChange_completedVirtualNormalGysinClassOfImmersion C sX
        (F.proj ≫ sY) F.imm _ _)
      (completedCommutesAfterBaseChange_completedFlatPullbackOfSmooth C _ sY F.proj rfl))

/-- **The Gysin map commutes with every class after every base change.** The Gysin map
`f^! ∈ A^*(X ⟶ Y)^∧` of a local complete intersection morphism for which it exists (Stacks 0FF3)
commutes with every class after every base change. -/
theorem completedCommutesAfterBaseChange_lciGysinMap (hlci : IsLocalCompleteIntersectionMorphism f)
    (h : GysinMapExists f) :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    completedCommutesAfterBaseChange C sX sY f hf (lciGysinMap C sX sY hf hlci h) :=
  SmoothFactorization.completedCommutesAfterBaseChange_gysinMap C sX sY hf _ hlci

/-- **Stacks 0FF6.** Let `f : X ⟶ Y` be a local complete intersection morphism of schemes locally
of finite type over the base such that the Gysin map `f^! ∈ A^*(X ⟶ Y)^∧` exists (Stacks 0FF3).
For every `g : Y' ⟶ Y` locally of finite type, the restriction `res(f^!) ∈ A^*(X' ⟶ Y')^∧` of
`f^!` along `g` (Stacks 0F9Z), `X' = X ×_Y Y'`, commutes with every bivariant class
`c ∈ A^q(Y'' ⟶ Y')`, for every `Y'' ⟶ Y'` locally of finite type and every degree `q`, in the sense
of Stacks 0FA2, degree by degree: every term of the tuple attached to `res(f^!)` by Stacks 0FE0
commutes with `c`. -/
@[stacks 0FF6 "for every Y' → Y, the restriction res(f^!) ∈ A^*(X' → Y')^∧ of the Gysin map of a \
local complete intersection morphism commutes with every c ∈ A^q(Y'' → Y'), every Y'' → Y' and q"]
theorem completedCommutesWithEveryClass_completedBivariantRestriction_lciGysinMap
    (hlci : IsLocalCompleteIntersectionMorphism f) (h : GysinMapExists f) {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] :
    haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
    haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
    haveI : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
    haveI : IsLocallyNoetherian (pullback f g) :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
    completedCommutesWithEveryClass C (pullback.fst f g ≫ sX) (g ≫ sY) (pullback.snd f g)
      (pullbackSnd_comp_structureMorphism_eq C sX sY f hf g)
      (completedBivariantRestrictionViaSequence C sX sY f hf g
        (lciGysinMap C sX sY hf hlci h)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  have : IsLocallyNoetherian Y' := LocallyOfFiniteType.isLocallyNoetherian (g ≫ sY)
  have : IsLocallyNoetherian (pullback f g) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst f g ≫ sX)
  exact (completedCommutesAfterBaseChange_lciGysinMap C sX sY hf hlci
    h).completedCommutesWithEveryClass_restriction g

end Stacks.Chow

end
