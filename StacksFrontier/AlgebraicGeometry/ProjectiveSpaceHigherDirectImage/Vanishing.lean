module

public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images of the twists on projective space, outside the relative dimension

Let `S` be a scheme, let `n` be a natural number and let `f : ℙⁿ_S ⟶ S` be the structure
morphism of projective `n`-space over `S`. For every integer `d` the higher direct images
`Rᵠ f_* 𝒪(d)` of the degree-`d` twist of the structure sheaf vanish in every degree `q` outside
the range `0 ≤ q ≤ n`: below zero because a right derived functor vanishes in negative degrees,
and above `n` because the cohomology of a quasi-coherent module on projective `n`-space over an
affine base vanishes above `n` and that vanishing of higher direct images survives base change.

The names in the two lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace, where the
fully-qualified form would not fit on a line.

## Main definitions

* `twistOverPullbackIso`: the twists of the structure sheaf of projective space are stable
  under base change of the base scheme.

## Main results

* `isPullback_structureMorphism_projectiveSpaceOver`: the structure morphism of `ℙⁿ_S` is the
  base change of the structure morphism of projective `n`-space over the integers.
* `isQuasicoherent_twistOver`: every twist of the structure sheaf of `ℙⁿ_S` is quasi-coherent.
* `isZero_rightDerivedPlus_pushforward_twistOver`: **`Rᵠ f_* 𝒪(d) = 0` for `q < 0` and for
  `q > n`**, for every scheme `S`, every `n` and every `d`.

## Where the vanishing row of [Stacks, Tag 01XW] is carried

The two degrees proved here are the outside of the row; the band `1 ≤ q ≤ n - 1` is
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/MiddleVanishing.lean`, which
composes the two into the whole row and carries the `@[stacks 01XW]` attribute for it. Nothing
here carries that attribute, because a statement restricted to the two outer degrees is not a
clause of the tag.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

open Stacks.AlgebraicGeometry.ProjTwistTensorPow

attribute [local instance] HasDerivedCategory.standard

/-- **The twists of the structure sheaf of projective space are stable under base change.**
Pulling the degree-`d` twist `𝒪(d)` on `ℙⁿ_S` back along the morphism `ℙⁿ_{S'} ⟶ ℙⁿ_S` induced
by `g : S' ⟶ S` gives the degree-`d` twist on `ℙⁿ_{S'}`.

Both twists are pulled back from the integral model, and the base-change morphism is the
identity on the integral model by `AlgebraicGeometry.projectiveSpaceOverMap_snd`, so the two
pullbacks compose to the one defining the twist on `ℙⁿ_{S'}`. -/
def twistOverPullbackIso (n : ℕ) {S' S : Scheme.{u}} (g : S' ⟶ S) (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj (twistOver n S d) ≅
      twistOver n S' d :=
  (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n g)
      (projectiveSpaceOver.toIntegralAtUniverse n S)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_snd n g)).app _

/-- **The structure morphism of `ℙⁿ_S` is a base change of the structure morphism of projective
`n`-space over the integers.** The square whose horizontal arrows are the base-change morphism
of projective spaces and the morphism from `S` to the terminal scheme `Spec ℤ`, and whose
vertical arrows are the two structure morphisms, is cartesian. -/
theorem isPullback_structureMorphism_projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) :
    IsPullback (projectiveSpaceOverMap n (specULiftZIsTerminal.from S))
      (projectiveSpaceOver n S ↘ S)
      (projectiveSpaceOverRing n (.of (ULift.{u} ℤ)) ↘ Spec (.of (ULift.{u} ℤ)))
      (specULiftZIsTerminal.from S) :=
  isPullback_projectiveSpaceOverMap n (specULiftZIsTerminal.from S)

/-- **Every twist of the structure sheaf of `ℙⁿ_S` is quasi-coherent**, with no hypothesis on
`S`: the twist is an invertible module, and an invertible module on a scheme is finite locally
free of rank one, hence quasi-coherent. -/
instance isQuasicoherent_twistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    (twistOver n S d).IsQuasicoherent :=
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- **The higher direct images of the twists on projective space vanish outside the relative
dimension.** For the structure morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S`, an
arbitrary `n` and an arbitrary integer `d`, the object `Rᵠ f_* 𝒪(d)` is zero whenever `q < 0` or
`q > n`.

Below degree zero this is the vanishing of any right derived functor in negative degrees. Above
degree `n` the twist is quasi-coherent, the structure morphism of `ℙⁿ_S` is the base change of
the structure morphism of projective `n`-space over the integers, and the higher direct images
of a quasi-coherent module along a base change of that morphism vanish above `n`: the
cohomological dimension of projective space over an affine base is `n`, and conclusion (a) of
[Stacks, Tag 0EX3] carries that bound to every base. -/
@[sga "6 III 2.2.2" "special case", sga "7 XI 1.1" "partial"]
theorem isZero_rightDerivedPlus_pushforward_twistOver
    (n : ℕ) (S : Scheme.{u}) (d : ℤ) (q : ℤ) (hq : q < 0 ∨ (n : ℤ) < q) :
    IsZero (((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).rightDerivedPlus q).obj
      (twistOver n S d)) := by
  rcases hq with hq | hq
  · exact Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj _ q hq _
  · exact
      TopDegreeBaseChangeSituation.isZero_rightDerivedPlus_pushforward_baseChange_projectiveSpace
        n (.of (ULift.{u} ℤ)) (projectiveSpaceOverMap n (specULiftZIsTerminal.from S))
        (projectiveSpaceOver n S ↘ S) (specULiftZIsTerminal.from S)
        (isPullback_structureMorphism_projectiveSpaceOver n S) q hq _

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
