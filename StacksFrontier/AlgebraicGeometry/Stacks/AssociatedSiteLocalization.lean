module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Localization.InheritedTopology
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.Sites.Gerbe.Localization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice

/-!
# Localization of the associated site at an object (Stacks 06W0)

Let `p : 𝒳 ⥤ (Sch/S)` be a category fibred in groupoids over the big fppf category of a
scheme `S` of a big fppf site `B`, and let `x` be an object of `𝒳` lying over a scheme `U`.
Stacks 06W0 says that localizing the associated site of `𝒳` at `x` gives the same site as
the localization of the base at `U`, and that the equivalence is realized by the *canonical*
functor `Over.post` rather than by some unspecified equivalence.

The source states this for each of the Zariski, étale, smooth, syntomic and fppf topologies.
As with `AlgebraicGeometry.Stack.associatedTopology` itself, the argument uses nothing about
which topology is chosen, so both results are stated here once for an arbitrary topology `τ`
on the underlying category of schemes of `B`; the five statements of the source are their
values at the five big topologies. This is a generalization of the source's hypothesis, not a
weakening of its conclusion.

## Main results

* `AlgebraicGeometry.Stack.isEquivalence_overPost`: **Stacks 06W0**, the canonical
  localization functor is an equivalence of categories.
* `AlgebraicGeometry.Stack.inducedTopology_overPost`: **Stacks 06W0**, it identifies the
  localized base topology with the localization of the associated topology.
* `CategoryTheory.Functor.isInheritedTopology_inheritedTopology'`: the inherited topology of a
  fibred functor satisfies `CategoryTheory.Functor.IsInheritedTopology`.

## Implementation notes

The canonical functor is `CategoryTheory.Over.post` applied to `p` followed by the forgetful
functor to the underlying category of schemes. Equality of the *induced* topology with the
localized associated topology is what says that this particular functor is an equivalence of
sites; the proof routes through `CategoryTheory.Functor.IsDenseSubsite` and
`CategoryTheory.Functor.restrictedTopology_eq_inducedTopology_of_isContinuous`.

`CategoryTheory.Functor.isInheritedTopology_inheritedTopology'` shows that the predicate
`CategoryTheory.Functor.IsInheritedTopology` is inhabited, so statements quantifying over an
arbitrary inherited topology may be instantiated at the constructed one.

The instance `HasPullbacks B.Schemes`, needed to apply
`CategoryTheory.Functor.isInheritedTopology_inheritedTopology` to the big fppf site, is derived
from the instance `AlgebraicGeometry.schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan`.

## References

* [Stacks Project, Tag 06W0](https://stacks.math.columbia.edu/tag/06W0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w
universe u' v' w'

namespace CategoryTheory.Functor

/-- The topology a fibred functor inherits from a topology on its base does satisfy
`CategoryTheory.Functor.IsInheritedTopology`: a family of strongly cartesian arrows is
inherited-covering exactly when its image is covering.

This is `CategoryTheory.Functor.isInheritedTopology_inheritedTopology` with the universe of the
index type of the covering families fixed at `max v' w`. -/
theorem isInheritedTopology_inheritedTopology'
    {C : Type u'} [Category.{w'} C] {X : Type v'} [Category.{w} X]
    (q : X ⥤ C) [q.IsFibered] [HasPullbacks C]
    (J : GrothendieckTopology C) :
    IsInheritedTopology.{max v' w} q J (q.inheritedTopology J) :=
  isInheritedTopology_inheritedTopology q J

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

add_to_stacks 06W0 "the canonical localization functor" CategoryTheory.Over.post

/-- Composing a fibred-in-groupoids functor with the forgetful functor to the base scheme
gives a functor fibred in groupoids over the underlying category of schemes. -/
private theorem isFiberedInGroupoids_comp_overForget {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :
    (p ⋙ Over.forget (B.obj hS)).IsFiberedInGroupoids :=
  Functor.IsFiberedInGroupoids.comp p (Over.forget (B.obj hS)) hp
    (Functor.IsFiberedInGroupoids.over_forget (B.obj hS))

/-- **Stacks 06W0.** The canonical localization functor from the slice of a category fibred in
groupoids at an object `x` to the schemes over the scheme `x` lies over is an equivalence of
categories. -/
@[stacks 06W0 "equivalence of categories"]
theorem isEquivalence_overPost {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳) :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
  (isFiberedInGroupoids_comp_overForget B S hS p hp).isEquivalence_overPost x

/-- **Stacks 06W0.** The canonical localization functor identifies the localization at `x` of
the associated topology with the localization of the base topology at the scheme `x` lies
over, so it is an equivalence of sites and not merely of categories. -/
@[stacks 06W0 "equivalence of site topologies"]
theorem inducedTopology_overPost {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (τ : GrothendieckTopology B.Schemes) (x : 𝒳) :
    (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inducedTopology
        (τ.over (p.obj x).left) =
      (associatedTopology B S hS p τ).over x := by
  let q := p ⋙ Over.forget (B.obj hS)
  let J𝒳 := q.inheritedTopology τ
  let F := Over.post (X := x) q
  have hq : q.IsFiberedInGroupoids :=
    isFiberedInGroupoids_comp_overForget B S hS p hp
  have he : F.IsEquivalence := hq.isEquivalence_overPost x
  have hJq : Functor.IsInheritedTopology q τ J𝒳 := by
    let _ : q.IsFibered := hq.isFibered
    change Functor.IsInheritedTopology q τ (q.inheritedTopology τ)
    exact Functor.isInheritedTopology_inheritedTopology q τ
  let _ : F.IsDenseSubsite (J𝒳.over x) (τ.over ((p.obj x).left)) :=
    ⟨inferInstance, inferInstance, inferInstance,
      (Functor.IsInheritedTopology.mem_over_iff_functorPushforward hq hJq _ _).symm⟩
  have hrestricted : F.restrictedTopology (τ.over ((p.obj x).left)) = J𝒳.over x := by
    ext Y T; rw [Functor.mem_restrictedTopology_iff]
    exact Functor.IsDenseSubsite.functorPushforward_mem_iff
  have htop := F.restrictedTopology_eq_inducedTopology_of_isContinuous
    (J := J𝒳.over x) hrestricted
  let _ : p.IsFibered := hp.isFibered
  rw [show J𝒳 = p.inheritedTopology (τ.over (B.obj hS)) from
    Functor.inheritedTopology_comp_overForget' (B.obj hS) p τ] at htop
  simpa [F, J𝒳] using htop

end AlgebraicGeometry.Stack

end
