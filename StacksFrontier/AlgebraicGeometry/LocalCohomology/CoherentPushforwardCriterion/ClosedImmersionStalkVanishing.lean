module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.ClosedImmersionPushforward
/-!
# Scheme-level vanishing of the stalks of a closed direct image off its image

Let `i : Z ⟶ X` be a closed immersion of schemes and `M` an `𝒪_Z`-module. At a point of `X`
outside the image of `i` the stalk of `i_* M` vanishes. This is [Stacks, Tag 00AE], and it is
already proved in the tree — but only for ringed spaces, as
`Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange`, whose subject is
`RingedSpaceModuleAdjunction.modulePushforward`. This file carries it across to Mathlib's
`AlgebraicGeometry.Scheme.Modules.pushforward`, which is the spelling every scheme-level
consumer uses.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pushforward_eq_modulePushforward`: the two direct-image
  functors are *equal*, not merely isomorphic.
* `AlgebraicGeometry.isZero_stalkFunctor_pushforward_of_notMemRange`: the ringed-space
  vanishing, restated for `Scheme.Modules.pushforward`.
* `AlgebraicGeometry.subsingleton_stalk_pushforward_of_notMemRange`: the same vanishing in the
  form the `X.Modules` API presents stalks in, namely as the stalk of the underlying presheaf
  of abelian groups.

## Implementation notes

`Scheme.Modules.pushforward f` is `SheafOfModules.pushforward f.toRingCatSheafHom` and
`RingedSpaceModuleAdjunction.modulePushforward g` is
`SheafOfModules.pushforward (structureSheafHom g)`. For `g = f.toLRSHom.toShHom` the two
morphisms of sheaves of rings are both `Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)`,
and `X.ringCatSheaf` and `structureSheafRing X.toRingedSpace` are both
`(sheafCompose _ (forget₂ CommRingCat RingCat)).obj X.sheaf`; so the bridge is `rfl`. It is
*not* `rfl` at reducible transparency, which is why instance search and `exact?` do not cross
the boundary on their own and a named lemma earns its place — the same observation is recorded
at `StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative`, which crosses it
for right exactness.

The third statement is `Subsingleton` rather than `IsZero` because `Stacks.Divisors`' associated
points read the stalk through `TopCat.Presheaf.stalk (C := Ab) F.val.presheaf x`, an abelian
group with no ambient zero object in scope at the point of use; subsingleton-ness is what the
annihilator argument there actually consumes.

## References

* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

/-- **Direct image of sheaves of modules along a morphism of schemes is the ringed-space direct
image.** Mathlib's `AlgebraicGeometry.Scheme.Modules.pushforward f` and the tree's
`RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom` are the same functor: both
are `SheafOfModules.pushforward` of `Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)`,
between the same two categories. -/
theorem Scheme.Modules.pushforward_eq_modulePushforward {Z X : Scheme.{u}} (i : Z ⟶ X) :
    Scheme.Modules.pushforward i
      = modulePushforward (X := Z.toLocallyRingedSpace.toRingedSpace)
          (Y := X.toLocallyRingedSpace.toRingedSpace) i.toLRSHom.toShHom :=
  rfl

/-- **[Stacks, Tag 00AE] for `Scheme.Modules.pushforward`.** At a point of `X` outside the image
of a closed immersion `i : Z ⟶ X`, the stalk of `i_* M` is a zero module over `𝒪_{X,x}`.

This is `Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange` carried across
`Scheme.Modules.pushforward_eq_modulePushforward`. -/
theorem isZero_stalkFunctor_pushforward_of_notMemRange {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding (ConcreteCategory.hom i.base)) (M : Z.Modules) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.base)) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf x).obj
      ((Scheme.Modules.pushforward i).obj M)) :=
  Stacks.ClosedImmersion.isZero_stalk_modulePushforward_of_notMemRange
    (Z := Z.toLocallyRingedSpace.toRingedSpace) (X := X.toLocallyRingedSpace.toRingedSpace)
    i.toLRSHom.toShHom hi M x hx

/-- **[Stacks, Tag 00AE] on the underlying abelian presheaf.** At a point of `X` outside the
image of a closed immersion `i : Z ⟶ X`, the stalk of the abelian sheaf underlying `i_* M` has
at most one element.

This is the shape consumed by the associated-point API, which reads stalks as
`TopCat.Presheaf.stalk (C := Ab) F.val.presheaf x`. -/
theorem subsingleton_stalk_pushforward_of_notMemRange {Z X : Scheme.{u}} (i : Z ⟶ X)
    (hi : Topology.IsClosedEmbedding (ConcreteCategory.hom i.base)) (M : Z.Modules) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.base)) :
    Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward i).obj M).val.presheaf x) :=
  ModuleCat.subsingleton_of_isZero (isZero_stalkFunctor_pushforward_of_notMemRange i hi M x hx)

/-- **[Stacks, Tag 00AE] for a closed immersion, with the embedding found by instances.** The
form of `subsingleton_stalk_pushforward_of_notMemRange` that takes `IsClosedImmersion i` rather
than a bare closed embedding of the underlying spaces. -/
theorem subsingleton_stalk_pushforward_of_notMemRange' {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (M : Z.Modules) (x : X)
    (hx : x ∉ Set.range (ConcreteCategory.hom i.base)) :
    Subsingleton (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward i).obj M).val.presheaf x) :=
  subsingleton_stalk_pushforward_of_notMemRange i (IsClosedImmersion.isClosedEmbedding i) M x hx

end AlgebraicGeometry

end
