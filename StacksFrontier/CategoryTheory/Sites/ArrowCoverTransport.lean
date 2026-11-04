module

public import Mathlib.CategoryTheory.Functor.Flat
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.MorphismsOfSites
public import StacksCore.Tactic.StacksAttribute

/-!
# Transport of coverings by a family of arrows along a morphism of sites

Let `u : C ⥤ D` be a continuous functor of sites, so that it defines a morphism of sites
`D → C` in the sense of [Stacks, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1). Two
statements are needed when one wants to push a covering *written as a family of arrows*
`{V i → Y}` forward to a covering `{u (V i) → u Y}`, and they are what the pullback arguments of
[Stacks, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO) and
[Stacks, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) use:

* the covering of the final object by the images `u U` (Stacks 08H2), and
* the image of a covering family of arrows is a covering family of arrows.

The first is already available as
`CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback`, which
asks for the sheaf pullback to preserve the terminal object; the form wanted at a morphism of
sites is the one that asks it to be left exact, and `coversTop_obj_of_preservesFiniteLimits`
below is that adapter.

The second is the content of this file. Mathlib has `CategoryTheory.CoverPreserving`, phrased
with `Sieve.functorPushforward`, and `CategoryTheory.Sieve.functorPushforward_ofArrows`
identifying the pushforward of `Sieve.ofArrows` — but not the combination, which is what a
consumer holding a covering family has.

## Main results

* `Stacks.Sites.coversTop_obj_of_preservesFiniteLimits`: the images `u U` cover the final
  object when the sheaf pullback along `u` is left exact.
* `Stacks.Sites.ofArrows_image_mem`: **the image of a covering family of arrows under a left
  exact continuous functor is a covering family of arrows.** A left exact functor out of a
  category with finite limits is representably flat, so for it continuity is equivalent to
  cover-preservation, and the pushforward of `Sieve.ofArrows V g` is `Sieve.ofArrows` of the
  images.

## Implementation notes

Both statements are about a bare functor between sites together with explicit hypotheses, not
about a bundled morphism of ringed sites: nothing here mentions a structure sheaf, and the
hypotheses are exactly the ones used. `ofArrows_image_mem` needs finite limits only in the
*source* `C`, since that is all `CategoryTheory.flat_of_preservesFiniteLimits` asks for; the
index type `I` is at an arbitrary universe, and the site universes are independent.

No `@[stacks]` attribute is placed here. `coversTop_obj_of_preservesFiniteLimits` is a weakening
of the hypotheses of the already-tagged Stacks 08H2 statement rather than a second proof of it,
and `ofArrows_image_mem` is an unlabelled step inside the proofs of Stacks 03DL and 03DO rather
than a numbered result.

## References

* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
* [Stacks Project, Tag 08H2](https://stacks.math.columbia.edu/tag/08H2)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public section

open CategoryTheory Limits

universe w v' v u' u

namespace Stacks.Sites

/-- If the sheaf pullback along a continuous functor `u : C ⥤ D` is left exact — which is what
`u` defining a morphism of sites gives — then the images `u U` cover the final object of
`Sh(D)`. This is `CategoryTheory.GrothendieckTopology
.coversTop_obj_of_preservesTerminal_sheafPullback` (Stacks 08H2) with the hypothesis in the form
a morphism of sites supplies. -/
theorem coversTop_obj_of_preservesFiniteLimits {C : Type u} [SmallCategory C] {D : Type u}
    [SmallCategory D] (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [PreservesFiniteLimits (u.sheafPullback (Type u) J K)] :
    K.CoversTop u.obj :=
  CategoryTheory.GrothendieckTopology.coversTop_obj_of_preservesTerminal_sheafPullback u J K

/-- **The image of a covering family of arrows is a covering family of arrows.** If `u : C ⥤ D`
is continuous and left exact and `C` has finite limits, then `u` carries a covering family
`{V i ⟶ Y}` of `J` to a covering family `{u (V i) ⟶ u Y}` of `K`. -/
theorem ofArrows_image_mem {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K] [HasFiniteLimits C] [PreservesFiniteLimits u]
    {I : Type w} (V : I → C) (Y : C) (g : ∀ i, V i ⟶ Y)
    (hg : Sieve.ofArrows V g ∈ J Y) :
    Sieve.ofArrows (fun i => u.obj (V i)) (fun i => u.map (g i)) ∈ K (u.obj Y) := by
  let _ : RepresentablyFlat u := flat_of_preservesFiniteLimits u
  have hcp : CoverPreserving J K u :=
    (Functor.isContinuous_iff_coverPreserving (F := u) (J := J) (K := K)).mp inferInstance
  have h := hcp.cover_preserve hg
  rwa [Sieve.functorPushforward_ofArrows] at h

end Stacks.Sites

end
