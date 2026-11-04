module

public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits

/-!
# Testing a property of morphisms of algebraic spaces on scheme-valued points

Let `P` be a property of morphisms of algebraic spaces over `S` which is local on the base for
the fppf topology of Stacks 03YH. A morphism `m : F ⟶ G` of algebraic spaces over `S` has `P` as
soon as every base change of it to a *representable* algebraic space has `P`: a scheme atlas of
`G` is an fppf covering of it (Stacks 025Y and 03Y8,
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas`), and the base change of `m` along that
atlas is one of the base changes assumed to have `P`.

This is the step that turns a statement proved over every scheme into a statement over every
algebraic space, and it is what reduces the right-hand side of Stacks 04XC to the
scheme-valued test in the definition of a relative property.

## Main results

* `AlgebraicGeometry.Space.prop_homMk_of_forall_yoneda`: the test above.

## Implementation notes

The two fibre products involved are the same: the base change of `m` along the atlas is the
presheaf fibre product `yoneda.obj T ×_G F`, which is cartesian in the category of algebraic
spaces by Stacks 02X2
(`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`), while
`AlgebraicGeometry.Space.prop_iff_pullbackSnd_atlas` is stated for the chosen pullback of that
category. The comparison is `CategoryTheory.IsPullback.isoPullback`, and `P` respects it because
a property local on the base respects isomorphisms.

The index universe of the fppf precoverage is free, so a consumer instantiates it at whatever
universe its locality hypothesis was stated at.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A property of morphisms of algebraic spaces local on the base for the fppf topology may be
tested on representable base changes.** If every base change of `m : F ⟶ G` to a representable
algebraic space has `P`, then `m` has `P`: apply the hypothesis to a scheme atlas of `G`, which
is an fppf covering of it. -/
theorem prop_homMk_of_forall_yoneda
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsLocalAtTarget (Topology.fppf.precoverage.{u, v} B S hS)]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (m : F ⟶ G)
    (hpoint : ∀ (V : BigFppfOver B S hS) (v : yoneda.obj V ⟶ G),
      P (ObjectProperty.homMk (pullback.fst v m) :
        (⟨pullback v m, isAlgebraicSpace_pullback B S hS v m
            (isAlgebraicSpace_yoneda B S hS V) hF hG⟩ : AlgebraicSpaces B S hS) ⟶
          (⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩ : AlgebraicSpaces B S hS))) :
    P (ObjectProperty.homMk m : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) := by
  obtain ⟨T, a, hsurj, hetale⟩ := hG.exists_atlas
  rw [prop_iff_pullbackSnd_atlas.{u, v} B S hS P
    (ObjectProperty.homMk m : (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩) hsurj hetale]
  have hpb := (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk a :
      (⟨yoneda.obj T, isAlgebraicSpace_yoneda B S hS T⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)
    (ObjectProperty.homMk m :
      (⟨F, hF⟩ : AlgebraicSpaces B S hS) ⟶ ⟨G, hG⟩)).flip
  refine (P.cancel_left_of_respectsIso hpb.isoPullback.hom _).mp ?_
  rw [hpb.isoPullback_hom_snd]
  exact hpoint T a

end AlgebraicGeometry.Space

end
