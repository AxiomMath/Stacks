module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation

/-!
# The summands of the graph relation of a group action

The scheme of arrows of the graph relation of a group `G` acting on an object `V` of a big
fppf site over `S` is the disjoint union of one copy of `V` for each element of `G`
(**Stacks 02Z2**). This file records the inclusions of those summands as morphisms of the
site, together with their composites with the source and target maps of the relation: the
summand indexed by `g` is a section of the source map and is carried by the target map to
the automorphism `g` acts by.

These are the morphisms which exhibit two points of `V` lying in one `G`-orbit as the images
of a single point of the relation scheme, and so as a single point of the quotient.

## Main definitions

* `AlgebraicGeometry.Space.siteActionRelationInclusion` is the inclusion of the summand of
  the relation scheme indexed by a group element.

## Main results

* `AlgebraicGeometry.Space.siteActionRelationInclusion_comp_source`: every summand is a
  section of the source map.
* `AlgebraicGeometry.Space.toScheme_map_siteActionRelationInclusion_comp_target`: the target
  map restricted to the summand indexed by `g` is the automorphism `g` acts by.

## Implementation notes

The target composite is stated for the underlying morphism of schemes rather than inside the
site. That is the form its consumers need — they move a point of the underlying scheme of
`V` along the action — and it avoids naming the site morphism underlying `(a g).asIso.hom.left`,
which only exists as a preimage under the fully faithful inclusion of the site.

## References

* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}} (G : Type v) [Group G] [Small.{u} G] (B : BigFppfSite.{u})
  (hS : B.Contains S) (V : BigFppfOver B S hS)
  (hR : B.Contains (actionRelationScheme (underlyingOver B hS V) G).left)

/-- **Stacks 02Z2.** The inclusion of the summand indexed by `g` into the scheme of arrows
of the graph relation of a group action, as a morphism of the big fppf site. -/
def siteActionRelationInclusion (g : G) : V ⟶ siteActionRelationScheme G B hS V hR :=
  Over.homMk (ObjectProperty.homMk (Sigma.ι (fun _ : G ↦ underlyingOver B hS V) g).left)
    (ObjectProperty.hom_ext _ (Sigma.ι (fun _ : G ↦ underlyingOver B hS V) g).w)

omit [Group G] in
/-- Every summand of the graph relation of a group action is a section of the source map:
the source map is the identity on each copy. -/
theorem siteActionRelationInclusion_comp_source (g : G) :
    siteActionRelationInclusion G B hS V hR g ≫ siteActionRelationSource G B hS V hR =
      𝟙 V := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change (Over.forget S).map (Sigma.ι (fun _ : G ↦ underlyingOver B hS V) g) ≫
      (Over.forget S).map (Sigma.desc fun _ : G ↦ 𝟙 (underlyingOver B hS V)) =
    (Over.forget S).map (𝟙 (underlyingOver B hS V))
  rw [← Functor.map_comp, Sigma.ι_desc]

/-- The target map of the graph relation of a group action, restricted to the summand indexed
by `g`, is the automorphism that `g` acts by. -/
theorem toScheme_map_siteActionRelationInclusion_comp_target
    (a : G →* Aut (underlyingOver B hS V)) (g : G) :
    (BigFppfOver.toScheme B S hS).map (siteActionRelationInclusion G B hS V hR g ≫
        siteActionRelationTarget G B hS V hR a) =
      (a g).asIso.hom.left := by
  rw [Functor.map_comp]
  change (Sigma.ι (fun _ : G ↦ underlyingOver B hS V) g).left ≫
    (actionRelationTarget (underlyingOver B hS V) G a).left = (a g).asIso.hom.left
  rw [← Over.comp_left, actionRelationTarget, Sigma.ι_desc]

end AlgebraicGeometry.Space

end
