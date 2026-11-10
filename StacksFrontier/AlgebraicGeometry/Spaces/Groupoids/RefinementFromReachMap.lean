module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationQuasiFiniteRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RefinementSiteData

/-!
# A refinement of a groupoid scheme from its reach map

`Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` is stated for an arbitrary site
presented by a functor `F : C ⥤ Over S`, and asks for the reach map as a morphism of that
site: two objects of `C` presenting its source and its target, isomorphisms identifying them,
the morphism of `C` itself, and the covering clause.  For the big fppf site of a scheme all of
that is determined by the size estimates of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/RefinementSiteData.lean` together with
fullness of `Over.post B.inclusion`, so a refinement may be built from purely scheme-level
data: the properties of the reach map `h = pullback.snd g t ≫ s` *in the category of schemes*.

This module is that construction.  It is the bridge between the shape in which
[Stacks Project, Tag 04N0] and the reach-map results of
`StacksFrontier/AlgebraicGeometry/Groupoids/Slicing/ReachMapCoproduct.lean` state the properties
of `h` -- a morphism of schemes out of `pullback g.left G.target.left` -- and the shape
`QuasiFiniteRefinement` records, a morphism of `Over S` out of the fibre product
`pullback g G.target` formed in `Over S`.  The comparison is
`AlgebraicGeometry.overFibreProduct_isPullback`: the underlying square of schemes of the fibre
product of `Over S` is cartesian, so its vertex is canonically isomorphic to the fibre product
of schemes, compatibly with the projections.

## Main definitions

* `AlgebraicGeometry.reachSourceIso`: the comparison of the two fibre products.
* `AlgebraicGeometry.quasiFiniteRefinementOfReachMap`: the refinement of a groupoid scheme
  determined by a morphism `g : U' ⟶ U` whose reach map, as a morphism of schemes, is flat,
  locally of finite presentation, locally quasi-finite and surjective, given that `U`, `U'`
  and the arrow scheme belong to the site.

## Main results

* `AlgebraicGeometry.restrictionReachMap_left_mem`: every property of morphisms of schemes
  which respects isomorphisms passes from the reach map of schemes to the reach map of
  `Over S`.
* `AlgebraicGeometry.contains_reachSource`: the source of the reach map belongs to the site
  when the restricting scheme and the arrow scheme do.

## Implementation notes

The morphism of the site underlying the reach map is produced by fullness of
`Over.post B.inclusion`, which is full because the inclusion of the bounded subcategory of
schemes is fully faithful.  `siteSource` and `siteTarget` are *chosen* to be
`AlgebraicGeometry.siteObject` on the source and target of the reach map, whose images under
`Over.post B.inclusion` are those two `S`-schemes on the nose, so the two comparison
isomorphisms are `Iso.refl` and the morphism to lift is the reach map itself.

The covering clause is `AlgebraicGeometry.Space.singleton_mem_bigFppfOver_topology_of_flat`,
and the surjectivity, flatness and local finite presentation it consumes are read off the
scheme-level reach map through the comparison isomorphism.

## References

* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The comparison of the fibre product of `Over S` defining the source of the reach map with
the fibre product of schemes. -/
noncomputable def reachSourceIso {S : Scheme.{u}} {G : GroupoidScheme S} {U' : Over S}
    (g : U' ⟶ G.objects) :
    (pullback g G.target).left ≅ pullback g.left G.target.left :=
  (overFibreProduct_isPullback g G.target).isoPullback

/-- The reach map of `Over S`, read through `AlgebraicGeometry.reachSourceIso`, is the reach
map of schemes. -/
theorem reachSourceIso_hom_comp {S : Scheme.{u}} {G : GroupoidScheme S} {U' : Over S}
    (g : U' ⟶ G.objects) :
    (reachSourceIso g).hom ≫ pullback.snd g.left G.target.left ≫ G.source.left =
      (GroupoidScheme.restrictionReachMap G g).left := by
  rw [← Category.assoc, reachSourceIso, IsPullback.isoPullback_hom_snd]
  rfl

/-- Every property of morphisms of schemes which respects isomorphisms passes from the reach
map of schemes to the reach map of `Over S`. -/
theorem restrictionReachMap_left_mem {S : Scheme.{u}} {G : GroupoidScheme S} {U' : Over S}
    (g : U' ⟶ G.objects) (P : MorphismProperty Scheme.{u}) (hP : P.RespectsIso)
    (h : P (pullback.snd g.left G.target.left ≫ G.source.left)) :
    P (GroupoidScheme.restrictionReachMap G g).left := by
  have _ := hP
  rw [← reachSourceIso_hom_comp g]
  exact (MorphismProperty.cancel_left_of_respectsIso (P := P) (reachSourceIso g).hom _).2 h

/-- The source of the reach map belongs to the site as soon as the restricting scheme and the
arrow scheme do. -/
theorem contains_reachSource (B : BigFppfSite.{u}) {S : Scheme.{u}} {G : GroupoidScheme S}
    {U' : Over S} (g : U' ⟶ G.objects) (hU' : B.Contains U'.left)
    (hR : B.Contains G.arrows.left) : B.Contains (pullback g G.target).left := by
  change (pullback g G.target).left.size < B.cutoff
  rw [Scheme.size_congr (reachSourceIso g)]
  exact Scheme.size_pullback_lt _ _ hU' hR

/-- **The refinement of a groupoid scheme determined by the properties of its reach map.**

Let `G` be a groupoid scheme over a scheme `S` of a big fppf site `B`, and let `g : U' ⟶ U` be
a morphism of `S`-schemes to its object scheme whose reach map
`h = pullback.snd g t ≫ s`, taken in the category of schemes, is flat, locally of finite
presentation, locally quasi-finite and surjective.  If `U`, `U'` and the arrow scheme of `G`
all belong to `B`, then `g` is a
`Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` of `G` for the big fppf site over `S`.

This is Step 3 of the proof of [Stacks Project, Tag 0489] packaged: the three geometric
properties are the output of [Stacks Project, Tag 04N0] carried along
`AlgebraicGeometry.reachMap_sigmaDesc_mem`, the surjectivity is
`AlgebraicGeometry.surjective_reachMap_sigmaDesc_of_finiteTypePoints`, and the site-theoretic
data is the footnote. -/
noncomputable def quasiFiniteRefinementOfReachMap (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {G : GroupoidScheme S} {U' : Over S} (g : U' ⟶ G.objects)
    (hU : B.Contains G.objects.left) (hU' : B.Contains U'.left)
    (hR : B.Contains G.arrows.left)
    (hflat : Flat (pullback.snd g.left G.target.left ≫ G.source.left))
    (hlfp : LocallyOfFinitePresentation (pullback.snd g.left G.target.left ≫ G.source.left))
    (hlqf : LocallyQuasiFinite (pullback.snd g.left G.target.left ≫ G.source.left))
    (hsurj : Surjective (pullback.snd g.left G.target.left ≫ G.source.left)) :
    GroupoidScheme.QuasiFiniteRefinement (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) G := by
  classical
  have hri : ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange → P.RespectsIso :=
    fun _ h => h.respectsIso
  have hflat' : Flat (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hflat
  have hlfp' : LocallyOfFinitePresentation
      (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hlfp
  have hlqf' : LocallyQuasiFinite (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hlqf
  have hsurj' : Surjective (GroupoidScheme.restrictionReachMap G g).left :=
    restrictionReachMap_left_mem g _ (hri _ inferInstance) hsurj
  have hP : B.Contains (pullback g G.target).left := contains_reachSource B g hU' hR
  have hmap : ∃ a : siteObject B S hS hP (pullback g G.target).hom ⟶
      siteObject B S hS hU G.objects.hom,
      (Over.post (X := B.obj hS) B.inclusion).map a =
        GroupoidScheme.restrictionReachMap G g :=
    (Over.post (X := B.obj hS) B.inclusion).map_surjective _
  have ha := hmap.choose_spec
  have hleft : (BigFppfOver.toScheme B S hS).map hmap.choose =
      (GroupoidScheme.restrictionReachMap G g).left :=
    congrArg Over.Hom.left ha
  refine ⟨U', g, hflat', hlfp', hlqf', _, _, Iso.refl _, Iso.refl _, hmap.choose, ?_, ?_⟩
  · exact (Category.comp_id _).trans (ha.trans (Category.id_comp _).symm)
  · refine Space.singleton_mem_bigFppfOver_topology_of_flat B S hS hmap.choose ?_ ?_ ?_
    · rw [hleft]; exact hsurj'
    · rw [hleft]; exact hflat'
    · rw [hleft]; exact hlfp'

end AlgebraicGeometry

end
