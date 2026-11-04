module

public import StacksFrontier.AlgebraicGeometry.Groupoids.More.CoproductRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivalenceRelationQuasiFiniteRefinement

/-!
# Step 3 of the proof of Stacks 0489, with the coproduct carried in the site

Step 3 of the proof of Stacks 0489 refines an equivalence relation by restricting the groupoid
along the coproduct `∐_u g_u` of the affine slices which Stacks 04N0 attaches to the finite type
points `u` of the object scheme `U`.  Two things have to be said about that coproduct: what its
reach map is, and that it is an object of the site.

The first is
`AlgebraicGeometry.GroupoidScheme.nonempty_isColimit_cofanMk_sigmaRestrictionReachι`: the source
of the reach map of `∐_u g_u` is the coproduct of the sources of the reach maps of the members,
so the reach map of the coproduct is the coproduct `∐_u h_u` of theirs, is flat, locally of
finite presentation and locally quasi-finite because each `h_u` is, and is surjective because
the `h_u` are jointly surjective.

The second is what the source secures by the size estimate of its footnote, and what this file
carries as data.  The convention is that of Stacks 04SK
(`AlgebraicGeometry.isAlgebraicSpace_of_isCovering`) and Stacks 02WQ
(`AlgebraicGeometry.isAlgebraicSpace_coproduct`): a coproduct which cannot be formed inside the
site is carried as an object of the site together with a cofan exhibiting it as the coproduct.
Here the objects to be coproduced are the sources `U'_u ×_{g_u, U, t} R` of the reach maps of
the members, since it is their coproduct that carries the covering morphism; the datum is an
object `siteSource` of the site, a cofan of site morphisms into it, and the statement that the
site functor takes that cofan to a coproduct in `Over S`.

Everything else is then derived.  The reach map of the coproduct, read in the site, is the
morphism out of the coproduct determined by the reach maps of the members, and it generates a
covering sieve because it is flat, locally of finite presentation and surjective: that last
implication is the only property of the topology used, and it is asked of `J` as the hypothesis
`hJ`, which for a big fppf site is
`AlgebraicGeometry.sieve_generate_singleton_mem_topology_over_of_flat`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.CoproductRefinement`: the output of Step 3 of the proof of
  **Stacks 0489** — a family of morphisms to the object scheme whose reach maps are flat,
  locally of finite presentation and locally quasi-finite and whose images contain the finite
  type points, together with the coproduct of the sources of those reach maps taken inside the
  site.
* `Stacks.Groupoids.GroupoidScheme.CoproductRefinement.cover`: the reach map of the coproduct,
  read as a morphism of the site.

## Main results

* `Stacks.Groupoids.GroupoidScheme.CoproductRefinement.quasiFiniteRefinement`: such a datum is
  a `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement`, so it discharges the hypothesis of
  `Stacks.Groupoids.GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap`.

## Implementation notes

The index type of the family is a parameter of the structure rather than a field, so that the
`CategoryTheory.Limits.Small` hypothesis which the coproduct of schemes needs can be an
instance argument.

The identification of `siteSource` with the source of the reach map of the coproduct is not
carried: it is the comparison of two coproducts of the same family, the one the site datum
provides and the one
`AlgebraicGeometry.GroupoidScheme.nonempty_isColimit_cofanMk_sigmaRestrictionReachι` provides,
and is therefore constructed, as
`Stacks.Groupoids.GroupoidScheme.CoproductRefinement.siteSourceIso`.

The three properties of the covering morphism are read off the reach map of the coproduct
through that identification, which is an isomorphism of `Over S` and hence of schemes on
underlying objects; `Stacks.Groupoids.GroupoidScheme.CoproductRefinement.map_cover_mem`
transfers any property stable under base change across it.

That the hypothesis `hJ` is satisfiable is recorded by
`Stacks.Groupoids.GroupoidScheme.bigFppfOver_generate_singleton_mem_topology`, which is it for
the big fppf site over `S` presented by `CategoryTheory.Over.post`.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidScheme

universe u v w t

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- **The output of Step 3 of the proof of Stacks 0489.**

A family of morphisms `g i : U'_i ⟶ U` to the object scheme of a groupoid scheme whose reach
maps `h i : U'_i ×_{g i, U, t} R ⟶ U` are flat, locally of finite presentation and locally
quasi-finite and have images containing every finite type point of `U`, together with the
coproduct of the sources of those reach maps taken *inside the site*: an object `siteSource`
of the site, site morphisms from objects
`sliceReachSource i` presenting the `U'_i ×_{g i, U, t} R` into it, and the statement that the
site functor takes the resulting cofan to a coproduct in `Over S`.

In the source the family is indexed by the finite type points of `U` and `g u` is the affine
slice at `u` produced by Stacks 04N0, whose reach map is flat, locally of finite presentation
and locally quasi-finite and whose image contains `u`; and the coproduct is an object of the
site by the size estimate of the footnote, which is what carrying it as data stands in for.
This is the convention of Stacks 04SK and Stacks 02WQ. -/
structure CoproductRefinement (J : GrothendieckTopology C) (F : C ⥤ Over S)
    (G : GroupoidScheme S) (ι : Type t) [Small.{u} ι] where
  /-- The members `U'_i` of the family. -/
  slice : ι → Over S
  /-- The morphisms `g i : U'_i ⟶ U`. -/
  sliceMap : ∀ i, slice i ⟶ G.objects
  /-- Each reach map `h i` is flat. -/
  reach_flat : ∀ i, Flat (restrictionReachMap G (sliceMap i)).left
  /-- Each reach map is locally of finite presentation. -/
  reach_locallyOfFinitePresentation : ∀ i,
    LocallyOfFinitePresentation (restrictionReachMap G (sliceMap i)).left
  /-- Each reach map is locally quasi-finite. -/
  reach_locallyQuasiFinite : ∀ i,
    LocallyQuasiFinite (restrictionReachMap G (sliceMap i)).left
  /-- Every finite type point of `U` is in the image of one of the reach maps.  In the source
  the family is indexed by the finite type points of `U` and the image of `h u` contains `u`.
  The reach maps are then jointly surjective, by
  `AlgebraicGeometry.jointlySurjective_of_isFiniteTypePoint`, because they are flat and locally
  of finite presentation and hence have open images. -/
  reach_mem_range_of_isFiniteTypePoint : ∀ y : G.objects.left, IsFiniteTypePoint y →
    ∃ i, y ∈ Set.range (restrictionReachMap G (sliceMap i)).left
  /-- An object of the site presenting the object scheme `U`. -/
  siteTarget : C
  /-- The identification of `siteTarget` with `U`. -/
  siteTargetIso : F.obj siteTarget ≅ G.objects
  /-- Objects of the site presenting the sources `U'_i ×_{g i, U, t} R` of the reach maps. -/
  sliceReachSource : ι → C
  /-- Their identifications with those sources. -/
  sliceReachSourceIso : ∀ i, F.obj (sliceReachSource i) ≅ pullback (sliceMap i) G.target
  /-- The coproduct of the sources of the reach maps, as an object of the site. -/
  siteSource : C
  /-- Its coproduct injections, as morphisms of the site. -/
  siteSourceι : ∀ i, sliceReachSource i ⟶ siteSource
  /-- They exhibit `siteSource` as the coproduct in the site. -/
  siteSource_isColimit : IsColimit (Cofan.mk siteSource siteSourceι)
  /-- The site functor takes that cofan to a coproduct of `S`-schemes. -/
  siteSource_mapIsColimit : IsColimit (Cofan.mk (F.obj siteSource)
    fun i => (sliceReachSourceIso i).inv ≫ F.map (siteSourceι i))
  /-- The reach maps of the members, as morphisms of the site. -/
  siteReach : ∀ i, sliceReachSource i ⟶ siteTarget
  /-- They are the reach maps under the identifications. -/
  siteReach_spec : ∀ i, F.map (siteReach i) ≫ siteTargetIso.hom =
    (sliceReachSourceIso i).hom ≫ restrictionReachMap G (sliceMap i)

namespace CoproductRefinement

variable {J : GrothendieckTopology C} {F : C ⥤ Over S} {G : GroupoidScheme S} {ι : Type t}
  [Small.{u} ι] (D : CoproductRefinement J F G ι)

/-- The reach map of the coproduct, read as a morphism of the site: the morphism out of the
coproduct in the site determined by the reach maps of the members. -/
noncomputable def cover : D.siteSource ⟶ D.siteTarget :=
  D.siteSource_isColimit.desc (Cofan.mk D.siteTarget D.siteReach)

/-- The morphism `cover` restricts along the `i`-th coproduct injection to the reach map of the
`i`-th member. -/
@[reassoc (attr := simp)]
lemma siteSourceι_cover (i : ι) : D.siteSourceι i ≫ D.cover = D.siteReach i :=
  D.siteSource_isColimit.fac (Cofan.mk D.siteTarget D.siteReach) ⟨i⟩

/-- The identification of `siteSource` with the source of the reach map of the coproduct: both
are coproducts of the sources of the reach maps of the members. -/
noncomputable def siteSourceIso :
    F.obj D.siteSource ≅ pullback (sigmaOverDesc D.sliceMap) G.target :=
  D.siteSource_mapIsColimit.coconePointUniqueUpToIso
    (nonempty_isColimit_cofanMk_sigmaRestrictionReachι G D.sliceMap).some

/-- Under `siteSourceIso`, the image of the `i`-th coproduct injection of the site is the `i`-th
coproduct injection `sigmaRestrictionReachι`. -/
lemma inj_siteSourceIso_hom (i : ι) :
    ((D.sliceReachSourceIso i).inv ≫ F.map (D.siteSourceι i)) ≫ D.siteSourceIso.hom =
      sigmaRestrictionReachι G D.sliceMap i :=
  D.siteSource_mapIsColimit.comp_coconePointUniqueUpToIso_hom
    (nonempty_isColimit_cofanMk_sigmaRestrictionReachι G D.sliceMap).some ⟨i⟩

/-- The morphism of the site is the reach map of the coproduct under the two
identifications. -/
theorem cover_spec : F.map D.cover ≫ D.siteTargetIso.hom =
    D.siteSourceIso.hom ≫ restrictionReachMap G (sigmaOverDesc D.sliceMap) := by
  refine D.siteSource_mapIsColimit.hom_ext fun ⟨i⟩ => ?_
  have hL : ((D.sliceReachSourceIso i).inv ≫ F.map (D.siteSourceι i)) ≫
      F.map D.cover ≫ D.siteTargetIso.hom = restrictionReachMap G (D.sliceMap i) := by
    rw [Category.assoc, ← Category.assoc (F.map (D.siteSourceι i)), ← F.map_comp,
      D.siteSourceι_cover i, D.siteReach_spec i, Iso.inv_hom_id_assoc]
  have hR : ((D.sliceReachSourceIso i).inv ≫ F.map (D.siteSourceι i)) ≫
      D.siteSourceIso.hom ≫ restrictionReachMap G (sigmaOverDesc D.sliceMap) =
      restrictionReachMap G (D.sliceMap i) := by
    rw [← Category.assoc, D.inj_siteSourceIso_hom i, sigmaRestrictionReachι_comp_reach]
  exact hL.trans hR.symm

/-- The morphism of the site, read as a morphism of `S`-schemes, is the reach map of the
coproduct conjugated by the two identifications. -/
theorem map_cover_eq : F.map D.cover =
    D.siteSourceIso.hom ≫ restrictionReachMap G (sigmaOverDesc D.sliceMap) ≫
      D.siteTargetIso.inv := by
  rw [← Category.assoc, ← D.cover_spec, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A property of morphisms of schemes which is stable under base change, hence respects
isomorphisms, and holds for the reach map of the coproduct holds for the covering morphism of
the site. -/
theorem map_cover_mem {P : MorphismProperty Scheme.{u}} [P.IsStableUnderBaseChange]
    (h : P (restrictionReachMap G (sigmaOverDesc D.sliceMap)).left) : P (F.map D.cover).left := by
  have : IsIso D.siteSourceIso.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map D.siteSourceIso.hom))
  have : IsIso D.siteTargetIso.inv.left :=
    inferInstanceAs (IsIso ((Over.forget S).map D.siteTargetIso.inv))
  rw [D.map_cover_eq, Over.comp_left, Over.comp_left, P.cancel_left_of_respectsIso,
    P.cancel_right_of_respectsIso]
  exact h

/-- The covering morphism of the site is flat. -/
theorem flat_map_cover : Flat (F.map D.cover).left :=
  D.map_cover_mem (reach_sigmaOverDesc_flat G D.sliceMap D.reach_flat)

/-- The covering morphism of the site is locally of finite presentation. -/
theorem locallyOfFinitePresentation_map_cover :
    LocallyOfFinitePresentation (F.map D.cover).left :=
  D.map_cover_mem
    (reach_sigmaOverDesc_locallyOfFinitePresentation G D.sliceMap
      D.reach_locallyOfFinitePresentation)

/-- The covering morphism of the site is surjective. -/
theorem surjective_map_cover : Surjective (F.map D.cover).left :=
  D.map_cover_mem (surjective_reach_sigmaOverDesc_of_isFiniteTypePoint G D.sliceMap
    D.reach_flat D.reach_locallyOfFinitePresentation D.reach_mem_range_of_isFiniteTypePoint)

/-- **Step 3 of the proof of Stacks 0489 produces the refinement.**

The coproduct of the family, with the morphism to the object scheme glued from the members, is
a refinement in the sense of `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement`: its reach
map is flat, locally of finite presentation and locally quasi-finite because the reach maps of
the members are, and the morphism of the site out of the carried coproduct is a singleton
covering because that reach map is flat, locally of finite presentation and surjective.

The hypothesis `hJ` is the only property of the topology that is used: a morphism of the site
which is flat, locally of finite presentation and surjective as a morphism of schemes generates
a covering sieve.  For a big fppf site it is
`AlgebraicGeometry.sieve_generate_singleton_mem_topology_over_of_flat`. -/
noncomputable def quasiFiniteRefinement
    (hJ : ∀ {A B : C} (a : A ⟶ B), Flat (F.map a).left →
      LocallyOfFinitePresentation (F.map a).left → Surjective (F.map a).left →
      Sieve.generate (Presieve.singleton a) ∈ J B) :
    QuasiFiniteRefinement J F G where
  objects := sigmaOver D.slice
  projection := sigmaOverDesc D.sliceMap
  reach_flat := reach_sigmaOverDesc_flat G D.sliceMap D.reach_flat
  reach_locallyOfFinitePresentation :=
    reach_sigmaOverDesc_locallyOfFinitePresentation G D.sliceMap
      D.reach_locallyOfFinitePresentation
  reach_locallyQuasiFinite :=
    reach_sigmaOverDesc_locallyQuasiFinite G D.sliceMap D.reach_locallyQuasiFinite
  siteSource := D.siteSource
  siteTarget := D.siteTarget
  siteSourceIso := D.siteSourceIso
  siteTargetIso := D.siteTargetIso
  cover := D.cover
  cover_spec := D.cover_spec
  cover_mem := hJ D.cover D.flat_map_cover D.locallyOfFinitePresentation_map_cover
    D.surjective_map_cover

end CoproductRefinement

/-! ### The covering hypothesis on a big fppf site -/

/-- On a big fppf site over `S`, presented by `CategoryTheory.Over.post` applied to the site's
inclusion into schemes, a morphism of the site which is flat, locally of finite presentation
and surjective as a morphism of schemes generates a covering sieve.

This is the hypothesis `hJ` of
`Stacks.Groupoids.GroupoidScheme.CoproductRefinement.quasiFiniteRefinement`, so that hypothesis
is a property the topology of interest has, not an extra assumption on the refinement. -/
theorem bigFppfOver_generate_singleton_mem_topology (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A A' : BigFppfOver B S hS} (a : A ⟶ A')
    (hflat : Flat ((Over.post B.inclusion).map a).left)
    (hfp : LocallyOfFinitePresentation ((Over.post B.inclusion).map a).left)
    (hsurj : Surjective ((Over.post B.inclusion).map a).left) :
    Sieve.generate (Presieve.singleton a) ∈ BigFppfOver.topology B S hS A' :=
  AlgebraicGeometry.Space.sieve_generate_singleton_mem_topology_over_of_flat B S hS a hsurj
    hflat hfp

/-- **Stacks Project, Tag 0489**, conditional on Steps 1 and 2 of its proof.

Let `R` be a groupoid scheme over `S` whose target and source are an equivalence relation.
Given the output of Step 3 of the proof in the sense of
`Stacks.Groupoids.GroupoidScheme.CoproductRefinement` — a family of morphisms
`g i : U'_i ⟶ U` whose reach maps are flat, locally of finite presentation and locally
quasi-finite and whose images contain the finite type points of `U`, together with the
coproduct of the sources of those reach maps taken inside the site — the restriction of `R` to
`∐ U'_i` is again an equivalence
relation, its source and target are flat, locally of finite presentation, locally of finite
type and locally quasi-finite, and the induced map of quotient sheaves is an isomorphism.

This is
`Stacks.Groupoids.GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap` with
its carried refinement replaced by the data of Step 3; the morphism to the object scheme is
produced here rather than carried. -/
theorem exists_restriction_locallyQuasiFinite_isIso_quotientMap_of_coproductRefinement
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S) (hF : F.Full)
    (G : GroupoidScheme S) [IsEquivalenceRelation G.target G.source] {ι : Type t}
    [Small.{u} ι] (D : CoproductRefinement J F G ι)
    (hJ : ∀ {A B : C} (a : A ⟶ B), Flat (F.map a).left →
      LocallyOfFinitePresentation (F.map a).left → Surjective (F.map a).left →
      Sieve.generate (Presieve.singleton a) ∈ J B) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects),
      ∀ R' : AlgebraicGeometry.GroupoidScheme.Restriction G g,
      IsEquivalenceRelation R'.groupoid.target R'.groupoid.source ∧
      Flat R'.groupoid.source.left ∧
      LocallyOfFinitePresentation R'.groupoid.source.left ∧
      LocallyOfFiniteType R'.groupoid.source.left ∧
      LocallyQuasiFinite R'.groupoid.source.left ∧
      Flat R'.groupoid.target.left ∧
      LocallyOfFinitePresentation R'.groupoid.target.left ∧
      LocallyOfFiniteType R'.groupoid.target.left ∧
      LocallyQuasiFinite R'.groupoid.target.left ∧
      IsIso (restrictionQuotientMap J F G g R') :=
  exists_restriction_locallyQuasiFinite_isIso_quotientMap J F hF G (D.quasiFiniteRefinement hJ)

end Stacks.Groupoids.GroupoidScheme

end
