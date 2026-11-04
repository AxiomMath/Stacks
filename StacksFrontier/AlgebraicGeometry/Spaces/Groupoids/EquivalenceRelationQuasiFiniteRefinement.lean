module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.GroupoidRestriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionEquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs

/-!
# Refining an equivalence relation to one with locally quasi-finite structure maps

Stacks 0489 says that an equivalence relation `j : R ⟶ U ×_S U` on schemes whose source and
target are flat and locally of finite presentation can be *refined*: there is an equivalence
relation `j' : R' ⟶ U' ×_S U'` whose source and target are in addition locally quasi-finite,
together with a morphism `U' ⟶ U` carrying `R'` into `R` which induces an isomorphism
`U'/R' ⟶ U/R` of quotient sheaves.

The refinement in the source is built in three steps.  Stacks 0460 shrinks `U` to the open over
which `s` is Cohen-Macaulay; Stacks 04N0 then produces, for each finite type point `u` of `U`,
an affine immersion `g_u : U'_u ⟶ U` locally of finite presentation such that the *reach map*
`h_u : U'_u ×_{g_u, U, t} R ⟶ U`, which sends an arrow whose target lifts along `g_u` to its
source, is flat, locally of finite presentation and locally quasi-finite; and `U'` is the
coproduct `∐_u U'_u` with `g = ∐ g_u`, for which the reach map `h = ∐ h_u` keeps those three
properties and is in addition surjective, hence an fppf covering.

What this file carries, as `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement`, is exactly
the output of those three steps: the morphism `g : U' ⟶ U` whose reach map is flat, locally of
finite presentation and locally quasi-finite, and which is a singleton covering of the site.
What it derives is the whole conclusion of the tag.  Both halves of the last step of the source
proof are the derivation: the source and target of the restriction `R' = R|_{U'}` inherit all
three properties from the reach map, because they are base changes of it along `g` (Stacks 04MV,
here `AlgebraicGeometry.restriction_source_mem` and
`AlgebraicGeometry.restriction_target_mem`); and the covering hypothesis feeds Stacks 02VH,
here `AlgebraicGeometry.GroupoidScheme.isIso_restrictionQuotientMap_of_reach_cover`, to give the
isomorphism of quotient sheaves.  That the restriction is again an equivalence relation is
`AlgebraicGeometry.restriction_isEquivalenceRelation`.

## Main definitions

* `Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement`: the output of Steps 1 to 3 of the
  proof of **Stacks 0489** — a morphism to the object scheme whose reach map is flat, locally of
  finite presentation and locally quasi-finite, together with the datum exhibiting that reach
  map as a singleton covering of the site.

## Main results

* `Stacks.Groupoids.GroupoidScheme.exists_restriction_locallyQuasiFinite_isIso_quotientMap`:
  **Stacks 0489**, conditional on that refinement.

## Implementation notes

**The refinement carried here is now built, and the tag is unconditional.**  The construction is
`AlgebraicGeometry.exists_quasiFiniteRefinement_cohenMacaulayRestriction`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/CohenMacaulayQuasiFiniteRefinement.lean`: it
produces a `QuasiFiniteRefinement` of the Cohen-Macaulay restriction of a flat, locally finitely
presented equivalence-relation groupoid whose object scheme belongs to the big fppf site.  The
unconditional form of the tag, in the shape its consumers use, is
`AlgebraicGeometry.exists_locallyQuasiFinite_groupoid_quotientSheaf_iso`.  The two obligations
the rest of this note names as owed -- openness of the image of each `h_u`, and the
set-theoretic footnote -- are
`AlgebraicGeometry.isOpen_range_of_flat_of_locallyOfFinitePresentation` (Mathlib's
`AlgebraicGeometry.UniversallyOpen.of_flat`, Stacks 01UA, read on the underlying spaces) and
`AlgebraicGeometry.Scheme.size_sigma_lt_of_mono` together with
`AlgebraicGeometry.BigFppfSite.contains_arrows_of_isEquivalenceRelation`.  The footnote is not
blocked by the countability restriction on `AlgebraicGeometry.Scheme.size_sigmaObj_lt` which the
paragraphs below cite: the slices are sources of monomorphisms into *one* scheme, so their sizes
have a bound with no index in it and no supremum needs its cofinality bounded.  The attribute
string on the theorem below, and the paragraphs that follow, describe the superseded conditional
state and are kept only for the account they give of the proof.

The refinement was carried rather than built because two pieces of substrate it needs are
missing from this library.  Steps 1 and 2 themselves are complete: see
`AlgebraicGeometry.exists_affine_slice_cohenMacaulayRestriction`, which produces the slice of
Step 2 at every finite type point of the Cohen-Macaulay open of Step 1, under no hypothesis
beyond those of the tag.  What is missing is Step 3, the passage from those slices to a single
`g`.

Of Step 3, what is available is
`StacksFrontier/AlgebraicGeometry/Groupoids/Slicing/ReachMapCoproduct.lean`: the reach map of
`∐_u g_u` is flat, locally of finite presentation and locally quasi-finite as soon as every
`h_u` is (`AlgebraicGeometry.reachMap_sigmaDesc_mem`, for any property Zariski-local at the
source — each slice is an open of the coproduct, so the reach maps of the slices cover the
source of the total reach map); it is surjective as soon as the images of the `h_u` cover `U`
(`AlgebraicGeometry.surjective_reachMap_of_jointly_covering`); the image of each `h_u` contains
the image of `g_u`, hence the point `u` (`AlgebraicGeometry.exists_section_comp_reachMap_eq`);
and an open of `U` containing every finite type point is `U`
(`AlgebraicGeometry.Scheme.Opens.eq_top_of_finiteTypePoints_subset`, from
[Stacks, Tag 02J4]).  What is still owed for the covering clause is that the image of each `h_u`
is *open*, which is flatness together with local finite presentation.

What is owed outright is the set-theoretic footnote: `∐_u U'_u`, over the finite type points of
`U`, must be an object of the site, and the reach map a morphism of the site.  The objects of a
big fppf site of this library are closed under at most countable coproducts
(`AlgebraicGeometry.schemeSizeBelow_isClosedUnderColimitsOfShape_discrete`), so this needs the
size estimate of the source's footnote against the site's strong-limit cutoff; the convention
this library follows meanwhile is to carry the coproduct-in-the-site as data, as Stacks 04SK and
Stacks 02WQ do.  The restriction of a groupoid scheme along a coproduct is likewise not
available as such: what exists is the binary comparison
`AlgebraicGeometry.GroupoidScheme.CoproductDecomposition` and the two-term material of
`StacksFrontier/AlgebraicGeometry/Spaces/CoveringRestrictionCoproduct.lean`, but the reach-map
results above make it unnecessary — the fields of `QuasiFiniteRefinement` are properties of the
reach map, and the passage from the fibre product of schemes used there to the one of `Over S`
is `AlgebraicGeometry.overFibreProduct_isPullback`.

Relatedly, the coproduct of Step 3 must be an object *of the site*, which the source secures by
the size estimate of its footnote; the convention this library follows for such a hypothesis is
that of Stacks 04SK and Stacks 02WQ, namely to carry the coproduct-in-the-site as data.  Here
that convention is realized by carrying the singleton-covering datum
(`siteSource`, `siteTarget`, `cover` and their compatibilities) rather than a coproduct: it is
the only consequence of Step 3 that the proof uses, and it is stated so that *any* site
presented by a functor `F : C ⥤ Over S` may be used, as everywhere else in the quotient-sheaf
API of this library.

Steps 1 and 2, by contrast, are not missing.  Step 1 is Stacks 0460, proved here in
`StacksFrontier/AlgebraicGeometry/Groupoids/More/CohenMacaulayRestriction.lean`; its part (5),
`AlgebraicGeometry.restricted_source_cohenMacaulay` and its three companions, gives the
restriction to `AlgebraicGeometry.cohenMacaulayOpen` Cohen-Macaulay and locally finitely
presented source and target maps.  Step 2 is Stacks 04N0, here
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`, in exactly the reach-map form used
here; its two Cohen-Macaulay hypotheses are literally what part (5) of Stacks 0460 produces, and
its remaining hypothesis, local quasi-finiteness of the stabilizer group scheme, is automatic for
an equivalence relation by `AlgebraicGeometry.locallyQuasiFinite_stabilizer_hom` — the stabilizer
is the object scheme itself, `AlgebraicGeometry.isIso_stabilizer_hom` — and the restriction of an
equivalence relation is again one, `AlgebraicGeometry.restriction_isEquivalenceRelation`.  The two
steps are joined in `AlgebraicGeometry.exists_affine_slice_cohenMacaulayRestriction`.

The hypotheses of the tag on `s` and `t`, flatness and local finite presentation, are *not*
assumed: in the proof they serve only to produce the refinement, whose properties are carried
directly, and the conclusion's flatness and local finite presentation of `s'` and `t'` are
obtained from the reach map instead.  Dropping them strengthens the statement rather than
weakening it.

## References

* [Stacks Project, Tag 0233](https://stacks.math.columbia.edu/tag/0233)
* [Stacks Project, Tag 0460](https://stacks.math.columbia.edu/tag/0460)
* [Stacks Project, Tag 02V8](https://stacks.math.columbia.edu/tag/02V8)
* [Stacks Project, Tag 02VD](https://stacks.math.columbia.edu/tag/02VD)
* [Stacks Project, Tag 02VH](https://stacks.math.columbia.edu/tag/02VH)
* [Stacks Project, Tag 04MV](https://stacks.math.columbia.edu/tag/04MV)
* [Stacks Project, Tag 04MZ](https://stacks.math.columbia.edu/tag/04MZ)
* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.GroupoidScheme

universe u v w

namespace Stacks.Groupoids.GroupoidScheme

variable {S : Scheme.{u}} {C : Type v} [Category.{w} C]

/-- **The output of Steps 1 to 3 of the proof of Stacks 0489.**

A morphism `g : U' ⟶ U` to the object scheme of a groupoid scheme `R` whose *reach map*
`h : U' ×_{g, U, t} R ⟶ U`, the morphism sending an arrow of `R` whose target lifts along `g` to
its source, is flat, locally of finite presentation and locally quasi-finite, together with the
datum exhibiting `h` as a singleton covering of the site presented by `F`.

In the source `U'` is the coproduct `∐_u U'_u` over the finite type points of `U` of the affine
immersions produced by Stacks 04N0, and `h = ∐ h_u` is flat, locally of finite presentation and
locally quasi-finite because each `h_u` is, and surjective because the image of each `h_u`
contains `u`; a flat, locally of finite presentation and surjective morphism is an fppf
covering, which is what the singleton-covering datum records. -/
structure QuasiFiniteRefinement (J : GrothendieckTopology C) (F : C ⥤ Over S)
    (G : GroupoidScheme S) where
  /-- The scheme `U'`. -/
  objects : Over S
  /-- The morphism `g : U' ⟶ U`. -/
  projection : objects ⟶ G.objects
  /-- The reach map `h : U' ×_{g, U, t} R ⟶ U` is flat. -/
  reach_flat : Flat (restrictionReachMap G projection).left
  /-- The reach map is locally of finite presentation. -/
  reach_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (restrictionReachMap G projection).left
  /-- The reach map is locally quasi-finite. -/
  reach_locallyQuasiFinite : LocallyQuasiFinite (restrictionReachMap G projection).left
  /-- An object of the site presenting the source `U' ×_{g, U, t} R` of the reach map. -/
  siteSource : C
  /-- An object of the site presenting the target `U` of the reach map. -/
  siteTarget : C
  /-- The identification of `siteSource` with the source of the reach map. -/
  siteSourceIso : F.obj siteSource ≅ pullback projection G.target
  /-- The identification of `siteTarget` with the object scheme `U`. -/
  siteTargetIso : F.obj siteTarget ≅ G.objects
  /-- The reach map, read as a morphism of the site. -/
  cover : siteSource ⟶ siteTarget
  /-- It is the reach map under the two identifications. -/
  cover_spec : F.map cover ≫ siteTargetIso.hom =
    siteSourceIso.hom ≫ restrictionReachMap G projection
  /-- It generates a covering sieve: in the source this is the statement that `h` is an fppf
  covering, which holds because `h` is flat, locally of finite presentation and surjective. -/
  cover_mem : Sieve.generate (Presieve.singleton cover) ∈ J siteTarget

/-- **Stacks Project, Tag 0489**, conditional on Steps 1 to 3 of its proof.

Let `R` be a groupoid scheme over `S` whose target and source are an equivalence relation.
Given a refinement in the sense of
`Stacks.Groupoids.GroupoidScheme.QuasiFiniteRefinement` — a morphism `g : U' ⟶ U` whose reach
map is flat, locally of finite presentation and locally quasi-finite and is a singleton covering
of the site — the restriction `R' = R|_{U'}` is again an equivalence relation, its source and
target are flat, locally of finite presentation, locally of finite type and locally
quasi-finite, and the induced map `U'/R' ⟶ U/R` of quotient sheaves is an isomorphism.

The conclusion is stated for *every* groupoid scheme realizing the restriction, which is
stronger than producing one and avoids any appeal to the realization
`AlgebraicGeometry.GroupoidScheme.restrict` built by `Classical.choice`.  The morphism
`U' ⟶ U` carrying `R'` into `R` is the one recorded by
`AlgebraicGeometry.GroupoidScheme.Restriction.hom`, so the clause of the tag that the
isomorphism of quotient sheaves is induced by a morphism `U' ⟶ U` mapping `R'` into `R` is part
of the statement rather than an afterthought.

The flatness and local finite presentation hypotheses which the tag places on `s` and `t` are
not assumed; see the module docstring. -/
@[stacks 0489 "the refinement with locally quasi-finite source and target and the same \
quotient sheaf, given the refinement data as `QuasiFiniteRefinement`. The tag itself, with \
nothing carried, is \
`AlgebraicGeometry.exists_locallyQuasiFinite_groupoid_quotientSheaf_iso` of \
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/CohenMacaulayQuotientUnchanged.lean`, which \
builds that data from the Cohen-Macaulay restriction and the reach map"]
theorem exists_restriction_locallyQuasiFinite_isIso_quotientMap
    (J : GrothendieckTopology C) [HasSheafify J (Type u)] (F : C ⥤ Over S) (hF : F.Full)
    (G : GroupoidScheme S) [IsEquivalenceRelation G.target G.source]
    (N : QuasiFiniteRefinement J F G) :
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
      IsIso (restrictionQuotientMap J F G g R') := by
  refine ⟨N.objects, N.projection, fun R' => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- the restriction of an equivalence relation is an equivalence relation
    exact AlgebraicGeometry.restriction_isEquivalenceRelation G N.projection R'
  -- the source and target of the restriction are base changes of the reach map, by Stacks 04MV
  · exact AlgebraicGeometry.restriction_source_mem G N.projection R' @Flat N.reach_flat
  · exact AlgebraicGeometry.restriction_source_mem G N.projection R'
      @LocallyOfFinitePresentation N.reach_locallyOfFinitePresentation
  · have := N.reach_locallyOfFinitePresentation
    exact AlgebraicGeometry.restriction_source_mem G N.projection R' @LocallyOfFiniteType
      inferInstance
  · exact AlgebraicGeometry.restriction_source_mem G N.projection R' @LocallyQuasiFinite
      N.reach_locallyQuasiFinite
  · exact AlgebraicGeometry.restriction_target_mem G N.projection R' @Flat N.reach_flat
  · exact AlgebraicGeometry.restriction_target_mem G N.projection R'
      @LocallyOfFinitePresentation N.reach_locallyOfFinitePresentation
  · have := N.reach_locallyOfFinitePresentation
    exact AlgebraicGeometry.restriction_target_mem G N.projection R' @LocallyOfFiniteType
      inferInstance
  · exact AlgebraicGeometry.restriction_target_mem G N.projection R' @LocallyQuasiFinite
      N.reach_locallyQuasiFinite
  · -- Stacks 02VH: the reach map is a covering, so the map of quotient sheaves is bijective
    exact isIso_restrictionQuotientMap_of_reach_cover J F hF G N.projection R'
      N.siteSource N.siteTarget N.siteSourceIso N.siteTargetIso N.cover N.cover_spec
      N.cover_mem

end Stacks.Groupoids.GroupoidScheme

end
