module

public import StacksFrontier.AlgebraicGeometry.Groupoids.QuotientSheaf.CoproductReachMap
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.EquivalenceRelationTrivial
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# The quasi-finite refinement of a Cohen–Macaulay equivalence-relation groupoid

Steps 2 and 3 of the proof of **Stacks 0489** take a groupoid scheme whose source and target
maps are Cohen–Macaulay and locally of finite presentation and whose stabilizer is locally
quasi-finite, and produce a single morphism `g : U' ⟶ U` whose *reach map*
`h : U' ×_{g, U, t} R ⟶ U` is flat, locally of finite presentation, locally quasi-finite and
surjective.

This file assembles them.  Step 2 is **Stacks 04N0**, available here as
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint`: it produces, for
each finite type point `u` of `U`, an affine immersion `g_u : U'_u ⟶ U` whose reach map `h_u` is
flat, locally of finite presentation and locally quasi-finite.  Step 3 takes `U'` to be the
disjoint union of the `U'_u` over all finite type points of `U` and `g` to be `∐_u g_u`; the
material of `CoproductReachMap` then gives the three local properties of `h = ∐_u h_u`, and
surjectivity because the image of each `h_u` contains `u` — the identity arrow at a point of
`U'_u` is a section of `h_u` over `g_u` — and the finite type points are dense.

The stabilizer hypothesis of Stacks 04N0 is *not* assumed: for an equivalence relation the
stabilizer is trivial, by `AlgebraicGeometry.locallyQuasiFinite_stabilizer_hom`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.reachSection`: the identity arrow at an object of `U'`, read
  as a section of the reach map over `g`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_reach_locallyQuasiFinite_surjective`: Steps 2 and 3
  of the proof of **Stacks 0489**.

## Implementation notes

The index set of Step 3 is the set of finite type points of the object scheme, a subtype of the
points of a scheme in `Type u`, so the smallness needed for the disjoint union is automatic.

The morphism `AlgebraicGeometry.SliceSituation.sourceMap` of the slice situation that
**Stacks 04N0** is stated with is the reach map
`AlgebraicGeometry.GroupoidScheme.restrictionReachMap`, both being
`pullback.snd g t ≫ s` in schemes over the base, so the output of Stacks 04N0 is used directly
with no comparison.

The conclusion is an existence statement rather than a structure, so that nothing about the
refinement is assumed; what it provides is exactly the geometric content needed to restrict the
groupoid, with no datum about any site.

## References

* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 0489](https://stacks.math.columbia.edu/tag/0489)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}}

/-- The identity arrow at an object of `U'`, read as a point of `U' ×_{g, U, t} R`: its target
lifts along `g` tautologically, and its source is the object itself, so it is a section of the
reach map over `g`. -/
public noncomputable def reachSection (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : U' ⟶ pullback g G.target :=
  pullback.lift (𝟙 U') (g ≫ G.identity) (by
    rw [Category.id_comp, Category.assoc, G.target_identity, Category.comp_id])

/-- The identity arrow is a section of the reach map over `g`. -/
public theorem reachSection_comp_reachMap (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) : reachSection G g ≫ restrictionReachMap G g = g := by
  have h : reachSection G g ≫ pullback.snd g G.target = g ≫ G.identity :=
    pullback.lift_snd _ _ _
  change reachSection G g ≫ pullback.snd g G.target ≫ G.source = g
  rw [← Category.assoc, h, Category.assoc, G.source_identity, Category.comp_id]

/-- Every point in the image of `g` is in the image of the reach map of `g`. -/
public theorem range_le_range_restrictionReachMap (G : GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) :
    Set.range g.left ⊆ Set.range (restrictionReachMap G g).left := by
  have hc : (reachSection G g).left ≫ (restrictionReachMap G g).left = g.left := by
    rw [← Over.comp_left, reachSection_comp_reachMap]
  rintro _ ⟨w, rfl⟩
  refine ⟨(reachSection G g).left w, ?_⟩
  rw [← hc]
  exact (Scheme.Hom.comp_apply _ _ w).symm

/-- **Steps 2 and 3 of the proof of Stacks 0489.** Let `(U, R, s, t, c, e, i)` be a groupoid
scheme over `S` whose target and source maps form an equivalence relation and are Cohen–Macaulay
and locally of finite presentation.  Then there is a morphism `g : U' ⟶ U` whose reach map
`h : U' ×_{g, U, t} R ⟶ U` is flat, locally of finite presentation, locally quasi-finite and
surjective.

`U'` is the disjoint union, over the finite type points `u` of `U`, of the affine slices
`g_u : U'_u ⟶ U` of **Stacks 04N0**, and `g = ∐_u g_u`.  The three local properties pass from the
`h_u` to `h` because they are Zariski-local at the source and the sources of the `h_u` cover the
source of `h`.  Surjectivity holds because `h` is flat and locally of finite presentation, hence
has open image, and that image contains every finite type point `u` — being the image of `h_u`,
which contains the image of `g_u`, which contains `u` — while the finite type points meet every
nonempty locally closed subset.

The stabilizer hypothesis of Stacks 04N0 is discharged rather than assumed, the stabilizer of an
equivalence-relation groupoid being trivial.

The last conclusion is the size estimate that the disjoint union of Step 3 raises, and it is
recorded because nothing else can recover it: the slices are affine immersions locally of finite
presentation, so each has size at most `size U` by **Stacks 000R** (8)
(`AlgebraicGeometry.Scheme.size_le_of_mono_locallyOfFinitePresentation`), and the index set is a
subtype of the points of `U`, of cardinality at most `2 ^ size U`
(`AlgebraicGeometry.Scheme.mk_le_two_pow_size`); so the disjoint union has size at most
`2 ^ size U` by **Stacks 000Q** (`AlgebraicGeometry.schemeSize_coproduct_le`).  One power is
genuinely lost — the family is indexed by points, not by a small set — but `2 ^ size U` is still
below every cardinal closed under powersets exceeding `size U`, which is what a size cutoff
provides. -/
public theorem exists_reach_locallyQuasiFinite_surjective
    (G : GroupoidScheme S) [IsEquivalenceRelation G.target G.source]
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hs : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf) :
    ∃ (U' : Over S) (g : U' ⟶ G.objects),
      Flat (restrictionReachMap G g).left ∧
      LocallyOfFinitePresentation (restrictionReachMap G g).left ∧
      LocallyQuasiFinite (restrictionReachMap G g).left ∧
      Surjective (restrictionReachMap G g).left ∧
      U'.left.size ≤ 2 ^ G.objects.left.size := by
  classical
  have _hflatloc : IsZariskiLocalAtSource (@Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat.{u})
  have _hlfploc : IsZariskiLocalAtSource (@LocallyOfFinitePresentation.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFinitePresentation.{u})
  have _hlqfloc : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyQuasiFinite.{u})
  -- Step 2, at every finite type point.
  have key : ∀ i : {y : G.objects.left // AlgebraicGeometry.IsFiniteTypePoint y},
      ∃ (U' : Over S) (g : U' ⟶ G.objects),
        i.1 ∈ Set.range g.left ∧
        Flat (restrictionReachMap G g).left ∧
        LocallyOfFinitePresentation (restrictionReachMap G g).left ∧
        LocallyQuasiFinite (restrictionReachMap G g).left ∧
        U'.left.size ≤ G.objects.left.size := by
    intro i
    obtain ⟨U', g, u', hgu, -, hImm, hgLFP, ⟨hflat, hlfp, hlqf⟩, -, -⟩ :=
      exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint G i.1 i.2 hs ht
    have _ : IsImmersion g.left := hImm
    have _ : LocallyOfFinitePresentation g.left := hgLFP
    exact ⟨U', g, ⟨u', hgu⟩, hflat, hlfp, hlqf,
      Scheme.size_le_of_mono_locallyOfFinitePresentation g.left⟩
  choose Uf gf hmem hflat hlfp hlqf hsize using key
  -- Step 3: the disjoint union of the slices.
  have hdesc : ∀ {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtSource P],
      (∀ i, P (restrictionReachMap G (gf i)).left) →
        P (restrictionReachMap G (sigmaOverDesc Uf gf)).left := fun hP =>
    reachMap_mem_of_forall G (sigmaOverDesc Uf gf) (sigmaOverIncl Uf)
      (sigmaOverIncl_comp_sigmaOverDesc Uf gf) (fun i => inferInstance)
      (exists_mem_range_sigmaOverIncl_left Uf) hP
  refine ⟨sigmaOver Uf, sigmaOverDesc Uf gf, hdesc hflat, hdesc hlfp, hdesc hlqf, ?_, ?_⟩
  · have _ := hdesc hflat
    have _ := hdesc hlfp
    exact surjective_reachMap_of_finiteTypePoints G (sigmaOverDesc Uf gf) (sigmaOverIncl Uf)
      (sigmaOverIncl_comp_sigmaOverDesc Uf gf)
      (fun y hy => ⟨⟨y, hy⟩, range_le_range_restrictionReachMap G (gf ⟨y, hy⟩)
        (hmem ⟨y, hy⟩)⟩)
  · -- The size of the disjoint union: at most `2 ^ size U` summands, each of size at most
    -- `size U`.
    have hℵ : Cardinal.aleph0 ≤ G.objects.left.size := G.objects.left.aleph0_le_size
    have hpow : G.objects.left.size ≤ 2 ^ G.objects.left.size := by
      rw [← Cardinal.power_self_eq hℵ]
      exact Cardinal.self_le_power _ (Cardinal.one_le_aleph0.trans hℵ)
    have hindex : Cardinal.mk {y : G.objects.left // AlgebraicGeometry.IsFiniteTypePoint y} ≤
        2 ^ G.objects.left.size :=
      (Cardinal.mk_subtype_le _).trans G.objects.left.mk_le_two_pow_size
    exact schemeSize_coproduct_le (fun i => (Uf i).left) _ (hℵ.trans hpow) hindex
      fun i => (hsize i).trans hpow

end AlgebraicGeometry.GroupoidScheme

end
