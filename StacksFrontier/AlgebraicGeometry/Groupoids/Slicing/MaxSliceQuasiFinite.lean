module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RelativeDimensionLocus
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.QuasiFiniteSlice
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Openness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksCore.Tactic.StacksAttribute

/-!
# A locally quasi-finite slice of a groupoid scheme

Let `(U, R, s, t, c, e, i)` be a groupoid scheme with `s` and `t` Cohen--Macaulay and locally of
finite presentation, let `u` be a finite type point of `U`, and assume the stabilizer group
scheme is locally quasi-finite.  Then `u` admits an affine slice `g : U' ⟶ U` which is an
immersion locally of finite presentation and for which `h : U' ×_{g, U, t} R ⟶ U` and the source
and target maps of the restriction of the groupoid to `U'` are flat, locally of finite
presentation and locally quasi-finite.

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.quasiFiniteAt_of_fiberDimensionAt_le_zero`: a morphism locally of finite
  type is quasi-finite at a point of a zero-dimensional fibre.
* `AlgebraicGeometry.locallyQuasiFinite_of_relativeDimensionLE_zero`: a morphism locally of
  finite type of relative dimension at most zero is locally quasi-finite.
* `AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite`: the locally quasi-finite slice.

## Implementation notes

The slice is the one of
`AlgebraicGeometry.exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint`, restated with
the fibre products of schemes rather than those of `Over S`: the structure maps of the groupoid
live in `Over S`, so the fibre product of the slice is formed twice, once in each category.  The
comparison is an isomorphism by `AlgebraicGeometry.overFibreProduct_isPullback` and all three
properties respect isomorphisms, which is what the two transfer lemmas record; the source and
target maps of the restricted groupoid are base changes of `h`, so they inherit the three
properties from it.

## References

* [Stacks Project, Tag 04N0](https://stacks.math.columbia.edu/tag/04N0)
* [Stacks Project, Tag 047W](https://stacks.math.columbia.edu/tag/047W)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A morphism locally of finite type is quasi-finite at a point whose fibre has local dimension
at most zero there: local dimensions are nonnegative, so the bound makes the dimension zero. -/
@[stacks 0397 "a zero-dimensional fibre point is a quasi-finite point"]
public theorem quasiFiniteAt_of_fiberDimensionAt_le_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) ≤ 0) :
    f.QuasiFiniteAt x :=
  ((quasiFiniteAt_iff_fiberDimensionAt_eq_zero f x).mpr
    (le_antisymm hx (topologicalKrullDimAt_nonneg _))).2

/-- A morphism locally of finite type of relative dimension at most zero is locally
quasi-finite. -/
@[stacks 0397 "relative dimension at most zero implies locally quasi-finite"]
public theorem locallyQuasiFinite_of_relativeDimensionLE_zero {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (hf : RelativeDimensionLE f 0) :
    LocallyQuasiFinite f := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
  refine top_le_iff.mp fun x _ => ?_
  rw [Scheme.Hom.mem_quasiFiniteLocus]
  exact quasiFiniteAt_of_fiberDimensionAt_le_zero f x (by simpa using hf x)

/-- A property of morphisms of schemes which respects isomorphisms and holds for the morphism
`h : U' ×_{g, U, t} R ⟶ U` formed with the fibre product of schemes also holds for the one
formed with the fibre product in `Over S`, the two being canonically isomorphic. -/
private lemma slice_sourceMap_mem {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange]
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Scheme.{u}} (g : U' ⟶ G.objects.left)
    (hP : P (pullback.snd g G.target.left ≫ G.source.left)) :
    P ((pullback.snd (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)
      G.target ≫ G.source).left) := by
  let gO : Over.mk (g ≫ G.objects.hom) ⟶ G.objects := Over.homMk g
  rw [Over.comp_left, ← (overFibreProduct_isPullback gO G.target).isoPullback_hom_snd,
    Category.assoc]
  exact (P.cancel_left_of_respectsIso _ _).mpr hP

/-- A property stable under base change which holds for `h : U' ×_{g, U, t} R ⟶ U` formed in
`Over S` holds for `h` formed with schemes and for the source and target maps of the restricted
groupoid. -/
private lemma slice_mem_of_over {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange]
    {S : Scheme.{u}} (G : GroupoidScheme S) {U' : Over S} (g : U' ⟶ G.objects)
    (hP : P ((pullback.snd g G.target ≫ G.source).left)) :
    P (pullback.snd g.left G.target.left ≫ G.source.left) ∧
      P (GroupoidScheme.restrict G (Over.homMk g.left : Over.mk (g.left ≫ G.objects.hom) ⟶
        G.objects)).groupoid.source.left ∧
      P (GroupoidScheme.restrict G (Over.homMk g.left : Over.mk (g.left ≫ G.objects.hom) ⟶
        G.objects)).groupoid.target.left := by
  have h : P (pullback.snd g.left G.target.left ≫ G.source.left) := by
    rw [Over.comp_left, ← (overFibreProduct_isPullback g G.target).isoPullback_hom_snd,
      Category.assoc, P.cancel_left_of_respectsIso] at hP
    exact hP
  exact ⟨h, restriction_source_mem G _ _ P (slice_sourceMap_mem G _ h),
    restriction_target_mem G _ _ P (slice_sourceMap_mem G _ h)⟩

/-- **Stacks Project, Tag 04N0.** A finite type point of a groupoid scheme whose source and
target maps are Cohen--Macaulay and locally of finite presentation and whose stabilizer group
scheme is locally quasi-finite has an affine slice `g : U' ⟶ U`, an immersion locally of finite
presentation, for which `h : U' ×_{g, U, t} R ⟶ U` and the source and target maps of the
restricted groupoid are flat, locally of finite presentation and locally quasi-finite. -/
@[stacks 04N0 "conclusions (1)-(5) with the fibre products of schemes: `g` an affine immersion \
locally of finite presentation, `h`, `s'`, `t'` flat, locally finitely presented, quasi-finite"]
public theorem exists_affine_slice_locallyQuasiFinite {S : Scheme.{u}}
    (G : GroupoidScheme S) (u : G.objects.left)
    (hu : AlgebraicGeometry.IsFiniteTypePoint u)
    [LocallyOfFinitePresentation G.source.left]
    [LocallyOfFinitePresentation G.target.left]
    (hs : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.source.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.source.left hf)
    (ht : ∃ hf : ∀ y : G.objects.left, IsLocallyNoetherian (G.target.left.fiber y),
      Scheme.Hom.IsCohenMacaulay G.target.left hf)
    [LocallyQuasiFinite (stabilizer G).hom] :
    ∃ (U' : Scheme.{u}) (g : U' ⟶ G.objects.left) (u' : U'),
      g u' = u ∧ IsAffine U' ∧ IsImmersion g ∧ LocallyOfFinitePresentation g ∧
      Flat (pullback.snd g G.target.left ≫ G.source.left) ∧
      LocallyOfFinitePresentation (pullback.snd g G.target.left ≫ G.source.left) ∧
      LocallyQuasiFinite (pullback.snd g G.target.left ≫ G.source.left) ∧
      Flat (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.source.left ∧
      LocallyOfFinitePresentation (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.source.left ∧
      LocallyQuasiFinite (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.source.left ∧
      Flat (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.target.left ∧
      LocallyOfFinitePresentation (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.target.left ∧
      LocallyQuasiFinite (GroupoidScheme.restrict G
        (Over.homMk g : Over.mk (g ≫ G.objects.hom) ⟶ G.objects)).groupoid.target.left := by
  obtain ⟨U', g, u', hgu, hAffine, hImm, hgLFP, ⟨hflatO, hlfpO, hqfO⟩, -, -⟩ :=
    exists_affine_slice_locallyQuasiFinite_of_isFiniteTypePoint G u hu hs ht
  obtain ⟨hflat, hflatS, hflatT⟩ := slice_mem_of_over (P := @Flat) G g hflatO
  obtain ⟨hfp, hfpS, hfpT⟩ := slice_mem_of_over (P := @LocallyOfFinitePresentation) G g hlfpO
  obtain ⟨hqf, hqfS, hqfT⟩ := slice_mem_of_over (P := @LocallyQuasiFinite) G g hqfO
  exact ⟨U'.left, g.left, u', hgu, hAffine, hImm, hgLFP, hflat, hfp, hqf, hflatS, hfpS, hqfS,
    hflatT, hfpT, hqfT⟩

end AlgebraicGeometry
