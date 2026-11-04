module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Fpqc
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Fppf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.DivisionDescent
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.InvariantAffineCover
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivision
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Comp
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.AffineRelationProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.OpenIdentityQuotientAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SchemeSplittings
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.FlatRelationQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteMorphismLocallySurjective

/-!
# The quotient of a groupoid divided by a finite locally free open subgroupoid

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `U` affine and in the big fppf site,
whose target and source form an internal equivalence relation and are flat, locally of finite
presentation, locally of finite type and locally quasi-finite, and let `P ⊆ R` be an open
subgroupoid on the same objects whose source and target are finite — a quasi-splitting in the
sense of [Stacks, Tag 04RK].  Then the fppf quotient sheaf `U/R` is an algebraic space over `S`
with a surjective étale atlas no larger than `U`.

This is the heart of the glueing step of [Stacks, Tag 04S6].  [Stacks, Tag 04S4] divides the
groupoid by `P`: the quotient `Ū = U/P` is an affine scheme, `U ⟶ Ū` is finite locally free and
surjective, and `R` is the restriction along `U ⟶ Ū` of a groupoid `(Ū, R̄, s̄, t̄)`, the square of
arrow schemes being cartesian.  From the cartesian square the identity section of the descended
groupoid is an open immersion — it is the descent of the open immersion `P ⟶ R` along the fppf
covering `R ⟶ R̄` — and `s̄` is flat and locally of finite presentation; so
[Stacks, Tag 02WW] applies to `R̄` and gives `Ū` as an atlas of `Ū/R̄`.  Finally `U/R = Ū/R̄`,
because `R` is the restriction of `R̄` along a morphism which is surjective on functors of points
([Stacks, Tag 045Z]).

## Main definitions

This file introduces no definitions.

## Main results

* `AlgebraicGeometry.isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_openFiniteSubgroupoid`:
  the quotient sheaf of the ambient groupoid is an algebraic space with an atlas of size at most
  that of the object scheme.

## Implementation notes

The atlas is `Ū`, and the bound `size Ū ≤ size U` is
`AlgebraicGeometry.Bootstrap04S6.size_le_of_flat_surjective_affine`: both schemes are affine and
`U ⟶ Ū` is flat and surjective, so the global sections of `Ū` inject into those of `U`.  The
doubly exponential bound of `AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective` would also
put `Ū` inside the site, but would not let the glueing induction keep its atlases bounded by the
object scheme it started from.

Two isomorphisms carry the conclusion from `Ū/R̄` back to `U/R`.  The first identifies `U/R` with
the quotient of the *restriction of the pre-relation of `R̄`* along `U ⟶ Ū`: the cartesian square
of [Stacks, Tag 04S4] says precisely that the arrow scheme of `R` is that restriction, and
`Stacks.Groupoids.quotientSheafMapIso` turns an isomorphism of pre-relations over the identity on
objects into an isomorphism of quotient sheaves.  The second is [Stacks, Tag 045Z]
(`Stacks.Groupoids.restrictQuotientSheafMap_isIso`), whose hypothesis is local surjectivity of
`U ⟶ Ū` on restricted functors of points — available because `U ⟶ Ū` is a surjective, flat,
locally finitely presented morphism of objects of the site.

The finite locally free hypotheses of [Stacks, Tag 04S4] on `P` are assembled from the
*finiteness* of its source and target, which the subgroupoid carries, together with flatness and
local finite presentation, which it inherits from `R` because `P ⟶ R` is an open immersion.

## References

* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 045Z](https://stacks.math.columbia.edu/tag/045Z)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Groupoids.GroupoidScheme

universe u

namespace AlgebraicGeometry

/-- A finite morphism out of the arrows of an open finite subgroupoid which is the restriction of
a flat, locally finitely presented morphism of the ambient groupoid is finite locally free. -/
private theorem openFiniteSubgroupoid_isFiniteLocallyFree {S : Scheme.{u}} {G : GroupoidScheme S}
    (P : OpenFiniteSubgroupoid G) {f : P.subgroupoid.arrows ⟶ P.subgroupoid.objects}
    {g : G.arrows ⟶ G.objects} (h : P.inclusion.mapArrows ≫ g = f ≫ P.inclusion.mapObjects)
    (hf : IsFinite f.left) [Flat g.left] [LocallyOfFinitePresentation g.left] :
    Stacks.Morphisms.IsFiniteLocallyFree f.left := by
  rw [P.mapObjects_eq] at h
  have h' : f = P.inclusion.mapArrows ≫ g ≫ eqToHom P.objects_eq.symm := by
    rw [← Category.assoc, h]
    simp
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion P.inclusion.mapArrows.left := P.arrows_open
  have _ : IsIso (eqToHom P.objects_eq.symm : G.objects ⟶ P.subgroupoid.objects).left :=
    (Over.forget S).map_isIso (eqToHom P.objects_eq.symm)
  have _ : Flat f.left := by
    rw [h', Over.comp_left, Over.comp_left]
    infer_instance
  have _ : LocallyOfFinitePresentation f.left := by
    rw [h', Over.comp_left, Over.comp_left]
    infer_instance
  exact (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
    ⟨hf, inferInstance, inferInstance⟩

/-- The pre-relation of an open finite subgroupoid of a groupoid with monic pre-relation is
monic. -/
private theorem openFiniteSubgroupoid_mono_groupoidPreRelation {S : Scheme.{u}}
    {G : GroupoidScheme S} (P : OpenFiniteSubgroupoid G) [Mono (groupoidPreRelation G)] :
    Mono (groupoidPreRelation P.subgroupoid) := by
  have _ : IsIso P.inclusion.mapObjects := by
    rw [P.mapObjects_eq]
    infer_instance
  have hkey : P.inclusion.mapArrows ≫ groupoidPreRelation G =
      groupoidPreRelation P.subgroupoid ≫
        prod.map P.inclusion.mapObjects P.inclusion.mapObjects := by
    rw [prod.comp_lift, P.inclusion.map_target, P.inclusion.map_source, prod.lift_map]
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion P.inclusion.mapArrows.left := P.arrows_open
  have _ : Mono P.inclusion.mapArrows :=
    (Over.forget S).mono_of_mono_map
      (_root_.AlgebraicGeometry.IsOpenImmersion.mono P.inclusion.mapArrows.left)
  have _ : Mono (groupoidPreRelation P.subgroupoid ≫
      prod.map P.inclusion.mapObjects P.inclusion.mapObjects) := by
    rw [← hkey]
    infer_instance
  exact mono_of_mono _ (prod.map P.inclusion.mapObjects P.inclusion.mapObjects)

/-- A finite flat quotient map, precomposed and postcomposed with isomorphisms, is still finite
locally free and surjective. -/
private theorem finiteFlatQuotient_isFiniteLocallyFree_and_surjective_of_eq {S : Scheme.{u}}
    {H : GroupoidScheme S} (Q : FiniteFlatQuotient H) {X Y : Over S} (e : X ⟶ H.objects)
    [IsIso e] (he : Q.space = Y) {f : X ⟶ Y} (hf : f = (e ≫ Q.quotientMap) ≫ eqToHom he) :
    Stacks.Morphisms.IsFiniteLocallyFree f.left ∧ Surjective f.left := by
  have _ := Q.finiteLocallyFree
  have _ := Q.surjective
  have _ : IsIso e.left := (Over.forget S).map_isIso e
  have _ : IsIso (eqToHom he).left := (Over.forget S).map_isIso (eqToHom he)
  have _ : Stacks.Morphisms.IsFiniteLocallyFree e.left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have _ : Stacks.Morphisms.IsFiniteLocallyFree (eqToHom he).left :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  subst hf
  rw [Over.comp_left, Over.comp_left]
  exact ⟨inferInstance, inferInstance⟩

/-- Flatness and local finite presentation of the source descend along a cartesian morphism of
groupoids whose object map is flat, surjective and locally of finite presentation. -/
private theorem flat_and_locallyOfFinitePresentation_source_of_isPullback_arrows
    {S : Scheme.{u}} {G K : GroupoidScheme S} (F : GroupoidScheme.Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left]
    [LocallyOfFinitePresentation F.mapObjects.left]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Flat K.source.left ∧ LocallyOfFinitePresentation K.source.left := by
  have _ : MorphismProperty.IsLocalAtSource (@Flat.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtSource.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have _ : MorphismProperty.IsLocalAtTarget (@Flat.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  have _ : MorphismProperty.IsLocalAtTarget
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le Scheme.fppfPrecoverage_le_fpqcPrecoverage
  exact ⟨property_source_of_isPullback_arrows (@Flat.{u}) F hp inferInstance,
    property_source_of_isPullback_arrows (@LocallyOfFinitePresentation.{u}) F hp inferInstance⟩

/-- An atlas bound for the quotient of a groupoid transports back along a cartesian morphism of
groupoids whose object map is flat, surjective and locally of finite presentation
([Stacks, Tag 045Z]). -/
private theorem isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_isPullback_arrows
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {G K : GroupoidScheme S} (hU : B.Contains G.objects.left) (hUK : B.Contains K.objects.left)
    (F : GroupoidScheme.Hom G K)
    (hp : IsPullback F.mapArrows (groupoidPreRelation G) (groupoidPreRelation K)
      (prod.map F.mapObjects F.mapObjects))
    [Surjective F.mapObjects.left] [Flat F.mapObjects.left]
    [LocallyOfFinitePresentation F.mapObjects.left] {μ : Cardinal.{u}}
    (h : Space.IsAlgebraicSpaceAtlasSizeLE B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation K)).obj μ) :
    Space.IsAlgebraicSpaceAtlasSizeLE B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation G)).obj μ := by
  set UG : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk G.objects.hom : B.obj hU ⟶ B.obj hS)
  set UK : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk K.objects.hom : B.obj hUK ⟶ B.obj hS)
  set qs : UG ⟶ UK :=
    Over.homMk (ObjectProperty.homMk F.mapObjects.left) (by ext; exact F.mapObjects.w)
  have hqmap : (Over.post (X := B.obj hS) B.inclusion).map qs = F.mapObjects := rfl
  have _ : Surjective ((BigFppfOver.toScheme B S hS).map qs) :=
    inferInstanceAs (Surjective F.mapObjects.left)
  have _ : Flat ((BigFppfOver.toScheme B S hS).map qs) :=
    inferInstanceAs (Flat F.mapObjects.left)
  have _ : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map qs) :=
    inferInstanceAs (LocallyOfFinitePresentation F.mapObjects.left)
  have _ : IsIso (restrictQuotientSheafMap (BigFppfOver.topology B S hS)
      (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation K) F.mapObjects) := by
    rw [← hqmap]
    exact restrictQuotientSheafMap_isIso _ _ _ _
      (AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation K)
      (Space.isLocallySurjective_whiskerLeft_yoneda_map_of_flat B S hS qs inferInstance
        inferInstance inferInstance)
  have hiso : Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation G) ≅
      Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion)
        (PreRelation.restrict (groupoidPreRelation K) F.mapObjects) := by
    refine quotientSheafMapIso _ _ (groupoidPreRelation G)
      (PreRelation.restrict (groupoidPreRelation K) F.mapObjects)
      hp.flip.isoPullback.hom (𝟙 G.objects) hp.flip.isoPullback.inv (𝟙 G.objects)
      ?_ ?_ ?_ ?_ (by simp) (by simp)
    · change hp.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ prod.snd = _
      rw [← Category.assoc, hp.flip.isoPullback_hom_fst, Category.comp_id]
    · change hp.flip.isoPullback.hom ≫ pullback.fst _ _ ≫ prod.fst = _
      rw [← Category.assoc, hp.flip.isoPullback_hom_fst, Category.comp_id]
    · change hp.flip.isoPullback.inv ≫ groupoidPreRelation G ≫ prod.snd = _
      rw [← Category.assoc, hp.flip.isoPullback_inv_fst, Category.comp_id]
    · change hp.flip.isoPullback.inv ≫ groupoidPreRelation G ≫ prod.fst = _
      rw [← Category.assoc, hp.flip.isoPullback_inv_fst, Category.comp_id]
  exact Space.IsAlgebraicSpaceAtlasSizeLE.of_iso
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)).mapIso (hiso.trans
      (asIso (restrictQuotientSheafMap (BigFppfOver.topology B S hS)
        (Over.post (X := B.obj hS) B.inclusion) (groupoidPreRelation K) F.mapObjects)))) h

/-- Flatness and local finite presentation of the source of a groupoid scheme pass to its
target. -/
private theorem flat_and_locallyOfFinitePresentation_target {S : Scheme.{u}}
    (G : GroupoidScheme S) [Flat G.source.left] [LocallyOfFinitePresentation G.source.left] :
    Flat G.target.left ∧ LocallyOfFinitePresentation G.target.left := by
  have _ : MorphismProperty.RespectsIso (@Flat.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact ⟨_root_.AlgebraicGeometry.GroupoidScheme.property_target_of_property_source
      (@Flat.{u}) G inferInstance,
    _root_.AlgebraicGeometry.GroupoidScheme.property_target_of_property_source
      (@LocallyOfFinitePresentation.{u}) G inferInstance⟩

/-- **The quotient of a groupoid scheme on an affine object divided by a finite locally free
open subgroupoid is an algebraic space, with an atlas no larger than the object scheme.**

This is the division step of [Stacks, Tag 04S6]: [Stacks, Tag 04S4] produces the affine quotient
`Ū` of the object scheme by the subgroupoid together with the descended groupoid on `Ū`, whose
identity section is an open immersion and whose source is flat and locally of finite
presentation, so [Stacks, Tag 02WW] gives `Ū` as a surjective étale atlas of `Ū/R̄`; and
`U/R = Ū/R̄` by [Stacks, Tag 045Z]. -/
theorem isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_openFiniteSubgroupoid
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (G : GroupoidScheme S) (hU : B.Contains G.objects.left)
    [IsAffine G.objects.left]
    [CategoryTheory.IsEquivalenceRelation G.target G.source]
    [Flat G.source.left] [LocallyOfFinitePresentation G.source.left]
    [LocallyQuasiFinite G.source.left] [LocallyOfFiniteType G.source.left]
    (P : OpenFiniteSubgroupoid G) :
    Space.IsAlgebraicSpaceAtlasSizeLE B S hS
      (Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B S hS)
        (Over.post B.inclusion) (groupoidPreRelation G)).obj G.objects.left.size := by
  classical
  have _ : JointlyMono₂ G.target G.source := jointlyMono₂_of_isEquivalenceRelation G
  have _ : Mono (groupoidPreRelation G) := mono_groupoidPreRelation_of_jointlyMono₂ G
  have hGs : (groupoidPreRelation G).source = G.source := prod.lift_snd _ _
  have _ : LocallyOfFiniteType (groupoidPreRelation G).source.left := by rw [hGs]; infer_instance
  have _ : LocallyQuasiFinite (groupoidPreRelation G).source.left := by rw [hGs]; infer_instance
  have _ : IsSeparated (groupoidPreRelation G).left :=
    PreRelation.isSeparated_of_isAffine (groupoidPreRelation G)
  have _ : LocallyOfFiniteType (groupoidPreRelation G).left :=
    PreRelation.locallyOfFiniteType_of_source (groupoidPreRelation G)
  have _ : LocallyQuasiFinite (groupoidPreRelation G).left :=
    PreRelation.locallyQuasiFinite_of_source (groupoidPreRelation G)
  obtain ⟨_, _⟩ := flat_and_locallyOfFinitePresentation_target G
  have _ : IsIso P.inclusion.mapObjects := by rw [P.mapObjects_eq]; infer_instance
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion P.inclusion.mapArrows.left := P.arrows_open
  have _ : Stacks.Morphisms.IsFiniteLocallyFree P.subgroupoid.source.left :=
    openFiniteSubgroupoid_isFiniteLocallyFree P P.inclusion.map_source P.source_finite
  have _ : Stacks.Morphisms.IsFiniteLocallyFree P.subgroupoid.target.left :=
    openFiniteSubgroupoid_isFiniteLocallyFree P P.inclusion.map_target P.target_finite
  have _ := openFiniteSubgroupoid_mono_groupoidPreRelation P
  obtain ⟨Q, hQaff, K, he, Fh, hFobj, hFpb, -⟩ :=
    exists_finiteFlatQuotient_isAffine_of_mono_groupoidPreRelation G P.subgroupoid P.inclusion
  obtain ⟨_, _⟩ :=
    finiteFlatQuotient_isFiniteLocallyFree_and_surjective_of_eq Q _ he.symm hFobj
  obtain ⟨_, _, _⟩ :=
    (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      Fh.mapObjects.left).mp inferInstance
  have _ : IsAffine K.objects.left := by rwa [he]
  have _ : JointlyMono₂ K.target K.source := jointlyMono₂_of_isPullback_arrows Fh hFpb
  have _ : CategoryTheory.IsEquivalenceRelation K.target K.source :=
    isEquivalenceRelation_of_jointlyMono₂ K
  have hkp : IsPullback (P.subgroupoid.target ≫ P.inclusion.mapObjects)
      (P.subgroupoid.source ≫ P.inclusion.mapObjects) Fh.mapObjects Fh.mapObjects := by
    refine Q.kernelPair.of_iso (Iso.refl P.subgroupoid.arrows) (asIso P.inclusion.mapObjects)
      (asIso P.inclusion.mapObjects) (eqToIso he.symm) (by simp) (by simp) ?_ ?_ <;>
      rw [hFobj] <;> simp
  have _ : _root_.AlgebraicGeometry.IsOpenImmersion K.identity.left :=
    isOpenImmersion_identity_of_isPullback_arrows Fh hFpb P.inclusion.mapArrows
      (P.subgroupoid.target ≫ P.inclusion.mapObjects)
      (P.subgroupoid.source ≫ P.inclusion.mapObjects)
      P.inclusion.map_target P.inclusion.map_source hkp
  obtain ⟨_, _⟩ := flat_and_locallyOfFinitePresentation_source_of_isPullback_arrows Fh hFpb
  have hKsize : K.objects.left.size ≤ G.objects.left.size := by
    have : Epi Fh.mapObjects.left := Flat.epi_of_flat_of_surjective Fh.mapObjects.left
    rw [Scheme.size_of_isAffine G.objects.left, Scheme.size_of_isAffine K.objects.left]
    exact max_le_max_left _ (Cardinal.mk_le_of_injective
      (ConcreteCategory.injective_of_mono_of_preservesPullback
        (Scheme.Γ.map Fh.mapObjects.left.op)))
  have hUK : B.Contains K.objects.left := hKsize.trans_lt hU
  exact (isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_isPullback_arrows B S hS hU hUK Fh hFpb
    (Space.isAlgebraicSpaceAtlasSizeLE_quotientSheaf_of_isOpenImmersion_identity B S hS K
      hUK)).mono hKsize

end AlgebraicGeometry

end
