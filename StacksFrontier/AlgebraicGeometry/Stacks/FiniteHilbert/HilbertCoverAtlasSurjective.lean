module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverAtlasRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.FieldPointCover
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.AlgebraicGeometry.Varieties.BoundedDegree.Rank

/-!
# The atlas candidate of `ℋ_d` is surjective

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` from the category represented by
the scheme of structure constants over `S` into the category `ℋ_d` of degree-`d` finite locally
free covers is surjective, in the sense the presentation clause of **Stacks 026O** asks for: it
has the relative property of **Stacks 03YK** for surjectivity of morphisms of algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.structureConstantsPoint`: a scheme morphism into the scheme of
  structure constants, read as a morphism of the big fppf site of `S` into the scheme of
  structure constants over `S`.

## Main results

* `AlgebraicGeometry.Stack.isPullback_toScheme_map_pullback_snd_structureConstantsPoint`: the
  base change of the universal cover over `S` along such a point is the base change of the
  universal cover over the integers along the point itself.
* `AlgebraicGeometry.Stack.exists_structureConstantsPoint_iso_of_isFieldObject`: a degree-`d`
  cover of an object of the site whose underlying scheme is the spectrum of a field is, over its
  base, the base change of the universal cover over `S` along a point of the scheme of structure
  constants over `S`.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_finiteCoverUniversalAtlas`: the atlas candidate
  is surjective on objects.
* `AlgebraicGeometry.Stack.hasRelativeProperty_surjective_finiteCoverUniversalAtlas`: the atlas
  candidate is surjective.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.FiniteFreeAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ) [NeZero d]

/-- A morphism of the site into the scheme of structure constants over `S`, from a scheme
morphism into the scheme of structure constants. -/
noncomputable def structureConstantsPoint (U : BigFppfOver B S hS)
    (q : (BigFppfOver.toScheme B S hS).obj U ⟶ structureConstantsSpec.{u} d) :
    U ⟶ structureConstantsOver B S hS d :=
  Over.homMk
    (ObjectProperty.homMk (pullback.lift q (B.inclusion.map U.hom)
      (specULiftZIsTerminal.hom_ext _ _)))
    (ObjectProperty.hom_ext _ (pullback.lift_snd _ _ _))

/-- The underlying scheme morphism of `structureConstantsPoint q` is the morphism into the fibre
product given by `q` and the structure morphism to `S`. -/
@[simp]
theorem toScheme_map_structureConstantsPoint (U : BigFppfOver B S hS)
    (q : (BigFppfOver.toScheme B S hS).obj U ⟶ structureConstantsSpec.{u} d) :
    (BigFppfOver.toScheme B S hS).map (structureConstantsPoint B S hS d U q) =
      pullback.lift q (B.inclusion.map U.hom) (specULiftZIsTerminal.hom_ext _ _) :=
  rfl

/-- The underlying scheme morphism of `structureConstantsPoint q`, followed by the projection to
the scheme of structure constants, is `q`. -/
@[simp]
theorem toScheme_map_structureConstantsPoint_comp_fst (U : BigFppfOver B S hS)
    (q : (BigFppfOver.toScheme B S hS).obj U ⟶ structureConstantsSpec.{u} d) :
    (BigFppfOver.toScheme B S hS).map (structureConstantsPoint B S hS d U q) ≫
        structureConstantsBaseChangeFst.{u} S d = q :=
  pullback.lift_fst _ _ _

/-- The base change in the big fppf site of `S` of the universal cover
`universalFiniteCoverMapOver` along `structureConstantsPoint q`, carried to schemes, is a base
change of the universal cover `universalFiniteCoverMap` over the integers along `q`. -/
theorem isPullback_toScheme_map_pullback_snd_structureConstantsPoint (U : BigFppfOver B S hS)
    (q : (BigFppfOver.toScheme B S hS).obj U ⟶ structureConstantsSpec.{u} d) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map
          (pullback.fst (universalFiniteCoverMapOver B S hS d)
            (structureConstantsPoint B S hS d U q)) ≫
        pullback.fst (universalFiniteCoverMap.{u} d) (structureConstantsBaseChangeFst.{u} S d))
      ((BigFppfOver.toScheme B S hS).map
        (pullback.snd (universalFiniteCoverMapOver B S hS d)
          (structureConstantsPoint B S hS d U q)))
      (universalFiniteCoverMap.{u} d) q := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsite := (IsPullback.of_hasPullback (universalFiniteCoverMapOver B S hS d)
    (structureConstantsPoint B S hS d U q)).map (BigFppfOver.toScheme B S hS)
  have hbase := IsPullback.of_hasPullback (universalFiniteCoverMap.{u} d)
    (structureConstantsBaseChangeFst.{u} S d)
  have hpaste := hsite.paste_horiz hbase
  rwa [toScheme_map_structureConstantsPoint_comp_fst] at hpaste

/-- Every degree-`d` cover of an object of the big fppf site whose underlying scheme is the
spectrum of a field is a base change of the universal degree-`d` cover over `S`: there is a
point of the scheme of structure constants over `S` and an isomorphism of the site identifying
the base change of the universal cover along it with the given cover, over the base. -/
theorem exists_structureConstantsPoint_iso_of_isFieldObject (y : FiniteCover B S hS d)
    (hy : IsFieldObject B S hS y.U) :
    ∃ (h : y.U ⟶ structureConstantsOver B S hS d)
      (e : pullback (universalFiniteCoverMapOver B S hS d) h ≅ y.Z),
      e.hom ≫ y.q = pullback.snd (universalFiniteCoverMapOver B S hS d) h := by
  obtain ⟨k, hk, ⟨ek⟩⟩ := hy
  let : Field k := hk
  let : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      ((BigFppfOver.toScheme B S hS).map y.q) d := y.finiteLocallyFree
  obtain ⟨pt, g, hpb⟩ := exists_point_isPullback_universalFiniteCoverMap_of_field
    ((BigFppfOver.toScheme B S hS).map y.q ≫ ek.hom) d
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.comp_isIso _ ek.hom d)
  have hiso : IsPullback (𝟙 ((BigFppfOver.toScheme B S hS).obj y.Z))
      ((BigFppfOver.toScheme B S hS).map y.q)
      ((BigFppfOver.toScheme B S hS).map y.q ≫ ek.hom) ek.hom :=
    IsPullback.of_horiz_isIso ⟨(Category.id_comp _)⟩
  have hcover : IsPullback g ((BigFppfOver.toScheme B S hS).map y.q)
      (universalFiniteCoverMap.{u} d) (ek.hom ≫ pt) := by
    simpa only [Category.id_comp] using hiso.paste_horiz hpb
  have hpt := isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d y.U
    (ek.hom ≫ pt)
  have key : (ObjectProperty.isoMk _ (hcover.isoIsPullback _ _ hpt).symm).hom ≫ y.q.left =
      (pullback.snd (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d y.U (ek.hom ≫ pt))).left :=
    ObjectProperty.hom_ext _ (hcover.isoIsPullback_inv_snd _ _ hpt)
  refine ⟨_, Over.isoMk (ObjectProperty.isoMk _ (hcover.isoIsPullback _ _ hpt).symm) ?_,
    Over.OverMorphism.ext key⟩
  rw [← Over.w y.q, ← Over.w (pullback.snd _ _), ← Category.assoc, key]

/-! ### Surjectivity -/

/-- The atlas candidate of `ℋ_d` is surjective on objects, in the sense of Stacks 06D4: a
degree-`d` finite locally free cover of an object of the big fppf site whose underlying scheme is
the spectrum of a field is the base change of the universal cover along a point of the scheme of
structure constants over `S`. -/
theorem isSurjectiveOnObjects_finiteCoverUniversalAtlas :
    IsSurjectiveOnObjects B S hS
      (schemeFibredCategory B S hS (structureConstantsOver B S hS d)).val.p
      (finiteCoverFibered B S hS d).val.p
      (CatFiberedInGroupoids.homFunctor (finiteCoverUniversalAtlas B S hS d)) := by
  intro U hU y hy
  subst hy
  obtain ⟨h, e, he⟩ := exists_structureConstantsPoint_iso_of_isFieldObject B S hS d y hU
  refine ⟨y.U, hU, 𝟙 y.U, Over.mk h, rfl, ⟨𝟙 y.U, e.hom, ?_⟩, ?_⟩
  · refine (IsPullback.of_id_fst (f := y.q)).of_iso e.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact e.inv_hom_id.symm
    · change y.q ≫ 𝟙 y.U = e.inv ≫ pullback.snd (universalFiniteCoverMapOver B S hS d) h
      rw [Category.comp_id, ← he, Iso.inv_hom_id_assoc]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp (𝟙 y.U)).symm
  · exact IsHomLift.of_fac' _ (𝟙 y.U) _ rfl rfl rfl

/-- The atlas candidate `finiteCoverUniversalAtlas` of `ℋ_d` is surjective: it has the relative
property of Stacks 03YK for surjectivity of morphisms of algebraic spaces. -/
theorem hasRelativeProperty_surjective_finiteCoverUniversalAtlas :
    HasRelativeProperty.{u, u, u + 1, u + 1} B S hS
      (Space.surjectiveMorphismProperty B S hS) (finiteCoverUniversalAtlas B S hS d)
      (isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas B S hS d) :=
  (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u + 1} B S hS
      (finiteCoverUniversalAtlas B S hS d)
      (isRepresentableByAlgebraicSpaces_finiteCoverUniversalAtlas B S hS d)).mp
    (isSurjectiveOnObjects_finiteCoverUniversalAtlas B S hS d)

end AlgebraicGeometry.Stack

end
