module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverAtlasSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.ThickeningPointCover

/-!
# The atlas candidate of `ℋ_d` is formally smooth on objects

Let `B` be a big fppf site, `S` a scheme contained in it and `d` a positive natural number. The
1-morphism `AlgebraicGeometry.Stack.finiteCoverUniversalAtlas` from the category represented by
the scheme of structure constants over `S` into the category `ℋ_d` of degree-`d` finite locally
free covers is formally smooth on objects in the sense of **Stacks 06D0**.

Unwinding the condition through
`AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_exists_homLift`, what has to be solved is
this lifting problem: given a first-order thickening `i : U ⟶ U'` of affine objects of the site,
a point `U ⟶ X` of the scheme of structure constants over `S`, and a degree-`d` cover of `U'`
whose restriction to `U` is the cover that point defines, extend the point to `U'` so that the
cover it defines over `U'` is the given one. Read in the big fppf site of `S`, that is exactly
`AlgebraicGeometry.FiniteFreeAlgebra.exists_point_isPullback_universalFiniteCoverMap_of_thickening`
applied there.

## Main results

* `AlgebraicGeometry.Stack.structureConstantsPoint_toScheme_map`: every morphism of the site into
  the scheme of structure constants over `S` is the one attached to its underlying morphism of
  schemes into the scheme of structure constants.
* `AlgebraicGeometry.Stack.comp_structureConstantsPoint`: those morphisms are compatible with
  precomposition.
* `AlgebraicGeometry.Stack.hasFirstOrderObjectLifts_finiteCoverUniversalAtlas`: the atlas
  candidate solves every first-order lifting problem.
* `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_finiteCoverUniversalAtlas`: the atlas
  candidate is formally smooth on objects.

## Implementation notes

The passage between the site and schemes is the one of
`AlgebraicGeometry.Stack.exists_structureConstantsPoint_iso_of_isFieldObject`: a morphism of the
site into the scheme of structure constants over `S` is a gap-filler into a fibre product, so it
is determined by its component on the scheme of structure constants together with its structure
morphism to `S`, and the base change of the universal cover along it is carried to schemes by
`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme`. The two lemmas on
`AlgebraicGeometry.Stack.structureConstantsPoint` recorded here are what make that determination
usable: the first says the correspondence is surjective, the second that it is compatible with
composition, and together they turn the restriction statement produced over schemes into the
equation `i ≫ h = A.hom` that the lifting problem asks for.

The cover component of the vertical identification is produced as in the surjectivity file, by
comparing two cartesian squares over the same cospan with
`CategoryTheory.IsPullback.isoIsPullback` and lifting the resulting isomorphism of schemes to the
site with `CategoryTheory.ObjectProperty.isoMk` and `CategoryTheory.Over.isoMk`. The commuting
triangle of the lifting problem is checked on underlying schemes, the functor to schemes being
faithful, through the universal property of the cartesian square produced over `U'`.

No `@[stacks]` attribute is placed here. **Stacks 06D0** is the definition of formal smoothness
on objects, and its tag sits on `AlgebraicGeometry.Stack.IsFormallySmoothOnObjects`. The
presentation clause of **Stacks 026O** asks three things of the atlas candidate —
representability by algebraic spaces, surjectivity and smoothness — and
`AlgebraicGeometry.Stack.isAlgebraicStack_of_onObjects_schemePoint` assembles smoothness from
formal smoothness on objects together with limit preservation on objects.

## References

* [Stacks Project, Tag 026O](https://stacks.math.columbia.edu/tag/026O)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 05YM](https://stacks.math.columbia.edu/tag/05YM)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry.FiniteFreeAlgebra

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ) [NeZero d]

/-- The underlying scheme morphism of a morphism of the site into the scheme of structure
constants over `S`, followed by the projection to `S`, is the structure morphism of its
source. -/
theorem toScheme_map_comp_structureConstantsBaseChangeSnd {U : BigFppfOver B S hS}
    (h : U ⟶ structureConstantsOver B S hS d) :
    (BigFppfOver.toScheme B S hS).map h ≫ structureConstantsBaseChangeSnd.{u} S d =
      B.inclusion.map U.hom := by
  simpa using congrArg (fun k : U.left ⟶ B.obj hS => B.inclusion.map k) (Over.w h)

/-- **Every morphism of the site into the scheme of structure constants over `S` is the one
attached to its own component on the scheme of structure constants.** -/
theorem structureConstantsPoint_toScheme_map {U : BigFppfOver B S hS}
    (h : U ⟶ structureConstantsOver B S hS d) :
    structureConstantsPoint B S hS d U
      ((BigFppfOver.toScheme B S hS).map h ≫ structureConstantsBaseChangeFst.{u} S d) = h := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [toScheme_map_structureConstantsPoint]
  exact pullback.hom_ext (pullback.lift_fst _ _ _)
    ((pullback.lift_snd _ _ _).trans
      (toScheme_map_comp_structureConstantsBaseChangeSnd B S hS d h).symm)

/-- The morphisms of the site into the scheme of structure constants over `S` attached to scheme
morphisms are compatible with precomposition. -/
theorem comp_structureConstantsPoint {U V : BigFppfOver B S hS} (i : U ⟶ V)
    (q : (BigFppfOver.toScheme B S hS).obj V ⟶ structureConstantsSpec.{u} d) :
    i ≫ structureConstantsPoint B S hS d V q =
      structureConstantsPoint B S hS d U ((BigFppfOver.toScheme B S hS).map i ≫ q) := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, toScheme_map_structureConstantsPoint,
    toScheme_map_structureConstantsPoint]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    exact congrArg (fun k : U.left ⟶ B.obj hS => B.inclusion.map k) (Over.w i)

/-- The base change of the universal cover along a morphism `h` of the site into the scheme of
structure constants over `S` is carried to schemes onto a base change of the universal cover
along the underlying scheme morphism of `h`. -/
private theorem isPullback_toScheme_map_pullback_snd_universalFiniteCoverMapOver
    {U : BigFppfOver B S hS}
    (h : U ⟶ structureConstantsOver B S hS d) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map (pullback.fst (universalFiniteCoverMapOver B S hS d) h) ≫
        pullback.fst (universalFiniteCoverMap.{u} d) (structureConstantsBaseChangeFst.{u} S d))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd (universalFiniteCoverMapOver B S hS d) h))
      (universalFiniteCoverMap.{u} d)
      ((BigFppfOver.toScheme B S hS).map h ≫ structureConstantsBaseChangeFst.{u} S d) := by
  have h' := isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d U
    ((BigFppfOver.toScheme B S hS).map h ≫ structureConstantsBaseChangeFst.{u} S d)
  rwa [structureConstantsPoint_toScheme_map B S hS d h] at h'

/-- A cartesian square of schemes exhibiting `p : Z ⟶ V` as the base change of the universal
cover along `q` lifts to an isomorphism over `V` in the site, from the base change of the
universal cover along `structureConstantsPoint B S hS d V q` onto `Z`. -/
private theorem exists_iso_pullback_structureConstantsPoint {V Z : BigFppfOver B S hS} (p : Z ⟶ V)
    (q : (BigFppfOver.toScheme B S hS).obj V ⟶ structureConstantsSpec.{u} d)
    {g : (BigFppfOver.toScheme B S hS).obj Z ⟶ (specCover (universalStructure.{u} d)).left}
    (hg : IsPullback g ((BigFppfOver.toScheme B S hS).map p) (universalFiniteCoverMap.{u} d) q) :
    ∃ ε : pullback (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d V q) ≅ Z,
      ε.hom ≫ p = pullback.snd (universalFiniteCoverMapOver B S hS d)
          (structureConstantsPoint B S hS d V q) ∧
        (BigFppfOver.toScheme B S hS).map ε.hom = (hg.isoIsPullback _ _
          (isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d V q)).inv := by
  have hpt := isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d V q
  have key : (ObjectProperty.isoMk _ (hg.isoIsPullback _ _ hpt).symm).hom ≫ p.left =
      (pullback.snd (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d V q)).left :=
    ObjectProperty.hom_ext _ (hg.isoIsPullback_inv_snd _ _ hpt)
  refine ⟨Over.isoMk (ObjectProperty.isoMk _ (hg.isoIsPullback _ _ hpt).symm) ?_,
    Over.OverMorphism.ext key, rfl⟩
  rw [← Over.w p, ← Over.w (pullback.snd (universalFiniteCoverMapOver B S hS d)
    (structureConstantsPoint B S hS d V q)), ← Category.assoc, key]

/-- Over a cartesian square of schemes exhibiting a cover `Y` as the base change of the universal
cover along `q'`, the base change of the universal cover along `Over.homMk i hb`, followed by the
identification `ε` of the site, is the morphism `k` of covers whose two components match. -/
private theorem finiteCoverPointMap_g_comp_iso_hom {A : Over (structureConstantsOver B S hS d)}
    {Y : FiniteCover B S hS d} (i : A.left ⟶ Y.U)
    (q' : (BigFppfOver.toScheme B S hS).obj Y.U ⟶ structureConstantsSpec.{u} d)
    (hb : i ≫ structureConstantsPoint B S hS d Y.U q' = A.hom)
    {g' : (BigFppfOver.toScheme B S hS).obj Y.Z ⟶ (specCover (universalStructure.{u} d)).left}
    (hg' : IsPullback g' ((BigFppfOver.toScheme B S hS).map Y.q) (universalFiniteCoverMap.{u} d)
      q')
    (ε : pullback (universalFiniteCoverMapOver B S hS d)
      (structureConstantsPoint B S hS d Y.U q') ≅ Y.Z)
    (hεmap : (BigFppfOver.toScheme B S hS).map ε.hom = (hg'.isoIsPullback _ _
      (isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d Y.U q')).inv)
    {k : pullback (universalFiniteCoverMapOver B S hS d) A.hom ⟶ Y.Z}
    (hw : k ≫ Y.q = pullback.snd (universalFiniteCoverMapOver B S hS d) A.hom ≫ i)
    (hk : (BigFppfOver.toScheme B S hS).map k ≫ g' =
      (BigFppfOver.toScheme B S hS).map (pullback.fst (universalFiniteCoverMapOver B S hS d)
        A.hom) ≫ pullback.fst (universalFiniteCoverMap.{u} d)
          (structureConstantsBaseChangeFst.{u} S d)) :
    (finiteCoverPointMap (universalFiniteCoverMapOver B S hS d)
        (isFiniteLocallyFreeOfRank_universalFiniteCoverMapOver B S hS d)
        (Over.homMk i hb : A ⟶ Over.mk (structureConstantsPoint B S hS d Y.U q'))).g ≫ ε.hom =
      k := by
  have hpt := isPullback_toScheme_map_pullback_snd_structureConstantsPoint B S hS d Y.U q'
  have hefst : (BigFppfOver.toScheme B S hS).map ε.hom ≫ g' =
      (BigFppfOver.toScheme B S hS).map (pullback.fst (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d Y.U q')) ≫
          pullback.fst (universalFiniteCoverMap.{u} d)
            (structureConstantsBaseChangeFst.{u} S d) := by
    rw [hεmap]
    exact IsPullback.isoIsPullback_inv_fst _ _ hg' hpt
  have hesnd : (BigFppfOver.toScheme B S hS).map ε.hom ≫ (BigFppfOver.toScheme B S hS).map Y.q =
      (BigFppfOver.toScheme B S hS).map (pullback.snd (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d Y.U q')) := by
    rw [hεmap]
    exact IsPullback.isoIsPullback_inv_snd _ _ hg' hpt
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  refine ((BigFppfOver.toScheme B S hS).map_comp _ _).trans ?_
  refine hg'.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hefst).trans ?_)
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ _) (((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans
      (congrArg (BigFppfOver.toScheme B S hS).map
        (finiteCoverPointMap_g_comp_fst (universalFiniteCoverMapOver B S hS d) _ _)))).trans ?_
    exact hk.symm
  · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hesnd).trans ?_)
    refine ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ?_
    refine (congrArg (BigFppfOver.toScheme B S hS).map
      (finiteCoverPointMap_g_comp_snd (universalFiniteCoverMapOver B S hS d) _ _)).trans ?_
    exact (congrArg (BigFppfOver.toScheme B S hS).map hw.symm).trans
      ((BigFppfOver.toScheme B S hS).map_comp _ _)

/-- **The atlas candidate of `ℋ_d` solves every first-order lifting problem on objects.** Given a
first-order thickening of affine objects of the site, a point of the scheme of structure
constants over `S` on its closed part and a degree-`d` cover of its ambient part restricting to
the cover that point defines, the point extends to the ambient part so that the cover it defines
is the given one. -/
theorem hasFirstOrderObjectLifts_finiteCoverUniversalAtlas :
    HasFirstOrderObjectLifts B S hS (finiteCoverUniversalAtlas B S hS d) := by
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  rintro U U' i hU hU' hi ⟨A, rfl⟩ ⟨P, rfl⟩ a ha
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj P.U) := hU'
  have haf : a.f = i := by
    have h : (finiteCoverFibered B S hS d).val.p.map a = 𝟙 _ ≫ i ≫ 𝟙 _ :=
      IsHomLift.fac' (finiteCoverFibered B S hS d).val.p i a
    exact (by simpa using h : (finiteCoverFibered B S hS d).val.p.map a = i)
  have hsq : IsPullback a.g
      (pullback.snd (universalFiniteCoverMapOver B S hS d) A.hom) P.q i := by
    rw [← haf]
    exact a.square
  obtain ⟨q', g', hq', hg', hcompat⟩ :=
    exists_point_isPullback_universalFiniteCoverMap_of_thickening d hi P.finiteLocallyFree
      (hsq.map (BigFppfOver.toScheme B S hS))
      (isPullback_toScheme_map_pullback_snd_universalFiniteCoverMapOver B S hS d A.hom)
  have hb : i ≫ structureConstantsPoint B S hS d P.U q' = A.hom :=
    (comp_structureConstantsPoint B S hS d (U := A.left) (V := P.U) i q').trans
      ((congrArg (structureConstantsPoint B S hS d A.left) hq').trans
        (structureConstantsPoint_toScheme_map B S hS d A.hom))
  obtain ⟨ε, hε, hεmap⟩ := exists_iso_pullback_structureConstantsPoint B S hS d P.q q' hg'
  refine ⟨⟨Over.mk (structureConstantsPoint B S hS d P.U q'), rfl⟩, Over.homMk i hb,
    ⟨𝟙 P.U, ε.hom, ?_⟩, ?_, ?_, ?_⟩
  · refine (IsPullback.of_id_fst (f := P.q)).of_iso ε.symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · exact ε.inv_hom_id.symm
    · change P.q ≫ 𝟙 P.U = ε.inv ≫ pullback.snd (universalFiniteCoverMapOver B S hS d)
        (structureConstantsPoint B S hS d P.U q')
      rw [Category.comp_id, ← hε, Iso.inv_hom_id_assoc]
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.id_comp (𝟙 P.U)).symm
  · exact IsHomLift.of_fac' _ i _ rfl rfl rfl
  · exact IsHomLift.of_fac' _ (𝟙 P.U) _ rfl rfl rfl
  · exact FiniteCover.Hom.ext ((Category.comp_id i).trans haf.symm)
      (finiteCoverPointMap_g_comp_iso_hom B S hS d i q' hb hg' ε hεmap hsq.w hcompat)

/-- **Stacks 06D0 for the atlas candidate of `ℋ_d`.** The 1-morphism from the category
represented by the scheme of structure constants over `S` into the category `ℋ_d` of degree-`d`
finite locally free covers is formally smooth on objects. -/
theorem isFormallySmoothOnObjects_finiteCoverUniversalAtlas :
    IsFormallySmoothOnObjects B S hS
      (schemeFibredCategory B S hS (structureConstantsOver B S hS d))
      (finiteCoverFibered B S hS d) (finiteCoverUniversalAtlas B S hS d) :=
  isFormallySmoothOnObjects_of_exists_homLift B S hS (finiteCoverUniversalAtlas B S hS d)
    (hasFirstOrderObjectLifts_finiteCoverUniversalAtlas B S hS d)

end AlgebraicGeometry.Stack

end
