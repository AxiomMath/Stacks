module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.QcSeparatedObjectColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite

/-!
# The level side of the site crossing of Stacks 09YQ

[Stacks, Tag 0EYL] presents the small affine étale site of a limit `X = lim X_i` of schemes with
affine transition morphisms as a colimit of a strict inverse system of sites
`Stacks.EtaleCohomology.AffineLimitCohomology.sys`, whose levels are categories of *chosen
pullback models* and whose canonical functors to the site of the limit are
`Stacks.EtaleCohomology.AffineLimitCohomology.toLimitSmall`. That system lives on the
size-bounded sites of [Stacks, Tag 021B]; the statements of [Stacks, Tag 09YQ] are about
*Mathlib's* small étale sites `AlgebraicGeometry.Scheme.smallEtaleTopology`.

This file identifies `toLimitSmall i`, composed with the two bounded-site crossings and the
embedding into Mathlib's site, with **base change along the projection `X → X_i` of the limit cone
on Mathlib's small étale sites**.

## Main definitions

* `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` — **the level-side
  identification**: for every level `i` of the system of [Stacks, Tag 0EYL],

  `toLimitSmall i ⋙ limitToSmallEtale ⋙ SmallEtale.toEtaleSite ≅`
  `levelToSmallEtale i ⋙ SmallEtale.toEtaleSite ⋙ smallEtaleBaseChange (c.π.app i)`

  as functors from the level to Mathlib's small étale site of the limit.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelRestrictionIso` — its consequence on sheaves:
  restriction of a sheaf on Mathlib's small étale site of the limit to a level is the direct image
  along the projection of the cone, restricted to the bounded small étale site of `X_i` and then
  to the level.
* `Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition` — the
  transition coherence: the two readings of a level through the identification agree up to a
  canonical isomorphism, since base change along two projections of the cone composes only up to
  the associativity of fibre products.

## Implementation notes

A level of `Stacks.EtaleCohomology.AffineLimitCohomology.sys` is a category of chosen pullback
models over a *later* stage, and `(affineEtaleSiteColimit …).toLimit i` reads off the stored
object over the limit, so `toLimitSmall i` is not literally a fibre-product construction. The
field `toLimit_isPullback` exhibits the stored object over the limit, with the stored projection
`toLimitFst`, as a fibre product of the level object along `c.π.app i`. Base change on Mathlib's
site is `CategoryTheory.MorphismProperty.Over.pullback`, the *chosen* fibre product, so the
comparison is `CategoryTheory.IsPullback.isoPullback`.

`AlgebraicGeometry.Scheme.Etale` is `CategoryTheory.MorphismProperty.Over` at the property
`AlgebraicGeometry.Etale`, and a goal mentioning an object of `Scheme.Etale` is not type-correct
under `implicit` transparency, so even `rw [Category.assoc]` fails on it. Hence
`levelCrossing_naturality_fst` and `levelCrossing_naturality_snd` are stated entirely inside
`AlgebraicGeometry.Scheme`, and the naturality square is reduced to them by the `rfl`-lemmas
`comp_left_etale`, `levelCrossingComponent_hom_left`, `levelCrossing_lhs_map_left` and
`levelCrossing_rhs_map_left`.

`comp_left_etale` is stated at a universe variable `w` rather than at `max u v`: with `max u v`
the elaborator would have to solve `max ?u ?v =?= max u v` when the lemma is used.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe wA vA w v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex levelToSmallEtale)

/-- Composition in Mathlib's small étale site is composition of the underlying morphisms of
schemes. -/
theorem comp_left_etale {Z : AlgebraicGeometry.Scheme.{w}} {A A' A'' : Z.Etale}
    (a : A ⟶ A') (b : A' ⟶ A'') : (a ≫ b).left = a.left ≫ b.left := rfl

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]

/-! ### The two sides of the square, read on schemes -/

/-- The underlying scheme of the image of a level object in the small affine étale site of its
own stage `X_i`. -/
abbrev levelToScheme (i : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C i ⥤ AlgebraicGeometry.Scheme.{max u v} :=
  ((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor ⋙
    AlgebraicGeometry.SmallAffineEtale.toScheme B (D.obj (levelIndex D c B hD hX hc i)) (hD _)

/-- The structure morphism to `X_i` of the image of a level object in the small affine étale site
of its own stage. -/
abbrev levelStruct (i : (sys D c B hD hX hc).I) (Y : (sys D c B hD hX hc).C i) :
    (levelToScheme D c B hD hX hc i).obj Y ⟶ D.obj (levelIndex D c B hD hX hc i) :=
  affineEtaleStructureMorphism D B hD _
    (((affineEtaleSiteColimit D c B hD hX hc).levelEquiv i).functor.obj Y)

/-- The underlying scheme of the image of a level object in the small affine étale site of the
limit. -/
abbrev limitToScheme (i : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C i ⥤ AlgebraicGeometry.Scheme.{max u v} :=
  (affineEtaleSiteColimit D c B hD hX hc).toLimit i ⋙
    AlgebraicGeometry.SmallAffineEtale.toScheme B c.pt hX

/-- The structure triangle of a morphism of a level, over the stage `X_i`, read on schemes. -/
theorem levelStruct_w (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    (levelToScheme D c B hD hX hc i).map k ≫ levelStruct D c B hD hX hc i Y' =
      levelStruct D c B hD hX hc i Y :=
  MorphismProperty.Over.w
    ((AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)).map
      ((levelToSmallEtale D c B hD hX hc i).map k))

/-- The structure triangle of a morphism of a level, over the limit `X`, read on schemes. -/
theorem limitStruct_w (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    (limitToScheme D c B hD hX hc i).map k ≫
        limitAffineEtaleStructureMorphism D c B hX
          (((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y') =
      limitAffineEtaleStructureMorphism D c B hX
        (((affineEtaleSiteColimit D c B hD hX hc).toLimit i).obj Y) :=
  MorphismProperty.Over.w
    ((toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).map k)

/-- Base change of a morphism of a level along the projection `X → X_i` of the limit cone, read
on the chosen fibre products in `AlgebraicGeometry.Scheme`. It is what base change on Mathlib's
small étale site does to the underlying morphism of schemes. -/
abbrev levelBaseChangeMap (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    pullback (levelStruct D c B hD hX hc i Y) (c.π.app (levelIndex D c B hD hX hc i)) ⟶
      pullback (levelStruct D c B hD hX hc i Y') (c.π.app (levelIndex D c B hD hX hc i)) :=
  pullback.lift
    (pullback.fst (levelStruct D c B hD hX hc i Y)
        (c.π.app (levelIndex D c B hD hX hc i)) ≫ (levelToScheme D c B hD hX hc i).map k)
    (pullback.snd (levelStruct D c B hD hX hc i Y)
      (c.π.app (levelIndex D c B hD hX hc i)))
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => pullback.fst (levelStruct D c B hD hX hc i Y)
          (c.π.app (levelIndex D c B hD hX hc i)) ≫ z)
        (levelStruct_w D c B hD hX hc i k)).trans pullback.condition))

/-! ### The identification -/

/-- The component of the level-side identification at an object of a level: the object stored
over the limit is the chosen fibre product of the level object along `c.π.app i`, via the
fibre-product square `Stacks.EtaleCohomology.AffineEtaleSiteColimit.toLimit_isPullback`. -/
def levelCrossingComponent (i : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C i) :
    (toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).obj Y ≅
      (levelToSmallEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i))).obj Y :=
  MorphismProperty.Over.isoMk
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y).isoPullback)
    (IsPullback.isoPullback_hom_snd _)

/-- The component of the identification, read on underlying schemes. -/
theorem levelCrossingComponent_hom_left (i : (sys D c B hD hX hc).I)
    (Y : (sys D c B hD hX hc).C i) :
    (levelCrossingComponent D c B hD hX hc i Y).hom.left =
      ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y).isoPullback.hom :=
  rfl

/-- The left-hand side of the identification acts on underlying schemes by `toLimit`. -/
theorem levelCrossing_lhs_map_left (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    ((toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).map k).left =
      (limitToScheme D c B hD hX hc i).map k :=
  rfl

/-- The right-hand side of the identification acts on underlying schemes by
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeMap`. -/
theorem levelCrossing_rhs_map_left (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    ((levelToSmallEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i))).map k).left =
      levelBaseChangeMap D c B hD hX hc i k :=
  rfl

/-- The first projection of the naturality square of the identification, stated inside
`AlgebraicGeometry.Scheme`. -/
theorem levelCrossing_naturality_fst (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    ((limitToScheme D c B hD hX hc i).map k ≫
        ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y').isoPullback.hom) ≫
      pullback.fst (levelStruct D c B hD hX hc i Y')
        (c.π.app (levelIndex D c B hD hX hc i)) =
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y).isoPullback.hom ≫
        levelBaseChangeMap D c B hD hX hc i k) ≫
      pullback.fst (levelStruct D c B hD hX hc i Y')
        (c.π.app (levelIndex D c B hD hX hc i)) := by
  rw [Category.assoc, IsPullback.isoPullback_hom_fst, Category.assoc, levelBaseChangeMap,
    pullback.lift_fst, ← Category.assoc, IsPullback.isoPullback_hom_fst]
  exact ((affineEtaleSiteColimit D c B hD hX hc).toLimitFst i).naturality k

/-- The second projection of the naturality square of the identification, stated inside
`AlgebraicGeometry.Scheme`. -/
theorem levelCrossing_naturality_snd (i : (sys D c B hD hX hc).I)
    {Y Y' : (sys D c B hD hX hc).C i} (k : Y ⟶ Y') :
    ((limitToScheme D c B hD hX hc i).map k ≫
        ((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y').isoPullback.hom) ≫
      pullback.snd (levelStruct D c B hD hX hc i Y')
        (c.π.app (levelIndex D c B hD hX hc i)) =
    (((affineEtaleSiteColimit D c B hD hX hc).toLimit_isPullback i Y).isoPullback.hom ≫
        levelBaseChangeMap D c B hD hX hc i k) ≫
      pullback.snd (levelStruct D c B hD hX hc i Y')
        (c.π.app (levelIndex D c B hD hX hc i)) := by
  rw [Category.assoc, IsPullback.isoPullback_hom_snd, Category.assoc, levelBaseChangeMap,
    pullback.lift_snd, IsPullback.isoPullback_hom_snd]
  exact limitStruct_w D c B hD hX hc i k

/-- **The level side of the site crossing of [Stacks, Tag 09YQ].** Let `(X_i)` be an inverse
system of schemes over a nonempty directed index with affine transition morphisms, all objects of
a big étale site `B`, and let `X = lim X_i`. For every level `i` of the system of sites of
[Stacks, Tag 0EYL], the canonical functor
`Stacks.EtaleCohomology.AffineLimitCohomology.toLimitSmall i` to the (raised, affine) small étale
site of the limit, followed by the two bounded-site crossings
`Stacks.EtaleCohomology.AffineLimitCohomology.limitToSmallEtale` and
`AlgebraicGeometry.SmallEtale.toEtaleSite`, **is base change along the projection `X → X_i` of
the limit cone on Mathlib's small étale sites**, the level being read on the small étale site of
`X_i` by `Stacks.EtaleCohomology.QcSeparatedColimit.levelToSmallEtale` and
`AlgebraicGeometry.SmallEtale.toEtaleSite`. -/
def levelCrossingIso (i : (sys D c B hD hX hc).I) :
    toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX ≅
      levelToSmallEtale D c B hD hX hc i ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i)) := by
  refine NatIso.ofComponents (levelCrossingComponent D c B hD hX hc i) fun k => ?_
  refine MorphismProperty.Over.Hom.ext ?_
  rw [comp_left_etale, comp_left_etale, levelCrossingComponent_hom_left,
    levelCrossingComponent_hom_left, levelCrossing_lhs_map_left, levelCrossing_rhs_map_left]
  exact pullback.hom_ext (levelCrossing_naturality_fst D c B hD hX hc i k)
    (levelCrossing_naturality_snd D c B hD hX hc i k)

/-! ### The consequence on sheaves -/

section Sheaves

variable (A : Type wA) [Category.{vA} A]

/-- The level crossing followed by base change along the projection of the cone: the right-hand
side of `Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso`. -/
abbrev levelBaseChangeCrossing (i : (sys D c B hD hX hc).I) :
    (sys D c B hD hX hc).C i ⥤ (c.pt).Etale :=
  levelToSmallEtale D c B hD hX hc i ⋙
    AlgebraicGeometry.SmallEtale.toEtaleSite B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
    Stacks.EtaleCohomology.smallEtaleBaseChange
      (c.π.app (levelIndex D c B hD hX hc i))

/-- Base change along the projection `X → X_i` of the limit cone is a morphism of Mathlib's small
étale sites. -/
theorem isContinuous_limitProjectionBaseChange (i : (sys D c B hD hX hc).I) :
    (Stacks.EtaleCohomology.smallEtaleBaseChange
        (c.π.app (levelIndex D c B hD hX hc i))).IsContinuous
      (AlgebraicGeometry.Scheme.smallEtaleTopology (D.obj (levelIndex D c B hD hX hc i)))
      (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) :=
  Stacks.EtaleCohomology.smallEtaleBaseChange_isContinuous
    (c.π.app (levelIndex D c B hD hX hc i))

/-- The embedding forgetting the size cutoff, followed by base change along the projection of the
cone, is a morphism of sites. -/
theorem isContinuous_toEtaleSiteBaseChange (i : (sys D c B hD hX hc).I) :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B
        (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
      Stacks.EtaleCohomology.smallEtaleBaseChange
        (c.π.app (levelIndex D c B hD hX hc i))).IsContinuous
      (AlgebraicGeometry.SmallEtale.topology B
        (D.obj (levelIndex D c B hD hX hc i)) (hD _))
      (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) :=
  let := isContinuous_limitProjectionBaseChange D c B hD hX hc i
  Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.Scheme.smallEtaleTopology (D.obj (levelIndex D c B hD hX hc i))) _

/-- The right-hand side of the identification is a morphism of sites. -/
theorem isContinuous_levelBaseChangeCrossing (i : (sys D c B hD hX hc).I) :
    (levelBaseChangeCrossing D c B hD hX hc i).IsContinuous
      ((sys D c B hD hX hc).J i) (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) :=
  let := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
  let := isContinuous_toEtaleSiteBaseChange D c B hD hX hc i
  Functor.isContinuous_comp _ _ _
    (AlgebraicGeometry.SmallEtale.topology B
      (D.obj (levelIndex D c B hD hX hc i)) (hD _)) _

/-- The left-hand side of the identification is a morphism of sites. -/
theorem isContinuous_levelCrossing (i : (sys D c B hD hX hc).I) :
    (toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
      AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).IsContinuous
      ((sys D c B hD hX hc).J i) (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) :=
  let := isContinuous_levelBaseChangeCrossing D c B hD hX hc i
  Functor.isContinuous_of_iso (levelCrossingIso D c B hD hX hc i).symm _ _

/-- **Restriction of a sheaf on Mathlib's small étale site of the limit to a level of
[Stacks, Tag 0EYL].** It is the direct image along the projection `X → X_i` of the limit cone,
restricted to the size-bounded small étale site of `X_i` and then to the level, for sheaves with
values in an arbitrary category `A`. -/
def levelRestrictionIso (i : (sys D c B hD hX hc).I) :
    letI := isContinuous_levelCrossing D c B hD hX hc i
    letI := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
    letI := isContinuous_limitProjectionBaseChange D c B hD hX hc i
    (toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).sheafPushforwardContinuous A
        ((sys D c B hD hX hc).J i)
        (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc i))).sheafPushforwardContinuous A
          (AlgebraicGeometry.Scheme.smallEtaleTopology
            (D.obj (levelIndex D c B hD hX hc i)))
          (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) ⋙
        (AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)).sheafPushforwardContinuous A
          (AlgebraicGeometry.SmallEtale.topology B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _))
          (AlgebraicGeometry.Scheme.smallEtaleTopology
            (D.obj (levelIndex D c B hD hX hc i))) ⋙
        (levelToSmallEtale D c B hD hX hc i).sheafPushforwardContinuous A
          ((sys D c B hD hX hc).J i)
          (AlgebraicGeometry.SmallEtale.topology B
            (D.obj (levelIndex D c B hD hX hc i)) (hD _)) := by
  letI := isContinuous_levelCrossing D c B hD hX hc i
  letI := QcSeparatedColimit.isContinuous_levelToSmallEtale D c B hD hX hc i
  letI := isContinuous_limitProjectionBaseChange D c B hD hX hc i
  letI := isContinuous_toEtaleSiteBaseChange D c B hD hX hc i
  letI := isContinuous_levelBaseChangeCrossing D c B hD hX hc i
  refine Functor.sheafPushforwardContinuousIso (levelCrossingIso D c B hD hX hc i) A
      ((sys D c B hD hX hc).J i) (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt) ≪≫
    (Functor.sheafPushforwardContinuousComp (levelToSmallEtale D c B hD hX hc i)
      (AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _) ⋙
        Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i))) A
      ((sys D c B hD hX hc).J i)
      (AlgebraicGeometry.SmallEtale.topology B
        (D.obj (levelIndex D c B hD hX hc i)) (hD _))
      (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt)).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.sheafPushforwardContinuousComp
        (AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _))
        (Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc i))) A
        (AlgebraicGeometry.SmallEtale.topology B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _))
        (AlgebraicGeometry.Scheme.smallEtaleTopology
          (D.obj (levelIndex D c B hD hX hc i)))
        (AlgebraicGeometry.Scheme.smallEtaleTopology c.pt)).symm
      ((levelToSmallEtale D c B hD hX hc i).sheafPushforwardContinuous A
        ((sys D c B hD hX hc).J i)
        (AlgebraicGeometry.SmallEtale.topology B
          (D.obj (levelIndex D c B hD hX hc i)) (hD _)))

/-! ### The transition coherence -/

/-- The cocone identity of [Stacks, Tag 09YL] for the left-hand side of the identification: the
crossing into Mathlib's small étale site of the limit is compatible with the transition functors
of the system, **on the nose**. -/
theorem levelCrossing_transition {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    (sys D c B hD hX hc).u a ⋙ (toLimitSmall D c B hD hX hc i ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX) =
      toLimitSmall D c B hD hX hc j ⋙ limitToSmallEtale D c B hX ⋙
        AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX := by
  rw [← Functor.assoc, toLimitSmall_transition]

/-- **The transition coherence of the level-side identification.** For an arrow `a : i ⟶ j` of the
index, reading the level `j` through
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` and reading the level `i` through
it after the transition functor `(sys …).u a` agree, up to a canonical isomorphism.

It is not an equality: for the system's own functors the cocone identity holds on the nose
(`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossing_transition`), while base change along
`X → X_i` and base change along `X → X_j` followed by `X_j → X_i` agree only up to the
associativity of fibre products. -/
def levelBaseChangeCrossing_transition {i j : (sys D c B hD hX hc).I} (a : i ⟶ j) :
    (sys D c B hD hX hc).u a ⋙ levelBaseChangeCrossing D c B hD hX hc i ≅
      levelBaseChangeCrossing D c B hD hX hc j :=
  Functor.isoWhiskerLeft ((sys D c B hD hX hc).u a)
      (levelCrossingIso D c B hD hX hc i).symm ≪≫
    eqToIso (levelCrossing_transition D c B hD hX hc a) ≪≫
      levelCrossingIso D c B hD hX hc j

end Sheaves

end Stacks.EtaleCohomology.AffineLimitCohomology

end
