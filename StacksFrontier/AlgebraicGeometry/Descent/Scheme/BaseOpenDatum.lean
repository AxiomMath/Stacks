module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.ChartFamilyOverBase

/-!
# A descent datum over an open of the base

Let `f : X ⟶ S` be a morphism of schemes, let `(V, φ)` be a descent datum relative to `X/S` and
let `T ⊆ S` be an open. There are two descent data attached to `T`: the restriction of `(V, φ)`
to the part of `V` lying over `T`, which is a datum relative to `X/S`, and the pullback of
`(V, φ)` along the square cutting out `T`, which is a datum relative to `X ×_S T / T`. This file
identifies them, and packages the geometry a scheme descending either of them carries.

## Main definitions

* `AlgebraicGeometry.DescentDatum.basePart`: the part of `V` lying over `T`, as a scheme over
  `X ×_S T`.
* `AlgebraicGeometry.DescentDatum.baseDatum`: the pullback of the datum along the square
  `(X ×_S T ⟶ T) ⟶ (X ⟶ S)`, and `AlgebraicGeometry.DescentDatum.baseDatumIso`: the
  identification of its scheme with the part of `V` lying over `T`.
* `AlgebraicGeometry.DescentDatum.baseSourceIso`: the identification of `V_T ×_S X` with
  `V_T ×_T (X ×_S T)`, the sources of the two gluing isomorphisms.
* `AlgebraicGeometry.DescentDatum.BaseChart`: a scheme over `T` descending the datum over `T`,
  with its projection, the fibre-product square over `S` and the invariance of the projection.
* `AlgebraicGeometry.DescentDatum.BaseChart.restrict`: the chart over a smaller open of the
  base, cut out of the given one.

## Main results

* `AlgebraicGeometry.DescentDatum.isPullback_basePart`: the part of `V` lying over `T` is the
  fibre product of `V` with `X ×_S T` over `X`.
* `AlgebraicGeometry.DescentDatum.baseSourceIso_hom_comp_transition`: **the two gluing
  isomorphisms agree**, in the one component where the agreement has content.
* `AlgebraicGeometry.DescentDatum.BaseChart.ofDescended` and
  `AlgebraicGeometry.DescentDatum.BaseChart.toDescended`: a scheme descending the pulled-back
  datum and a chart over `T` are the same thing.
* `AlgebraicGeometry.DescentDatum.BaseChart.descended`: a chart over `T` descends the
  restriction of the datum to the part of `V` lying over `T`.
* `AlgebraicGeometry.DescentDatum.BaseChart.restrictProj_comp_ι`: the projection of the
  restricted chart, followed by the inclusion of the open it lands in, is the inclusion of the
  smaller part of `V` followed by the projection.
* `AlgebraicGeometry.DescentDatum.BaseChart.toBase_preimage_self`: a chart over `T` lies
  entirely over `T`.

## Implementation notes

The part of `V` lying over `T` is `V ×_S T`, hence also `V ×_X (X ×_S T)`, which is the scheme
of the pulled-back datum. The square exhibiting it as the latter is obtained from the square
exhibiting it as the former — `AlgebraicGeometry.isPullback_morphismRestrict` for the structure
morphism `V ⟶ S` — by cancelling the defining square of `X ×_S T`, which is
`CategoryTheory.IsPullback.of_bot`. Both the fibre-product square of a chart and the
fibre-product square of a scheme descending the pulled-back datum are then read off each other
by pasting, respectively cancelling, that same square.

The gluing isomorphisms are compared in the only component where there is something to prove:
the component landing in the scheme of the datum. Composed with the inclusion of that scheme in
`V`, the pulled-back gluing isomorphism is described by
`AlgebraicGeometry.DescentData.PullbackFunctor.gluing` and the restricted one by
`AlgebraicGeometry.DescentDatum.transitionPullbackIso_naturality`; both descriptions are in
terms of `φ` itself, and the two maps `V_T ×_S X ⟶ V ×_S X` they are expressed by agree. The
inclusion being a monomorphism, that is the whole comparison, and the remaining component is
not needed: the invariance of a projection only ever uses this one.

The restriction of a chart to a smaller open of the base is `AlgebraicGeometry.morphismRestrict`
on the structure morphism of the chart. The open of the chart it cuts out is the preimage of the
smaller open, and the part of `V` over the smaller open is identified with the preimage of that
open under the projection by `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`, exactly as for
`AlgebraicGeometry.DescentDatum.Descended.shrink`; no hypothesis on `f` is needed, because the
open is given rather than descended.

## References

* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
* [Stacks Project, Tag 0BTM](https://stacks.math.columbia.edu/tag/0BTM)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

namespace DescentDatum

variable {S X : Scheme.{u}}

attribute [local implicit_reducible] restrictOpen

/-- The pullback functor on descent data for the square cutting out an open of the base. -/
abbrev basePullbackFunctor (f : X ⟶ S) (T : S.Opens) :
    DescentData.PullbackFunctor f (pullback.snd f T.ι) T.ι (pullback.fst f T.ι)
      pullback.condition :=
  DescentData.pullbackFunctor f (pullback.snd f T.ι) T.ι (pullback.fst f T.ι) pullback.condition

variable {f : X ⟶ S} (D : DescentDatum f) (T : S.Opens)

/-! ### The part of the datum lying over an open of the base -/

/-- The part of `V` lying over an open `T` of the base, as a scheme over `X ×_S T`: its two
components are the inclusion into `V` followed by the structure morphism and the structure
morphism of `V` over `S` restricted to `T`. -/
def basePart : (D.baseOpens T).toScheme ⟶ pullback f T.ι :=
  pullback.lift ((D.baseOpens T).ι ≫ D.over.hom) ((D.over.hom ≫ f) ∣_ T) (by
    rw [morphismRestrict_ι, Category.assoc])

/-- The first component of `basePart` is the inclusion into `V` followed by the structure
morphism. -/
@[reassoc (attr := simp)]
lemma basePart_comp_fst :
    D.basePart T ≫ pullback.fst f T.ι = (D.baseOpens T).ι ≫ D.over.hom :=
  pullback.lift_fst _ _ _

/-- The second component of `basePart` is the structure morphism of `V` over `S` restricted to
`T`. -/
@[reassoc (attr := simp)]
lemma basePart_comp_snd :
    D.basePart T ≫ pullback.snd f T.ι = (D.over.hom ≫ f) ∣_ T :=
  pullback.lift_snd _ _ _

/-- **The part of `V` lying over `T` is the fibre product of `V` with `X ×_S T` over `X`.** The
square exhibiting it as `V ×_S T` is the vertical pasting of this square with the defining
square of `X ×_S T`. -/
lemma isPullback_basePart :
    IsPullback (D.baseOpens T).ι (D.basePart T) D.over.hom (pullback.fst f T.ι) := by
  refine IsPullback.of_bot ?_ (D.basePart_comp_fst T).symm (IsPullback.of_hasPullback f T.ι)
  rw [D.basePart_comp_snd T]
  exact (isPullback_morphismRestrict (D.over.hom ≫ f) T).flip

/-! ### The pullback of the datum to the part of `X` over an open of the base -/

/-- **The pullback of a descent datum to the part of `X` lying over an open of the base.** -/
abbrev baseDatum : DescentDatum (pullback.snd f T.ι) :=
  (basePullbackFunctor f T).functor.obj D

/-- **The part of `V` lying over `T`, identified with the scheme of the pulled-back datum.** -/
def baseDatumIso : (D.baseOpens T).toScheme ≅ (D.baseDatum T).over.left :=
  (D.isPullback_basePart T).isoPullback ≪≫
    ((Over.forget (pullback f T.ι)).mapIso ((basePullbackFunctor f T).objIso D)).symm

/-- `baseDatumIso` followed by the identification of the pulled-back scheme with the chosen
fibre product is the isomorphism of the part of `V` over `T` with that fibre product. -/
@[reassoc]
lemma baseDatumIso_hom_comp_objIso :
    (D.baseDatumIso T).hom ≫ ((basePullbackFunctor f T).objIso D).hom.left =
      (D.isPullback_basePart T).isoPullback.hom := by
  rw [baseDatumIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map,
    Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  exact Category.comp_id _

/-- Under `baseDatumIso`, the structure morphism of the pulled-back datum is `basePart`. -/
@[reassoc (attr := simp)]
lemma baseDatumIso_hom_comp_over_hom :
    (D.baseDatumIso T).hom ≫ (D.baseDatum T).over.hom = D.basePart T := by
  have hw : ((basePullbackFunctor f T).objIso D).hom.left ≫
      pullback.snd D.over.hom (pullback.fst f T.ι) = (D.baseDatum T).over.hom :=
    Over.w ((basePullbackFunctor f T).objIso D).hom
  rw [← hw, ← Category.assoc, D.baseDatumIso_hom_comp_objIso T]
  exact (D.isPullback_basePart T).isoPullback_hom_snd

/-- The inverse of `baseDatumIso` followed by the inclusion into `V` is the first projection of
the fibre product `V ×_X (X ×_S T)`. -/
@[reassoc]
lemma baseDatumIso_inv_comp_ι :
    (D.baseDatumIso T).inv ≫ (D.baseOpens T).ι =
      ((basePullbackFunctor f T).objIso D).hom.left ≫
        pullback.fst D.over.hom (pullback.fst f T.ι) := by
  rw [Iso.inv_comp_eq, ← Category.assoc, D.baseDatumIso_hom_comp_objIso T]
  exact (D.isPullback_basePart T).isoPullback_hom_fst.symm

/-- The inverse of `baseDatumIso` followed by `basePart` is the structure morphism of the
pulled-back datum, also after any further morphism. -/
private theorem baseDatumIso_inv_comp_basePart_comp {Z : Scheme.{u}} (g : pullback f T.ι ⟶ Z) :
    (D.baseDatumIso T).inv ≫ D.basePart T ≫ g = (D.baseDatum T).over.hom ≫ g := by
  rw [← D.baseDatumIso_hom_comp_over_hom T, Category.assoc, Iso.inv_hom_id_assoc]

/-- The inverse of `baseDatumIso` followed by the inclusion into `V` and the structure morphism
to `X` is the structure morphism of the pulled-back datum followed by the projection to `X`. -/
@[reassoc]
lemma baseDatumIso_inv_comp_ι_comp_over_hom :
    (D.baseDatumIso T).inv ≫ (D.baseOpens T).ι ≫ D.over.hom =
      (D.baseDatum T).over.hom ≫ pullback.fst f T.ι := by
  rw [← D.basePart_comp_fst T]
  exact D.baseDatumIso_inv_comp_basePart_comp T _


/-- The inverse of `baseDatumIso` followed by the morphism to `T` is the structure morphism of
the pulled-back datum followed by the projection to `T`. -/
@[reassoc]
lemma baseDatumIso_inv_comp_morphismRestrict :
    (D.baseDatumIso T).inv ≫ ((D.over.hom ≫ f) ∣_ T) =
      (D.baseDatum T).over.hom ≫ pullback.snd f T.ι := by
  rw [← D.basePart_comp_snd T]
  exact D.baseDatumIso_inv_comp_basePart_comp T _

/-! ### Comparing the gluing isomorphisms of the two data over an open of the base -/

/-- The structure morphism of the restriction of a datum to the part of `V` over an open of the
base. -/
lemma restrictBaseOpens_over_hom :
    (D.restrictBaseOpens T).over.hom = (D.baseOpens T).ι ≫ D.over.hom := rfl

/-- The projection of `V_T ×_S X` onto `X ×_S T`. -/
def baseSourcePart :
    pullback ((D.restrictBaseOpens T).over.hom ≫ f) f ⟶ pullback f T.ι :=
  pullback.lift (pullback.snd ((D.restrictBaseOpens T).over.hom ≫ f) f)
    (pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ ((D.over.hom ≫ f) ∣_ T))
    (by
      have h := pullback.condition (f := (D.restrictBaseOpens T).over.hom ≫ f) (g := f)
      rw [D.restrictBaseOpens_over_hom T, Category.assoc] at h
      rw [Category.assoc, morphismRestrict_ι]
      exact h.symm)

/-- The first component of `baseSourcePart` is the projection of `V_T ×_S X` to `X`. -/
@[reassoc (attr := simp)]
lemma baseSourcePart_comp_fst :
    D.baseSourcePart T ≫ pullback.fst f T.ι =
      pullback.snd ((D.restrictBaseOpens T).over.hom ≫ f) f :=
  pullback.lift_fst _ _ _

/-- The second component of `baseSourcePart` is the projection of `V_T ×_S X` to `V_T` followed
by the morphism to `T`. -/
@[reassoc (attr := simp)]
lemma baseSourcePart_comp_snd :
    D.baseSourcePart T ≫ pullback.snd f T.ι =
      pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ ((D.over.hom ≫ f) ∣_ T) :=
  pullback.lift_snd _ _ _

/-- `V_T ×_S X`, viewed in `V_T ×_T (X ×_S T)`. -/
def baseSourceHom :
    pullback ((D.restrictBaseOpens T).over.hom ≫ f) f ⟶
      pullback ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) :=
  pullback.lift
    (pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ (D.baseDatumIso T).hom)
    (D.baseSourcePart T)
    (by
      rw [Category.assoc, ← Category.assoc ((D.baseDatumIso T).hom),
        D.baseDatumIso_hom_comp_over_hom T, D.basePart_comp_snd T, D.baseSourcePart_comp_snd T])

/-- The first component of `baseSourceHom` is the projection to `V_T` followed by
`baseDatumIso`. -/
@[reassoc (attr := simp)]
lemma baseSourceHom_comp_fst :
    D.baseSourceHom T ≫
        pullback.fst ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) =
      pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ (D.baseDatumIso T).hom :=
  pullback.lift_fst _ _ _

/-- The second component of `baseSourceHom` is `baseSourcePart`. -/
@[reassoc (attr := simp)]
lemma baseSourceHom_comp_snd :
    D.baseSourceHom T ≫
        pullback.snd ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) =
      D.baseSourcePart T :=
  pullback.lift_snd _ _ _

/-- `V_T ×_T (X ×_S T)`, viewed in `V_T ×_S X`. -/
def baseSourceInv :
    pullback ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) ⟶
      pullback ((D.restrictBaseOpens T).over.hom ≫ f) f :=
  pullback.lift
    (pullback.fst ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) ≫
      (D.baseDatumIso T).inv)
    (pullback.snd ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) ≫
      pullback.fst f T.ι)
    (by
      rw [D.restrictBaseOpens_over_hom T]
      simp only [Category.assoc]
      rw [D.baseDatumIso_inv_comp_ι_comp_over_hom_assoc T, pullback.condition (f := f) (g := T.ι),
        ← Category.assoc ((D.baseDatum T).over.hom), ← Category.assoc,
        pullback.condition (f := (D.baseDatum T).over.hom ≫ pullback.snd f T.ι)
          (g := pullback.snd f T.ι), Category.assoc])

/-- The first component of `baseSourceInv` is the projection to the scheme of the pulled-back
datum followed by the inverse of `baseDatumIso`. -/
@[reassoc (attr := simp)]
lemma baseSourceInv_comp_fst :
    D.baseSourceInv T ≫ pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f =
      pullback.fst ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) ≫
        (D.baseDatumIso T).inv :=
  pullback.lift_fst _ _ _

/-- The second component of `baseSourceInv` is the projection to `X ×_S T` followed by the
projection to `X`. -/
@[reassoc (attr := simp)]
lemma baseSourceInv_comp_snd :
    D.baseSourceInv T ≫ pullback.snd ((D.restrictBaseOpens T).over.hom ≫ f) f =
      pullback.snd ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) ≫
        pullback.fst f T.ι :=
  pullback.lift_snd _ _ _

/-- **`V_T ×_S X` is `V_T ×_T (X ×_S T)`**: the sources of the gluing isomorphisms of the
restriction of the datum over `T` and of the pulled-back datum agree. -/
def baseSourceIso :
    pullback ((D.restrictBaseOpens T).over.hom ≫ f) f ≅
      pullback ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) where
  hom := D.baseSourceHom T
  inv := D.baseSourceInv T
  hom_inv_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, D.baseSourceInv_comp_fst T, D.baseSourceHom_comp_fst_assoc T,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, D.baseSourceInv_comp_snd T, D.baseSourceHom_comp_snd_assoc T,
        D.baseSourcePart_comp_fst T, Category.id_comp]
  inv_hom_id := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, D.baseSourceHom_comp_fst T, D.baseSourceInv_comp_fst_assoc T,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    · rw [Category.assoc, D.baseSourceHom_comp_snd T, Category.id_comp]
      refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, D.baseSourcePart_comp_fst T, D.baseSourceInv_comp_snd T]
      · rw [Category.assoc, D.baseSourcePart_comp_snd T, D.baseSourceInv_comp_fst_assoc T,
          D.baseDatumIso_inv_comp_morphismRestrict T,
          pullback.condition (f := (D.baseDatum T).over.hom ≫ pullback.snd f T.ι)
            (g := pullback.snd f T.ι)]

/-- The forward map of `baseSourceIso` is `baseSourceHom`. -/
@[simp]
lemma baseSourceIso_hom : (D.baseSourceIso T).hom = D.baseSourceHom T := rfl

/-- The inverse map of `baseSourceIso` is `baseSourceInv`. -/
@[simp]
lemma baseSourceIso_inv : (D.baseSourceIso T).inv = D.baseSourceInv T := rfl

/-- The morphism of descent data including the restriction over an open of the base into the
datum. -/
abbrev restrictBaseOpensHom : D.restrictBaseOpens T ⟶ D :=
  D.restrictOpenHom (D.baseOpens T) (D.isTransitionInvariant_preimage_base T)

/-- Read on `V_T ×_S X`, the two maps to `V ×_S X` — the one coming from the pullback functor
and the one coming from the inclusion of the restricted datum — agree. -/
lemma baseSourceIso_hom_comp_sourceMap :
    (D.baseSourceIso T).hom ≫ (basePullbackFunctor f T).sourceMap D =
      homSourceMap (D.restrictBaseOpensHom T) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, (basePullbackFunctor f T).sourceMap_fst D, homSourceMap_comp_fst,
      restrictOpenHom_hom_left, baseSourceIso_hom, D.baseSourceHom_comp_fst_assoc T,
      ← Category.assoc ((D.baseDatumIso T).hom), D.baseDatumIso_hom_comp_objIso T,
      (D.isPullback_basePart T).isoPullback_hom_fst]
  · rw [Category.assoc, (basePullbackFunctor f T).sourceMap_snd D, baseSourceIso_hom,
      D.baseSourceHom_comp_snd_assoc T, D.baseSourcePart_comp_fst T, homSourceMap,
      pullback.lift_snd, Category.comp_id]

/-- The gluing isomorphism of the pulled-back datum, read in `V` through the inclusion of the
part of `V` over `T`: it is the gluing isomorphism of the datum itself. -/
lemma baseDatum_transition_comp_ι :
    (D.baseDatum T).transitionPullbackIso.hom ≫
        pullback.snd (pullback.snd f T.ι) ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) ≫
          (D.baseDatumIso T).inv ≫ (D.baseOpens T).ι =
      (basePullbackFunctor f T).sourceMap D ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  rw [D.baseDatumIso_inv_comp_ι T, ← (basePullbackFunctor f T).targetMap_snd D,
    ← Category.assoc (D.baseDatum T).transitionPullbackIso.hom,
    (basePullbackFunctor f T).gluing D, Category.assoc]

/-- The gluing isomorphism of the restriction over `T`, read in `V` through the inclusion of the
part of `V` over `T`: it is the gluing isomorphism of the datum itself. -/
lemma restrictBaseOpens_transition_comp_ι :
    (D.restrictBaseOpens T).transitionPullbackIso.hom ≫
        pullback.snd f ((D.restrictBaseOpens T).over.hom ≫ f) ≫ (D.baseOpens T).ι =
      homSourceMap (D.restrictBaseOpensHom T) ≫ D.transitionPullbackIso.hom ≫
        pullback.snd f (D.over.hom ≫ f) := by
  rw [← Category.assoc (homSourceMap (D.restrictBaseOpensHom T)),
    transitionPullbackIso_naturality (D.restrictBaseOpensHom T), Category.assoc,
    homTargetMap_comp_snd, restrictOpenHom_hom_left]

/-- **The two gluing isomorphisms agree**, in the component landing in the scheme of the datum:
the gluing isomorphism of the pulled-back datum, read through the identification of the sources
and of the schemes, is the gluing isomorphism of the restriction of the datum over `T`. This is
the one component the invariance of a projection uses. -/
lemma baseSourceIso_hom_comp_transition :
    (D.baseSourceIso T).hom ≫ (D.baseDatum T).transitionPullbackIso.hom ≫
        pullback.snd (pullback.snd f T.ι) ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) =
      (D.restrictBaseOpens T).transitionPullbackIso.hom ≫
        pullback.snd f ((D.restrictBaseOpens T).over.hom ≫ f) ≫ (D.baseDatumIso T).hom := by
  refine (cancel_mono ((D.baseDatumIso T).inv ≫ (D.baseOpens T).ι)).mp ?_
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [D.baseDatum_transition_comp_ι T, ← Category.assoc, D.baseSourceIso_hom_comp_sourceMap T,
    ← D.restrictBaseOpens_transition_comp_ι T]

/-- The first projection of `V_T ×_S X`, read in `V_T ×_T (X ×_S T)`. -/
lemma baseSourceIso_hom_comp_fst :
    (D.baseSourceIso T).hom ≫
        pullback.fst ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) (pullback.snd f T.ι) =
      pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ (D.baseDatumIso T).hom := by
  rw [baseSourceIso_hom, D.baseSourceHom_comp_fst T]

/-- The inverse of `baseDatumIso` followed by `basePart` is the structure morphism of the
pulled-back datum. -/
@[reassoc]
lemma baseDatumIso_inv_comp_basePart :
    (D.baseDatumIso T).inv ≫ D.basePart T = (D.baseDatum T).over.hom := by
  rw [← D.baseDatumIso_hom_comp_over_hom T, Iso.inv_hom_id_assoc]

/-- The scheme of the pulled-back datum is étale over `X ×_S T` when the scheme of the datum is
étale over `X`, being a base change of it. -/
instance etale_baseDatum_over_hom [Etale D.over.hom] : Etale (D.baseDatum T).over.hom := by
  have h1 : Etale (D.basePart T) :=
    MorphismProperty.of_isPullback (D.isPullback_basePart T) inferInstance
  have h2 : (D.baseDatum T).over.hom = (D.baseDatumIso T).inv ≫ D.basePart T := by
    rw [← D.baseDatumIso_hom_comp_over_hom T, Iso.inv_hom_id_assoc]
  rw [h2]
  infer_instance

/-- The part of `V` over a smaller open of the base is contained in the part over a larger
one. -/
lemma baseOpens_mono {T' : S.Opens} (hle : T' ≤ T) : D.baseOpens T' ≤ D.baseOpens T :=
  fun _ hx ↦ hle hx

/-- The invariance of a morphism out of the part of `V` over `T` is the same condition for the
restriction of the datum over `T` and for the pulled-back datum. -/
lemma proj_invariant_baseDatum_iff {Y : Scheme.{u}} (q : (D.baseDatum T).over.left ⟶ Y) :
    ((D.baseDatum T).transitionPullbackIso.hom ≫
          pullback.snd (pullback.snd f T.ι)
            ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι) ≫ q =
        pullback.fst ((D.baseDatum T).over.hom ≫ pullback.snd f T.ι)
          (pullback.snd f T.ι) ≫ q) ↔
      ((D.restrictBaseOpens T).transitionPullbackIso.hom ≫
          pullback.snd f ((D.restrictBaseOpens T).over.hom ≫ f) ≫
            ((D.baseDatumIso T).hom ≫ q) =
        pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫
          ((D.baseDatumIso T).hom ≫ q)) := by
  have htrans := congrArg (· ≫ q) (D.baseSourceIso_hom_comp_transition T)
  have hfst := congrArg (· ≫ q) (D.baseSourceIso_hom_comp_fst T)
  simp only [Category.assoc] at htrans hfst
  rw [← htrans, ← hfst]
  exact (cancel_epi (D.baseSourceIso T).hom).symm

/-! ### Charts over an open of the base -/

/-- **A chart of a descent datum over an open of the base.** For a descent datum `(V, φ)`
relative to `f : X ⟶ S` and an open `T ⊆ S`, a scheme over `T` together with a morphism from the
part of `V` lying over `T`, which exhibits that part as the fibre product of the scheme with `X`
over `S` and equalises the two legs of the gluing isomorphism of the restricted datum. -/
structure BaseChart where
  /-- The scheme over the open of the base. -/
  base : Over T.toScheme
  /-- The projection of the part of `V` lying over `T` onto it. -/
  proj : (D.baseOpens T).toScheme ⟶ base.left
  /-- The projection exhibits the part of `V` lying over `T` as the fibre product of the scheme
  with `X` over `S`. -/
  isPullback : IsPullback ((D.baseOpens T).ι ≫ D.over.hom) proj f (base.hom ≫ T.ι)
  /-- The projection equalises the gluing isomorphism of the restriction of the datum over `T`
  followed by the projection of `X ×_S V_T` to `V_T` and the projection of `V_T ×_S X` to
  `V_T`. -/
  proj_invariant : (D.restrictBaseOpens T).transitionPullbackIso.hom ≫
      pullback.snd f ((D.restrictBaseOpens T).over.hom ≫ f) ≫ proj =
    pullback.fst ((D.restrictBaseOpens T).over.hom ≫ f) f ≫ proj

namespace BaseChart

variable {D T}

/-- **A chart over `T` descends the restriction of the datum over `T`.** -/
@[implicit_reducible]
def descended (C : D.BaseChart T) : (D.restrictBaseOpens T).Descended where
  base := Over.mk (C.base.hom ≫ T.ι)
  proj := C.proj
  isPullback := C.isPullback
  proj_invariant := C.proj_invariant

/-- **A scheme descending the pulled-back datum is a chart over `T`.** -/
@[implicit_reducible]
def ofDescended (Q : (D.baseDatum T).Descended) : D.BaseChart T where
  base := Q.base
  proj := (D.baseDatumIso T).hom ≫ Q.proj
  isPullback := by
    have s : IsPullback (D.basePart T) ((D.baseDatumIso T).hom ≫ Q.proj)
        (pullback.snd f T.ι) Q.base.hom :=
      Q.isPullback.of_iso' (D.baseDatumIso T) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rw [Iso.refl_hom, Category.comp_id]; exact D.baseDatumIso_hom_comp_over_hom T)
        (by rw [Iso.refl_hom, Category.comp_id]) (by simp) (by simp)
    have h := s.paste_horiz (IsPullback.of_hasPullback f T.ι)
    rwa [D.basePart_comp_fst T] at h
  proj_invariant := (D.proj_invariant_baseDatum_iff T Q.proj).mp Q.proj_invariant

/-- **A chart over `T` is a scheme descending the pulled-back datum.** -/
@[implicit_reducible]
def toDescended (C : D.BaseChart T) : (D.baseDatum T).Descended where
  base := C.base
  proj := (D.baseDatumIso T).inv ≫ C.proj
  isPullback := by
    have hw : ((D.over.hom ≫ f) ∣_ T) = C.proj ≫ C.base.hom := by
      refine (cancel_mono T.ι).mp ?_
      rw [morphismRestrict_ι, Category.assoc, ← C.isPullback.w, Category.assoc]
    have s : IsPullback (D.basePart T) C.proj (pullback.snd f T.ι) C.base.hom := by
      refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback f T.ι)
      · rw [D.basePart_comp_fst T]; exact C.isPullback
      · rw [D.basePart_comp_snd T, hw]
    refine s.of_iso' (D.baseDatumIso T).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]
          exact D.baseDatumIso_inv_comp_basePart T)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom]) (by simp) (by simp)
  proj_invariant := by
    refine (D.proj_invariant_baseDatum_iff T ((D.baseDatumIso T).inv ≫ C.proj)).mpr ?_
    rw [Iso.hom_inv_id_assoc]
    exact C.proj_invariant

variable (C : D.BaseChart T)

/-- The structure morphism of a chart, as a morphism to `S`. -/
abbrev toBase : C.base.left ⟶ S := C.base.hom ≫ T.ι

/-- The projection of a chart lies over the base. -/
@[reassoc]
lemma proj_comp_toBase : C.proj ≫ C.toBase = (D.baseOpens T).ι ≫ D.over.hom ≫ f := by
  rw [← C.isPullback.w, Category.assoc]

/-- A chart over `T` lies entirely over `T`. -/
lemma toBase_preimage_self : C.toBase ⁻¹ᵁ T = ⊤ := by
  rw [toBase, Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self, Scheme.Hom.preimage_top]

variable {T' : S.Opens} (hle : T' ≤ T)

/-- The part of `V` over the smaller open is the part of `V_T` lying in the part of the chart
over that open. -/
lemma proj_preimage_toBase_preimage :
    C.proj ⁻¹ᵁ (C.toBase ⁻¹ᵁ T') = (D.baseOpens T).ι ⁻¹ᵁ D.baseOpens T' := by
  rw [← Scheme.Hom.comp_preimage, C.proj_comp_toBase, Scheme.Hom.comp_preimage]

/-- The part of `V` over the smaller open, identified with the part of `V_T` lying in the part
of the chart over that open. -/
def restrictIso :
    (D.baseOpens T').toScheme ≅ (C.proj ⁻¹ᵁ (C.toBase ⁻¹ᵁ T')).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.over.left.homOfLE (D.baseOpens_mono T hle))
    (C.proj ⁻¹ᵁ (C.toBase ⁻¹ᵁ T')).ι
    (by simp only [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
      Scheme.opensRange_homOfLE, C.proj_preimage_toBase_preimage])

/-- That identification is the inclusion of the part of `V` over the smaller open. -/
lemma restrictIso_hom_comp_ι :
    (C.restrictIso hle).hom ≫ (C.proj ⁻¹ᵁ (C.toBase ⁻¹ᵁ T')).ι =
      D.over.left.homOfLE (D.baseOpens_mono T hle) :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The projection of the chart over a smaller open of the base. -/
@[implicit_reducible]
def restrictProj : (D.baseOpens T').toScheme ⟶ (C.toBase ⁻¹ᵁ T').toScheme :=
  (C.restrictIso hle).hom ≫ (C.proj ∣_ (C.toBase ⁻¹ᵁ T'))

/-- **The characterisation of the restricted projection**: followed by the inclusion of the part
of the chart over the smaller open, it is the inclusion of the part of `V` over the smaller open
followed by the projection. -/
@[reassoc]
lemma restrictProj_comp_ι :
    C.restrictProj hle ≫ (C.toBase ⁻¹ᵁ T').ι =
      D.over.left.homOfLE (D.baseOpens_mono T hle) ≫ C.proj := by
  rw [restrictProj, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    C.restrictIso_hom_comp_ι hle]

/-- **The chart over a smaller open of the base**, cut out of the given one. -/
@[implicit_reducible]
def restrict : D.BaseChart T' where
  base := Over.mk (C.toBase ∣_ T')
  proj := C.restrictProj hle
  isPullback := by
    have s : IsPullback (C.restrictProj hle) (D.over.left.homOfLE (D.baseOpens_mono T hle))
        (C.toBase ⁻¹ᵁ T').ι C.proj :=
      (isPullback_morphismRestrict C.proj (C.toBase ⁻¹ᵁ T')).of_iso'
        (C.restrictIso hle) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rw [Iso.refl_hom, Category.comp_id]; rfl)
        (by rw [Iso.refl_hom, Category.comp_id]; exact C.restrictIso_hom_comp_ι hle)
        (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
        (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
    have h := s.paste_vert C.isPullback.flip
    rw [← Category.assoc, Scheme.homOfLE_ι] at h
    have heq : (C.toBase ∣_ T') ≫ T'.ι = (C.toBase ⁻¹ᵁ T').ι ≫ C.toBase :=
      morphismRestrict_ι C.toBase T'
    exact heq ▸ h.flip
  proj_invariant := by
    refine (cancel_mono (C.toBase ⁻¹ᵁ T').ι).mp ?_
    simp only [Category.assoc]
    rw [C.restrictProj_comp_ι hle]
    exact Descended.comp_proj_invariant
      (D.restrictOpenMono (D.isTransitionInvariant_preimage_base T')
        (D.isTransitionInvariant_preimage_base T) (D.baseOpens_mono T hle)) C.descended

/-- The structure morphism of the restricted chart is the restriction of `toBase` to the smaller
open. -/
@[simp]
lemma restrict_base_hom : (C.restrict hle).base.hom = C.toBase ∣_ T' := rfl

/-- The projection of the restricted chart is `restrictProj`. -/
@[simp]
lemma restrict_proj : (C.restrict hle).proj = C.restrictProj hle := rfl

/-- The chart over a smaller open of the base is again étale over that open. -/
instance etale_restrict_base_hom [Etale C.base.hom] : Etale (C.restrict hle).base.hom :=
  MorphismProperty.of_isPullback (isPullback_morphismRestrict C.toBase T').flip inferInstance

end BaseChart

end DescentDatum

end AlgebraicGeometry

end

end
