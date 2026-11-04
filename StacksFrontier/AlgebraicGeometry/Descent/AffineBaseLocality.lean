module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.DescendedScheme
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpenFromBase
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackSquare

/-!
# Effective descent of affine morphisms reduces to an affine base

Let `f : X ⟶ S` be a surjective, flat, quasi-compact morphism of schemes and let `(V, φ)` be a
descent datum relative to `X/S` whose structure morphism `V ⟶ X` is affine. This file reduces
the effectivity of `(V, φ)` to the same statement over an affine base, by restricting the datum
to the part of `V` lying over an affine open of `S` and recognising that part as the base change
of the datum along that open.

## Main definitions

* `AlgebraicGeometry.DescentDatum.baseOpenPullbackFunctor` is the pullback of descent data along
  the Cartesian square whose vertical arrows are `f` and `f ∣_ U`, for `U` an open of `S`, and
  `AlgebraicGeometry.DescentDatum.restrictBaseOpen` is the descent datum relative to `f ∣_ U` it
  produces.
* `AlgebraicGeometry.DescentDatum.restrictBaseOpenProj` is the projection of the scheme carried
  by the base-restricted datum onto `V`, and
  `AlgebraicGeometry.DescentDatum.restrictBaseOpenIso` identifies that scheme with the open of
  `V` lying over `U`.

## Main results

* `AlgebraicGeometry.DescentDatum.isPullback_restrictBaseOpenCompare`: the source product
  `W ×_S X` of the restriction of the datum to that open is the source product of the
  base-restricted datum.
* `AlgebraicGeometry.DescentDatum.Descended.ofRestrictBaseOpen`: a descended scheme for the
  base-restricted datum is a descended scheme for the restriction of `(V, φ)` to that invariant
  open, its scheme over `S` being the one over `U` followed by `U ⟶ S`.
* `AlgebraicGeometry.DescentDatum.isEffective_of_isAffineHom_of_affineBaseCase`: **effective
  descent for affine morphisms along a single quasi-compact fpqc covering reduces to the case of
  an affine base.**

## Implementation notes

The invariant open used is the preimage `W` of an affine open `U ⊆ S` under `V ⟶ X ⟶ S`; its
invariance is `AlgebraicGeometry.DescentDatum.isTransitionInvariant_preimage_base`, from
`StacksFrontier/AlgebraicGeometry/Descent/Scheme/InvariantOpenFromBase.lean`.

The comparison between `W` and the scheme carried by the base-restricted datum is a comparison
of two pullbacks of the same cospan: `W` is a pullback of `V ⟶ X` along `f^{-1}(U) ⟶ X` by
`AlgebraicGeometry.isPullback_morphismRestrict`, and so is the base-restricted scheme by the
`objIso` field of `AlgebraicGeometry.DescentData.PullbackFunctor`. Both coordinates of a point
of `W ×_S X` lie over `U`, so `W ×_S X` is likewise the source product of the base-restricted
datum, and the projection equalising the two legs of the restricted gluing isomorphism is
checked after composing with that comparison. The two gluing isomorphisms are matched by the
`gluing` field of the pullback functor together with the naturality
`AlgebraicGeometry.DescentDatum.transitionPullbackIso_naturality` of the gluing isomorphism
along the inclusion of the restricted datum, after cancelling the open immersion `W ⟶ V`.

The comparison statements are phrased for an arbitrary descent datum mapping to `(V, φ)` by an
open immersion, together with an identification of its scheme with the base-restricted scheme
over the projection to `V`. That keeps every fibre product written through one structure
morphism, and the restriction to the open lying over `U` is the instance of interest.

## References

* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 023Y](https://stacks.math.columbia.edu/tag/023Y)
* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

namespace DescentDatum

section BaseRestriction

variable {S X : Scheme.{u}}

/-- The pullback of descent data along the restriction of `f : X ⟶ S` to an open `U ⊆ S`: the
Cartesian square with vertical arrows `f` and `f ∣_ U` and horizontal arrows the open immersions
`f^{-1}(U) ⟶ X` and `U ⟶ S`. -/
def baseOpenPullbackFunctor (f : X ⟶ S) (U : S.Opens) :
    DescentData.PullbackFunctor f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι (morphismRestrict_ι f U).symm :=
  DescentData.pullbackFunctor f (f ∣_ U) U.ι (f ⁻¹ᵁ U).ι (morphismRestrict_ι f U).symm

variable {f : X ⟶ S} (D : DescentDatum f) (U : S.Opens)

/-- The descent datum relative to `f ∣_ U : f^{-1}(U) ⟶ U` obtained from `D` by base change
along the open immersion `U ⟶ S`. -/
@[reducible]
def restrictBaseOpen : DescentDatum (f ∣_ U) :=
  (baseOpenPullbackFunctor f U).functor.obj D

/-- The projection of the scheme carried by the base-restricted datum onto `V`. Together with
the structure morphism it exhibits that scheme as `f^{-1}(U) ×_X V`. -/
def restrictBaseOpenProj : (D.restrictBaseOpen U).over.left ⟶ D.over.left :=
  ((baseOpenPullbackFunctor f U).objIso D).hom.left ≫ pullback.fst D.over.hom (f ⁻¹ᵁ U).ι

/-- The projection onto `V` and the structure morphism of the base-restricted datum exhibit the
scheme it carries as the fibre product `f^{-1}(U) ×_X V`. -/
theorem isPullback_restrictBaseOpenProj :
    IsPullback (D.restrictBaseOpenProj U) (D.restrictBaseOpen U).over.hom D.over.hom
      (f ⁻¹ᵁ U).ι := by
  refine (IsPullback.of_hasPullback D.over.hom (f ⁻¹ᵁ U).ι).of_iso'
    ((Over.forget _).mapIso ((baseOpenPullbackFunctor f U).objIso D)) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · rw [Iso.refl_hom, Category.comp_id]
    rfl
  · rw [Iso.refl_hom, Category.comp_id]
    exact Over.w ((baseOpenPullbackFunctor f U).objIso D).hom

/-- The projection onto `V` carries the structure morphism of the base-restricted datum to the
structure morphism of `D`. -/
theorem restrictBaseOpenProj_comp_over_hom :
    D.restrictBaseOpenProj U ≫ D.over.hom =
      (D.restrictBaseOpen U).over.hom ≫ (f ⁻¹ᵁ U).ι :=
  (D.isPullback_restrictBaseOpenProj U).w

/-! ### The open lying over `U` is the scheme carried by the base-restricted datum -/

/-- The open of `V` lying over an open `U ⊆ S` is a fibre product `f^{-1}(U) ×_X V`: the open
immersion `W ⟶ V` and the restriction of `V ⟶ X` exhibit it as one. -/
theorem isPullback_preimage_base_ι :
    IsPullback ((D.over.hom ≫ f) ⁻¹ᵁ U).ι (D.over.hom ∣_ (f ⁻¹ᵁ U)) D.over.hom (f ⁻¹ᵁ U).ι :=
  (isPullback_morphismRestrict D.over.hom (f ⁻¹ᵁ U)).flip

/-- The identification of the open of `V` lying over `U` with the scheme carried by the
base-restricted datum: both are fibre products of `V ⟶ X` along `f^{-1}(U) ⟶ X`. -/
def restrictBaseOpenIso :
    ((D.over.hom ≫ f) ⁻¹ᵁ U).toScheme ≅ (D.restrictBaseOpen U).over.left :=
  (D.isPullback_preimage_base_ι U).isoPullback ≪≫
    (D.isPullback_restrictBaseOpenProj U).isoPullback.symm

/-- The identification of the open lying over `U` with the base-restricted scheme is compatible
with the two projections to `V`. -/
@[reassoc (attr := simp)]
lemma restrictBaseOpenIso_hom_comp_proj :
    (D.restrictBaseOpenIso U).hom ≫ D.restrictBaseOpenProj U = ((D.over.hom ≫ f) ⁻¹ᵁ U).ι := by
  simp [restrictBaseOpenIso]

/-- The structure morphism of the base-restricted datum is affine as soon as that of `D` is,
being its base change along the open immersion `f^{-1}(U) ⟶ X`. -/
theorem isAffineHom_restrictBaseOpen_over_hom [IsAffineHom D.over.hom] :
    IsAffineHom (D.restrictBaseOpen U).over.hom :=
  MorphismProperty.of_isPullback (D.isPullback_restrictBaseOpenProj U) inferInstance

/-! ### The gluing isomorphism of the base-restricted datum -/

/-- The map of source products of the base restriction is the projection onto `V` in the first
factor. -/
@[reassoc]
lemma baseOpenSourceMap_comp_fst :
    (baseOpenPullbackFunctor f U).sourceMap D ≫ pullback.fst (D.over.hom ≫ f) f =
      pullback.fst ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) (f ∣_ U) ≫
        D.restrictBaseOpenProj U :=
  (baseOpenPullbackFunctor f U).sourceMap_fst D

/-- The map of source products of the base restriction is the open immersion `f^{-1}(U) ⟶ X`
in the second factor. -/
@[reassoc]
lemma baseOpenSourceMap_comp_snd :
    (baseOpenPullbackFunctor f U).sourceMap D ≫ pullback.snd (D.over.hom ≫ f) f =
      pullback.snd ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι :=
  (baseOpenPullbackFunctor f U).sourceMap_snd D

/-- The map of target products of the base restriction is the projection onto `V` in the second
factor. -/
@[reassoc]
lemma baseOpenTargetMap_comp_snd :
    (baseOpenPullbackFunctor f U).targetMap D ≫ pullback.snd f (D.over.hom ≫ f) =
      pullback.snd (f ∣_ U) ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) ≫
        D.restrictBaseOpenProj U :=
  (baseOpenPullbackFunctor f U).targetMap_snd D

/-- The gluing isomorphism of the base-restricted datum is the gluing isomorphism of `D` pulled
back along the induced map of self-fibre products. -/
lemma baseOpen_gluing :
    (baseOpenPullbackFunctor f U).sourceMap D ≫ D.transitionPullbackIso.hom =
      (D.restrictBaseOpen U).transitionPullbackIso.hom ≫
        (baseOpenPullbackFunctor f U).targetMap D :=
  ((baseOpenPullbackFunctor f U).gluing D).symm

/-- The base change of the component of a morphism of descent data in the first factor leaves
the `X`-coordinate alone. -/
@[reassoc]
lemma homSourceMap_comp_snd {D E : DescentDatum f} (g : D ⟶ E) :
    homSourceMap g ≫ pullback.snd (E.over.hom ≫ f) f = pullback.snd (D.over.hom ≫ f) f :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-! ### Comparing an open sub-datum with the base restriction -/

section Comparison

variable {D' : DescentDatum f} (i : D' ⟶ D)
  (e : D'.over.left ≅ (D.restrictBaseOpen U).over.left)
  (he : e.hom ≫ D.restrictBaseOpenProj U = (i.hom ()).left)

include he in
/-- An identification of an open sub-datum with the base-restricted scheme over the projection
to `V` carries the component of the sub-datum to that projection. -/
lemma restrictBaseOpenCompare_inv_comp_hom_left :
    e.inv ≫ (i.hom ()).left = D.restrictBaseOpenProj U := by
  rw [← he, Iso.inv_hom_id_assoc]

include he in
/-- Such an identification carries the structure morphism of the sub-datum to the structure
morphism of the base-restricted datum followed by `f^{-1}(U) ⟶ X`. -/
lemma restrictBaseOpenCompare_inv_comp_over_hom :
    e.inv ≫ D'.over.hom = (D.restrictBaseOpen U).over.hom ≫ (f ⁻¹ᵁ U).ι := by
  rw [← Over.w (i.hom ()), ← Category.assoc,
    D.restrictBaseOpenCompare_inv_comp_hom_left U i e he,
    D.restrictBaseOpenProj_comp_over_hom U]

include he in
/-- The same compatibility, read in the other direction. -/
lemma restrictBaseOpenCompare_hom_comp_over_hom :
    e.hom ≫ (D.restrictBaseOpen U).over.hom ≫ (f ⁻¹ᵁ U).ι = D'.over.hom := by
  rw [← D.restrictBaseOpenCompare_inv_comp_over_hom U i e he, Iso.hom_inv_id_assoc]

include he in
/-- **The source product of the base-restricted datum is the source product of the open
sub-datum.** Both coordinates of a point of `W ×_S X` lie over `U`, so the fibre product over
`S` is already the fibre product over `U`. -/
theorem isPullback_restrictBaseOpenCompare :
    IsPullback
      (pullback.fst ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) (f ∣_ U) ≫ e.inv)
      (pullback.snd ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) (f ∣_ U) ≫ (f ⁻¹ᵁ U).ι)
      (D'.over.hom ≫ f) f := by
  refine ((IsPullback.of_hasPullback ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U)
      (f ∣_ U)).flip.paste_horiz (isPullback_morphismRestrict f U).flip).flip.of_iso
    (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp) ?_ (by simp)
  simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
  calc ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) ≫ U.ι
      = (D.restrictBaseOpen U).over.hom ≫ (f ⁻¹ᵁ U).ι ≫ f := by
        rw [Category.assoc, morphismRestrict_ι]
    _ = (e.inv ≫ D'.over.hom) ≫ f := by
        rw [← Category.assoc, ← D.restrictBaseOpenCompare_inv_comp_over_hom U i e he]
    _ = e.inv ≫ D'.over.hom ≫ f := Category.assoc _ _ _

include he in
/-- The comparison of source products is the map of source products of the pullback functor,
read through the inclusion of the open sub-datum in `D`. -/
theorem restrictBaseOpenCompare_comp_homSourceMap :
    (D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom ≫ homSourceMap i =
      (baseOpenPullbackFunctor f U).sourceMap D := by
  apply pullback.hom_ext
  · rw [Category.assoc, homSourceMap_comp_fst, ← Category.assoc,
      IsPullback.isoPullback_hom_fst, Category.assoc,
      D.restrictBaseOpenCompare_inv_comp_hom_left U i e he, D.baseOpenSourceMap_comp_fst U]
  · rw [Category.assoc, homSourceMap_comp_snd, IsPullback.isoPullback_hom_snd,
      D.baseOpenSourceMap_comp_snd U]

section Mono

variable [IsOpenImmersion (i.hom ()).left]

include he in
/-- **The gluing isomorphism of the open sub-datum, followed by the projection of `X ×_S W` to
`W`, read through the comparison of source products.** It is the gluing isomorphism of the
base-restricted datum followed by the projection of `f^{-1}(U) ×_U E` to `E`. -/
@[reassoc]
theorem restrictBaseOpenCompare_comp_transition :
    (D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom ≫
        D'.transitionPullbackIso.hom ≫ pullback.snd f (D'.over.hom ≫ f) =
      (D.restrictBaseOpen U).transitionPullbackIso.hom ≫
        pullback.snd (f ∣_ U) ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) ≫ e.inv := by
  refine (cancel_mono (i.hom ()).left).mp (Eq.symm ?_)
  calc ((D.restrictBaseOpen U).transitionPullbackIso.hom ≫
        pullback.snd (f ∣_ U) ((D.restrictBaseOpen U).over.hom ≫ f ∣_ U) ≫ e.inv) ≫
          (i.hom ()).left
      = (D.restrictBaseOpen U).transitionPullbackIso.hom ≫
          (baseOpenPullbackFunctor f U).targetMap D ≫ pullback.snd f (D.over.hom ≫ f) := by
        rw [Category.assoc, Category.assoc,
          D.restrictBaseOpenCompare_inv_comp_hom_left U i e he, D.baseOpenTargetMap_comp_snd U]
    _ = (baseOpenPullbackFunctor f U).sourceMap D ≫ D.transitionPullbackIso.hom ≫
          pullback.snd f (D.over.hom ≫ f) := by
        rw [← Category.assoc, ← D.baseOpen_gluing U, Category.assoc]
    _ = (D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom ≫
          homSourceMap i ≫ D.transitionPullbackIso.hom ≫
            pullback.snd f (D.over.hom ≫ f) := by
        rw [← D.restrictBaseOpenCompare_comp_homSourceMap U i e he, Category.assoc]
    _ = (D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom ≫
          D'.transitionPullbackIso.hom ≫
            homTargetMap i ≫ pullback.snd f (D.over.hom ≫ f) := by
        rw [← Category.assoc (homSourceMap i), transitionPullbackIso_naturality i,
          Category.assoc]
    _ = ((D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom ≫
          D'.transitionPullbackIso.hom ≫ pullback.snd f (D'.over.hom ≫ f)) ≫
            (i.hom ()).left := by
        rw [homTargetMap_comp_snd]
        simp only [Category.assoc]

include he in
/-- **A descended scheme for the base-restricted datum descends an open sub-datum identified
with it.** Its scheme over `S` is the given scheme over `U` followed by the open immersion
`U ⟶ S`, and its projection is the given one read through that identification. -/
def Descended.ofRestrictBaseOpenOfIso (Q : (D.restrictBaseOpen U).Descended) : D'.Descended where
  base := Over.mk (Q.base.hom ≫ U.ι)
  proj := e.hom ≫ Q.proj
  isPullback :=
    ((Q.isPullback.flip.paste_vert (isPullback_morphismRestrict f U)).of_iso' e (Iso.refl _)
      (Iso.refl _) (Iso.refl _) (by simp)
      (by
        simp only [Iso.refl_hom, Category.comp_id]
        exact D.restrictBaseOpenCompare_hom_comp_over_hom U i e he)
      (by simp) (by simp)).flip
  proj_invariant := by
    refine (cancel_epi
      (D.isPullback_restrictBaseOpenCompare U i e he).isoPullback.hom).mp ?_
    simp only [D.restrictBaseOpenCompare_comp_transition_assoc U i e he,
      IsPullback.isoPullback_hom_fst_assoc, Category.assoc, Iso.inv_hom_id_assoc]
    exact Q.proj_invariant

end Mono

end Comparison

/-- **A descended scheme for the base-restricted datum descends the restriction of `D` to the
invariant open of `V` lying over `U`.** -/
def Descended.ofRestrictBaseOpen (Q : (D.restrictBaseOpen U).Descended) :
    (D.restrictOpen ((D.over.hom ≫ f) ⁻¹ᵁ U)
      (D.isTransitionInvariant_preimage_base U)).Descended :=
  Descended.ofRestrictBaseOpenOfIso D U
    (D.restrictOpenHom ((D.over.hom ≫ f) ⁻¹ᵁ U) (D.isTransitionInvariant_preimage_base U))
    (D.restrictBaseOpenIso U) (D.restrictBaseOpenIso_hom_comp_proj U) Q

end BaseRestriction

/-! ### Reduction to an affine base -/

/-- **Effective descent for affine morphisms along a single quasi-compact fpqc covering reduces
to the case of an affine base.** If every descent datum with affine structure morphism relative
to a surjective, flat, quasi-compact morphism onto an *affine* base is effective, then so is
every such datum over an arbitrary base. -/
theorem isEffective_of_isAffineHom_of_affineBaseCase
    {S X : Scheme.{u}} {f : X ⟶ S} [Surjective f] [Flat f] [QuasiCompact f]
    (H : ∀ (S' X' : Scheme.{u}) (f' : X' ⟶ S') [IsAffine S'] [Surjective f'] [Flat f']
      [QuasiCompact f'] (D' : DescentDatum f'), IsAffineHom (D'.obj ()).hom →
      DescentData.IsEffective D')
    (D : DescentDatum f) (haff : IsAffineHom D.over.hom) :
    DescentData.IsEffective D := by
  have := haff
  refine isEffective_of_forall_exists_restrictOpen D fun v ↦ ?_
  obtain ⟨U, hU, hvU, -⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := S) (x := (D.over.hom ≫ f).base v) (U := ⊤) trivial
  refine ⟨(D.over.hom ≫ f) ⁻¹ᵁ U, D.isTransitionInvariant_preimage_base U, hvU, ?_⟩
  have : IsAffine U.toScheme := hU
  have : Surjective (f ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  obtain ⟨Q⟩ := nonempty_descended_of_isEffective
    (H U.toScheme (f ⁻¹ᵁ U).toScheme (f ∣_ U) (D.restrictBaseOpen U)
      (D.isAffineHom_restrictBaseOpen_over_hom U))
  exact (Descended.ofRestrictBaseOpen D U Q).isEffective

end DescentDatum

end AlgebraicGeometry

end
