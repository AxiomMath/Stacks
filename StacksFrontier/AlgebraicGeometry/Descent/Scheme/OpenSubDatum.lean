module

public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.RestrictOpen

/-!
# An open sub-datum of a descent datum is the restriction to an invariant open

Let `f : X ⟶ S` be a morphism of schemes and let `(V, φ)` be a descent datum relative to
`X/S`. A *morphism of descent data whose component is an open immersion* `ι : V' ⟶ V` is the
same thing as an invariant open `W ⊆ V` together with an identification of the datum upstairs
with `AlgebraicGeometry.DescentDatum.restrictOpen`. In particular, the existence of an effective
open sub-datum through a point of `V` is equivalent to the existence of an invariant open
neighbourhood of that point whose restricted datum is effective.

## Main definitions

* `AlgebraicGeometry.DescentDatum.homSourceMap` and
  `AlgebraicGeometry.DescentDatum.homTargetMap` are the two base changes along `f` of the
  component of a morphism of descent data, as maps `V ×_S X ⟶ V' ×_S X` and
  `X ×_S V ⟶ X ×_S V'` of literal fibre products.
* `AlgebraicGeometry.DescentDatum.restrictOpenHom` is the inclusion
  `D.restrictOpen W hW ⟶ D` of the restriction to an invariant open, as a morphism of descent
  data. Its component is the open immersion `W ⟶ V`.
* `AlgebraicGeometry.DescentDatum.overRestrictOpenIso` identifies the scheme over `X` carried
  by a descent datum mapping to `D` by an open immersion with the open subscheme of `V` cut out
  by the image of that open immersion.
* `AlgebraicGeometry.DescentDatum.restrictOpenIso` upgrades that identification to an
  isomorphism of descent data `E ≅ D.restrictOpen W hW`.

## Main results

* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_opensRange`: the image of a morphism of
  descent data whose component is an open immersion is an invariant open.
* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_inf` and
  `AlgebraicGeometry.DescentDatum.isTransitionInvariant_top`: the invariant opens of `V` are
  closed under intersection and contain `V`.
* `AlgebraicGeometry.DescentDatum.isTransitionInvariant_preimage`: the preimage of an invariant
  open along a morphism of descent data is invariant.
* `AlgebraicGeometry.DescentDatum.transitionPullbackIso_naturality`: the compatibility square
  of a morphism of descent data, computed on the literal fibre products `V ×_S X` and
  `X ×_S V`.
* `AlgebraicGeometry.DescentDatum.exists_openImmersionHom_isEffective_iff`: through a point of
  `V` there is an effective descent datum mapping to `D` by an open immersion if and only if
  there is an invariant open neighbourhood whose restricted datum is effective.
* `AlgebraicGeometry.range_pullbackMapFst_of_isOpenImmersion` and
  `AlgebraicGeometry.range_pullbackMapSnd_of_isOpenImmersion`: the image of a fibre product
  base changed along an open immersion in one factor is the preimage of the image of that open
  immersion.

## References

* [Stacks Project, Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Limits

/-! ### The image of a fibre product base changed along an open immersion -/

/-- Precomposing with an isomorphism does not change the image on underlying spaces. -/
private lemma range_comp_base_of_isIso {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e] (g : B ⟶ C) :
    Set.range (e ≫ g).base = Set.range g.base := by
  have hsurj : Function.Surjective e.base := (Scheme.homeoOfIso (asIso e)).surjective
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr hsurj,
    Set.image_univ]

section Range

variable {A B Y Z : Scheme.{u}} (ι : A ⟶ B) [IsOpenImmersion ι] (b : B ⟶ Z) (a : A ⟶ Z)
  (g : Y ⟶ Z)

omit [IsOpenImmersion ι] in
/-- The base change of an open immersion `ι` in the first factor, read through
`CategoryTheory.Limits.pullbackRightPullbackFstIso`, is the second projection of
`A ×_B (B ×_Z Y)`. -/
lemma pullbackRightPullbackFstIso_hom_comp_pullbackMap
    (h₁ : (ι ≫ b) ≫ 𝟙 Z = ι ≫ b) (h₂ : g ≫ 𝟙 Z = 𝟙 Y ≫ g) :
    (pullbackRightPullbackFstIso b g ι).hom ≫
        pullback.map (ι ≫ b) g b g ι (𝟙 Y) (𝟙 Z) h₁ h₂ =
      pullback.snd ι (pullback.fst b g) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.map, pullback.lift_fst,
      pullbackRightPullbackFstIso_hom_fst_assoc]
    exact pullback.condition
  · rw [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]

omit [IsOpenImmersion ι] in
/-- The base change of an open immersion `ι` in the second factor, read through
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, is the first projection of
`(Y ×_Z B) ×_B A`. -/
lemma pullbackLeftPullbackSndIso_hom_comp_pullbackMap
    (h₁ : g ≫ 𝟙 Z = 𝟙 Y ≫ g) (h₂ : (ι ≫ b) ≫ 𝟙 Z = ι ≫ b) :
    (pullbackLeftPullbackSndIso g b ι).hom ≫
        pullback.map g (ι ≫ b) g b (𝟙 Y) ι (𝟙 Z) h₁ h₂ =
      pullback.fst (pullback.snd g b) ι := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.map, pullback.lift_fst, Category.comp_id,
      pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, pullback.map, pullback.lift_snd,
      pullbackLeftPullbackSndIso_hom_snd_assoc]
    exact pullback.condition.symm

/-- **The image of a fibre product base changed along an open immersion in the first factor.**
If `a = ι ≫ b` with `ι` an open immersion, the induced map `A ×_Z Y ⟶ B ×_Z Y` has image the
preimage of the image of `ι` under the first projection. -/
lemma range_pullbackMapFst_of_isOpenImmersion (hab : a = ι ≫ b)
    (h₁ : a ≫ 𝟙 Z = ι ≫ b) (h₂ : g ≫ 𝟙 Z = 𝟙 Y ≫ g) :
    Set.range (pullback.map a g b g ι (𝟙 Y) (𝟙 Z) h₁ h₂).base =
      ↑(pullback.fst b g ⁻¹ᵁ ι.opensRange) := by
  subst hab
  rw [← IsOpenImmersion.range_pullbackSnd ι (pullback.fst b g),
    ← pullbackRightPullbackFstIso_hom_comp_pullbackMap ι b g h₁ h₂, range_comp_base_of_isIso]

/-- **The image of a fibre product base changed along an open immersion in the second factor.**
If `a = ι ≫ b` with `ι` an open immersion, the induced map `Y ×_Z A ⟶ Y ×_Z B` has image the
preimage of the image of `ι` under the second projection. -/
lemma range_pullbackMapSnd_of_isOpenImmersion (hab : a = ι ≫ b)
    (h₁ : g ≫ 𝟙 Z = 𝟙 Y ≫ g) (h₂ : a ≫ 𝟙 Z = ι ≫ b) :
    Set.range (pullback.map g a g b (𝟙 Y) ι (𝟙 Z) h₁ h₂).base =
      ↑(pullback.snd g b ⁻¹ᵁ ι.opensRange) := by
  subst hab
  rw [← IsOpenImmersion.range_pullbackFst ι (pullback.snd g b),
    ← pullbackLeftPullbackSndIso_hom_comp_pullbackMap ι b g h₁ h₂, range_comp_base_of_isIso]

end Range

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} {D E : DescentDatum f}

/-! ### The compatibility square on the literal fibre products -/

/-- The structure morphism to `S` of the source of a morphism of descent data factors through
the component of that morphism. -/
lemma hom_left_comp_over_hom (g : D ⟶ E) :
    (D.over.hom ≫ f) ≫ 𝟙 S = (g.hom ()).left ≫ (E.over.hom ≫ f) := by
  rw [Category.comp_id, ← Category.assoc, Over.w]

/-- The component of a morphism of descent data, base changed along `f` in the first factor:
the map `V ×_S X ⟶ V' ×_S X`. -/
abbrev homSourceMap (g : D ⟶ E) :
    pullback (D.over.hom ≫ f) f ⟶ pullback (E.over.hom ≫ f) f :=
  pullback.map (D.over.hom ≫ f) f (E.over.hom ≫ f) f (g.hom ()).left (𝟙 X) (𝟙 S)
    (hom_left_comp_over_hom g) (by simp)

/-- The component of a morphism of descent data, base changed along `f` in the second factor:
the map `X ×_S V ⟶ X ×_S V'`. -/
abbrev homTargetMap (g : D ⟶ E) :
    pullback f (D.over.hom ≫ f) ⟶ pullback f (E.over.hom ≫ f) :=
  pullback.map f (D.over.hom ≫ f) f (E.over.hom ≫ f) (𝟙 X) (g.hom ()).left (𝟙 S)
    (by simp) (hom_left_comp_over_hom g)

/-- `AlgebraicGeometry.DescentDatum.homSourceMap` is the component of `g` in the first
factor. -/
@[reassoc]
lemma homSourceMap_comp_fst (g : D ⟶ E) :
    homSourceMap g ≫ pullback.fst (E.over.hom ≫ f) f =
      pullback.fst (D.over.hom ≫ f) f ≫ (g.hom ()).left :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.DescentDatum.homTargetMap` is the component of `g` in the second
factor. -/
@[reassoc]
lemma homTargetMap_comp_snd (g : D ⟶ E) :
    homTargetMap g ≫ pullback.snd f (E.over.hom ≫ f) =
      pullback.snd f (D.over.hom ≫ f) ≫ (g.hom ()).left :=
  pullback.lift_snd _ _ _

/-- **The compatibility square of a morphism of descent data, on the literal fibre products.**
The gluing isomorphisms of `D` and `E` commute with the two base changes of the component of
`g` along `f`. -/
theorem transitionPullbackIso_naturality (g : D ⟶ E) :
    homSourceMap g ≫ E.transitionPullbackIso.hom =
      D.transitionPullbackIso.hom ≫ homTargetMap g := by
  set sD := Over.prodLeftIsoPullback ((Over.map f).obj D.over) (Over.mk f) with hsD
  set sE := Over.prodLeftIsoPullback ((Over.map f).obj E.over) (Over.mk f) with hsE
  set tD := Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj D.over) with htD
  set tE := Over.prodLeftIsoPullback (Over.mk f) ((Over.map f).obj E.over) with htE
  have hs : homSourceMap g =
      sD.inv ≫ (prod.map ((Over.map f).map (g.hom ())) (𝟙 (Over.mk f))).left ≫ sE.hom := by
    simpa [hsD, hsE] using
      (DescentData.prodMap_left ((Over.map f).map (g.hom ())) (𝟙 (Over.mk f))).symm
  have ht : homTargetMap g =
      tD.inv ≫ (prod.map (𝟙 (Over.mk f)) ((Over.map f).map (g.hom ()))).left ≫ tE.hom := by
    simpa [htD, htE] using
      (DescentData.prodMap_left (𝟙 (Over.mk f)) ((Over.map f).map (g.hom ()))).symm
  have h' := congrArg (fun k => sD.inv ≫ k ≫ tE.hom)
    (congrArg Over.Hom.left (g.comm () ()))
  simpa [hs, ht, hsD, hsE, htD, htE, DescentData.gluingPullbackIso, DescentData.gluingIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map, Over.comp_left,
    Category.assoc] using h'

/-! ### Invariance is stable under intersection -/

variable (D) in
/-- **The intersection of two invariant opens is invariant.** -/
theorem isTransitionInvariant_inf {W₁ W₂ : D.over.left.Opens}
    (h₁ : D.IsTransitionInvariant W₁) (h₂ : D.IsTransitionInvariant W₂) :
    D.IsTransitionInvariant (W₁ ⊓ W₂) := by
  have hinj : Function.Injective D.transitionPullbackIso.hom.base :=
    (Scheme.homeoOfIso D.transitionPullbackIso).injective
  have e : ∀ W : D.over.left.Opens, D.IsTransitionInvariant W →
      D.transitionPullbackIso.hom.base ''
        ((pullback.fst (D.over.hom ≫ f) f).base ⁻¹' (W : Set _)) =
        (pullback.snd f (D.over.hom ≫ f)).base ⁻¹' (W : Set _) := fun W h ↦ by
    simpa only [Scheme.Hom.coe_image, TopologicalSpace.Opens.map_coe] using
      TopologicalSpace.Opens.ext_iff.mp h
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.map_coe,
    TopologicalSpace.Opens.coe_inf, Set.preimage_inter]
  rw [Set.image_inter hinj, e W₁ h₁, e W₂ h₂]

variable (D) in
/-- **The whole of `V` is an invariant open.** -/
theorem isTransitionInvariant_top : D.IsTransitionInvariant ⊤ := by
  have hsurj : Function.Surjective D.transitionPullbackIso.hom.base :=
    (Scheme.homeoOfIso D.transitionPullbackIso).surjective
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_image, TopologicalSpace.Opens.map_coe,
    TopologicalSpace.Opens.coe_top, Set.preimage_univ, Set.image_univ]
  exact Set.range_eq_univ.mpr hsurj

/-! ### Invariance pulls back along a morphism of descent data -/

/-- **The preimage of an invariant open under a morphism of descent data is invariant.** -/
theorem isTransitionInvariant_preimage (g : D ⟶ E) {W : E.over.left.Opens}
    (hW : E.IsTransitionInvariant W) :
    D.IsTransitionInvariant ((g.hom ()).left ⁻¹ᵁ W) := by
  have hinv : D.transitionPullbackIso.inv ≫ homSourceMap g =
      homTargetMap g ≫ E.transitionPullbackIso.inv := by
    have h := congrArg (fun k ↦ D.transitionPullbackIso.inv ≫ k ≫
      E.transitionPullbackIso.inv) (transitionPullbackIso_naturality g)
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] using h
  calc D.transitionPullbackIso.hom ''ᵁ
        (pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ ((g.hom ()).left ⁻¹ᵁ W))
      = (D.transitionPullbackIso.inv ≫ pullback.fst (D.over.hom ≫ f) f ≫
          (g.hom ()).left) ⁻¹ᵁ W := by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.inv_preimage]
    _ = (homTargetMap g ≫ E.transitionPullbackIso.inv ≫
          pullback.fst (E.over.hom ≫ f) f) ⁻¹ᵁ W := by
        rw [← homSourceMap_comp_fst g, ← Category.assoc, hinv, Category.assoc]
    _ = homTargetMap g ⁻¹ᵁ (pullback.snd f (E.over.hom ≫ f) ⁻¹ᵁ W) := by
        rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage, Scheme.Hom.inv_preimage, hW]
    _ = pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ ((g.hom ()).left ⁻¹ᵁ W) := by
        rw [← Scheme.Hom.comp_preimage, homTargetMap_comp_snd g, Scheme.Hom.comp_preimage]

/-! ### The image of an open sub-datum is an invariant open -/

/-- **The image of a morphism of descent data whose component is an open immersion is an
invariant open.** -/
theorem isTransitionInvariant_opensRange (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    D.IsTransitionInvariant (i.hom ()).left.opensRange := by
  have hab : E.over.hom ≫ f = (i.hom ()).left ≫ (D.over.hom ≫ f) := by
    rw [← Category.assoc, Over.w]
  apply TopologicalSpace.Opens.ext
  rw [Scheme.Hom.coe_image]
  have h1 : ((pullback.fst (D.over.hom ≫ f) f ⁻¹ᵁ (i.hom ()).left.opensRange :
      (pullback (D.over.hom ≫ f) f).Opens) : Set _) = Set.range (homSourceMap i).base :=
    (range_pullbackMapFst_of_isOpenImmersion (i.hom ()).left (D.over.hom ≫ f)
      (E.over.hom ≫ f) f hab (hom_left_comp_over_hom i) (by simp)).symm
  have h2 : ((pullback.snd f (D.over.hom ≫ f) ⁻¹ᵁ (i.hom ()).left.opensRange :
      (pullback f (D.over.hom ≫ f)).Opens) : Set _) = Set.range (homTargetMap i).base :=
    (range_pullbackMapSnd_of_isOpenImmersion (i.hom ()).left (D.over.hom ≫ f)
      (E.over.hom ≫ f) f hab (by simp) (hom_left_comp_over_hom i)).symm
  rw [h1, h2, ← Set.range_comp, show (D.transitionPullbackIso.hom.base ∘ (homSourceMap i).base) =
      (homSourceMap i ≫ D.transitionPullbackIso.hom).base from rfl,
    transitionPullbackIso_naturality i, range_comp_base_of_isIso]

/-! ### The restriction to an invariant open, as an open sub-datum -/

variable (D) in
/-- **The restriction of a descent datum to an invariant open, as an open sub-datum.** Its
component is the open immersion `W ⟶ V` of schemes over `X`. -/
def restrictOpenHom (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    D.restrictOpen W hW ⟶ D where
  hom _ := D.restrictOpenι W
  comm _ _ := (D.restrictOpen_transition_hom_left W hW).symm

variable (D) in
/-- The component of `AlgebraicGeometry.DescentDatum.restrictOpenHom` is the open immersion
`W ⟶ V`. -/
@[simp]
lemma restrictOpenHom_hom_left (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    ((D.restrictOpenHom W hW).hom ()).left = W.ι := rfl

/-- The component of `AlgebraicGeometry.DescentDatum.restrictOpenHom` is an open immersion. -/
instance isOpenImmersion_restrictOpenHom_hom_left (D : DescentDatum f)
    (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    IsOpenImmersion ((D.restrictOpenHom W hW).hom ()).left :=
  inferInstanceAs (IsOpenImmersion W.ι)

/-! ### An open sub-datum is the restriction to its image -/

section Iso

variable (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) (i : E ⟶ D)
  (e : E.over ≅ D.restrictOpenObj W) (he : e.hom ≫ D.restrictOpenι W = i.hom ())

include he in
/-- The component of a morphism of descent data factors through `W ⟶ V` after `f` has been
applied. -/
lemma map_hom_comp_restrictOpenιMap :
    (Over.map f).map e.hom ≫ D.restrictOpenιMap W = (Over.map f).map (i.hom ()) := by
  rw [show D.restrictOpenιMap W = (Over.map f).map (D.restrictOpenι W) from rfl,
    ← Functor.map_comp, he]

include he in
/-- The compatibility square for an identification of the source of an open sub-datum with the
open subscheme cut out by its image. -/
lemma restrictOpenGluing_comm :
    prod.map ((Over.map f).map e.hom) (𝟙 (Over.mk f)) ≫ D.restrictOpenGluing W hW =
      E.transition.hom.left ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map e.hom) := by
  refine (cancel_mono (prod.map (𝟙 (Over.mk f)) (D.restrictOpenιMap W))).mp ?_
  simp only [Category.assoc, D.restrictOpenGluing_comp W hW, prod.map_map,
    prod.map_map_assoc, Category.comp_id, map_hom_comp_restrictOpenιMap W i e he]
  exact i.comm () ()

include he in
/-- The compatibility square for the inverse of an identification of the source of an open
sub-datum with the open subscheme cut out by its image. -/
lemma restrictOpenGluing_comm_inv :
    prod.map ((Over.map f).map e.inv) (𝟙 (Over.mk f)) ≫ E.transition.hom.left =
      D.restrictOpenGluing W hW ≫ prod.map (𝟙 (Over.mk f)) ((Over.map f).map e.inv) := by
  have key := congrArg (fun k => prod.map ((Over.map f).map e.inv) (𝟙 (Over.mk f)) ≫ k ≫
      prod.map (𝟙 (Over.mk f)) ((Over.map f).map e.inv))
    (restrictOpenGluing_comm W hW i e he)
  have hid : E.transition.hom.left ≫ 𝟙 (Over.mk f ⨯ (Over.map f).obj E.over) =
      E.transition.hom.left := Category.comp_id _
  simp only [Category.assoc, prod.map_map, prod.map_map_assoc, Category.comp_id,
    Category.id_comp, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, prod.map_id_id, hid] at key
  exact key.symm

include he in
/-- **An open sub-datum is the restriction to its image.** An identification of the scheme over
`X` carried by `E` with the open subscheme `W ⊆ V`, compatible with the component of
`i : E ⟶ D`, is an isomorphism of descent data `E ≅ D.restrictOpen W hW`. -/
def restrictOpenIso : E ≅ D.restrictOpen W hW where
  hom := { hom := fun _ ↦ e.hom, comm := fun _ _ ↦ restrictOpenGluing_comm W hW i e he }
  inv := { hom := fun _ ↦ e.inv, comm := fun _ _ ↦ restrictOpenGluing_comm_inv W hW i e he }
  hom_inv_id := DescentData.hom_ext fun _ ↦ e.hom_inv_id
  inv_hom_id := DescentData.hom_ext fun _ ↦ e.inv_hom_id

end Iso

/-- The identification of the scheme carried by an open sub-datum with the open subscheme of
`V` cut out by its image, on underlying schemes. -/
def overLeftRestrictOpenIso (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    E.over.left ≅ ((i.hom ()).left.opensRange : D.over.left.Opens).toScheme :=
  IsOpenImmersion.isoOfRangeEq (i.hom ()).left
    ((i.hom ()).left.opensRange : D.over.left.Opens).ι (by rw [Scheme.Opens.range_ι]; rfl)

/-- `AlgebraicGeometry.DescentDatum.overLeftRestrictOpenIso` factors the component of the
morphism it is built from through the open immersion `W ⟶ V`. -/
@[simp]
lemma overLeftRestrictOpenIso_hom_comp_ι (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    (overLeftRestrictOpenIso i).hom ≫
        ((i.hom ()).left.opensRange : D.over.left.Opens).ι = (i.hom ()).left :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The identification of the scheme over `X` carried by an open sub-datum with the open
subscheme of `V` cut out by its image. -/
def overRestrictOpenIso (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    E.over ≅ D.restrictOpenObj (i.hom ()).left.opensRange :=
  Over.isoMk (overLeftRestrictOpenIso i) (by
    change (overLeftRestrictOpenIso i).hom ≫
      ((i.hom ()).left.opensRange : D.over.left.Opens).ι ≫ D.over.hom = E.over.hom
    rw [← Category.assoc, overLeftRestrictOpenIso_hom_comp_ι]
    exact Over.w (i.hom ()))

/-- `AlgebraicGeometry.DescentDatum.overRestrictOpenIso` is compatible with the component of
the morphism it is built from. -/
lemma overRestrictOpenIso_hom_comp (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    (overRestrictOpenIso i).hom ≫ D.restrictOpenι (i.hom ()).left.opensRange = i.hom () := by
  ext
  show (overLeftRestrictOpenIso i).hom ≫
    ((i.hom ()).left.opensRange : D.over.left.Opens).ι = (i.hom ()).left
  exact overLeftRestrictOpenIso_hom_comp_ι i

/-- **An open sub-datum is isomorphic to the restriction of `D` to its image.** -/
def restrictOpenIsoOpensRange (i : E ⟶ D) [IsOpenImmersion (i.hom ()).left] :
    E ≅ D.restrictOpen (i.hom ()).left.opensRange (isTransitionInvariant_opensRange i) :=
  restrictOpenIso _ (isTransitionInvariant_opensRange i) i (overRestrictOpenIso i)
    (overRestrictOpenIso_hom_comp i)

/-! ### Effective open sub-data and invariant open neighbourhoods -/

/-- Through a point `v` of `V` there passes an effective descent datum mapping to `D` by an open
immersion exactly when `v` has an invariant open neighbourhood whose restricted datum is
effective. -/
theorem exists_openImmersionHom_isEffective_iff (D : DescentDatum f) (v : D.over.left) :
    (∃ (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W),
        v ∈ W ∧ DescentData.IsEffective (D.restrictOpen W hW)) ↔
      ∃ (E : DescentDatum f) (i : E ⟶ D) (w : E.over.left),
        IsOpenImmersion (i.hom ()).left ∧ (i.hom ()).left.base w = v ∧
          DescentData.IsEffective E := by
  refine ⟨fun ⟨W, hW, hv, hEff⟩ ↦
    ⟨D.restrictOpen W hW, D.restrictOpenHom W hW, ⟨v, hv⟩, inferInstance, rfl, hEff⟩,
    fun ⟨E, i, w, _, hw, hEff⟩ ↦ ⟨(i.hom ()).left.opensRange, isTransitionInvariant_opensRange i,
      hw ▸ Set.mem_range_self w, hEff.ofIso (restrictOpenIsoOpensRange i)⟩⟩

end DescentDatum

end AlgebraicGeometry

end
