module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleBaseChangeRings
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit

/-!
# A chosen affine étale model of each stage base change

Let `R` be a topological ring presenting an affine formal algebraic space `Spf R` over `S` and
let `v : V ⟶ Spf R` be a morphism from an affine formal algebraic space which is representable
by algebraic spaces and étale. For each weak ideal of definition `J ⊆ R` the base change

`Spec (R ⧸ J) ×_{Spf R} V`

is represented by an affine scheme étale over `Spec (R ⧸ J)`
(`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`). Such a representing object is
chosen here for every `J` at once, together with the étale ring map on global sections that the
choice determines, and the chosen objects form a diagram indexed by the weak ideals of
definition.

## Main definitions

* `AlgebraicGeometry.FormalSpace.stageBaseChangeModel`: the chosen object of the site
  representing `Spec (R ⧸ J) ×_{Spf R} V`, with its cartesian square, affineness and étaleness.
* `AlgebraicGeometry.FormalSpace.stageBaseChangeRing`: its coordinate ring.
* `AlgebraicGeometry.FormalSpace.stageBaseChangeRingHom`: the ring map `R ⧸ J → \bar A_J`.
* `AlgebraicGeometry.FormalSpace.isoStageBaseChange`: the chosen object represents the stage of
  `AlgebraicGeometry.FormalSpace.stageBaseChangeDiagram`.

## Main results

* `AlgebraicGeometry.FormalSpace.etale_stageBaseChangeRingHom`: the ring map is étale.

## References

* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-- Cancelling the inverse of an isomorphism at the end of a composite:
`(h ≫ m ≫ e.inv) ≫ e.hom = h ≫ m`. -/
private theorem comp_assoc_inv_hom_id {C : Type*} [Category C] {W X Y Z : C}
    (h : W ⟶ X) (m : X ⟶ Z) (e : Y ≅ Z) : (h ≫ m ≫ e.inv) ≫ e.hom = h ≫ m := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem 𝔅 S hS R)
  {V : FppfSheaf 𝔅 S hS} (v : V ⟶ formalSpectrum D)

/-- The underlying scheme of a quotient stage of the canonical presentation of a formal
spectrum is affine: it is `Spec (R ⧸ J)`. -/
theorem isAffine_toScheme_stage (J : WeakIdeals R) :
    IsAffine ((BigFppfOver.toScheme 𝔅 S hS).obj
      ((BigAffineFppf.inclusion 𝔅 S hS).obj (D.diagram.obj J))) := by
  show IsAffine (Spec (.of (R ⧸ (OrderDual.ofDual J).1)))
  infer_instance

variable (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D))
  (hV : IsAffineFormalAlgebraicSpace 𝔅 S hS V) (hv : IsRepresentableEtale 𝔅 S hS v)

/-- **The chosen affine model of the base change of `V` to the quotient stage at `J`.** An
object of the site representing `Spec (R ⧸ J) ×_{Spf R} V`, together with the cartesian square
exhibiting it as that fibre product, the affineness of its underlying scheme and the étaleness
of its projection to `Spec (R ⧸ J)`. -/
noncomputable def stageBaseChangeModel (J : WeakIdeals R) :
    AffineEtaleBaseChange 𝔅 S hS (formalSpectrum D)
      ((BigAffineFppf.inclusion 𝔅 S hS).obj (D.diagram.obj J))
      (formalSpectrumInclusion D J) ⟨Over.mk v, hV, hv⟩ :=
  affineEtaleBaseChangeData 𝔅 S hS hY _ (isAffine_toScheme_stage D J)
    (formalSpectrumInclusion D J) ⟨Over.mk v, hV, hv⟩

/-- **The chosen affine model represents the stage of the base-change diagram.** The cartesian
square of `AlgebraicGeometry.FormalSpace.stageBaseChangeModel`, read as an isomorphism with the
chosen fibre product `Spec (R ⧸ J) ×_{Spf R} V`. -/
noncomputable def isoStageBaseChange (J : WeakIdeals R) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).obj
        (stageBaseChangeModel D v hY hV hv J).obj ≅ (stageBaseChangeDiagram D v).obj J :=
  (stageBaseChangeModel D v hY hV hv J).isPullback.flip.isoPullback

/-- The isomorphism `AlgebraicGeometry.FormalSpace.isoStageBaseChange` followed by the projection
`pullback.snd` to `V` is the morphism `fst` of the chosen model. -/
@[reassoc (attr := simp)]
theorem isoStageBaseChange_hom_snd (J : WeakIdeals R) :
    (isoStageBaseChange D v hY hV hv J).hom ≫
        pullback.snd (formalSpectrumInclusion D J) v =
      (stageBaseChangeModel D v hY hV hv J).fst :=
  (stageBaseChangeModel D v hY hV hv J).isPullback.flip.isoPullback_hom_snd

/-- The isomorphism `AlgebraicGeometry.FormalSpace.isoStageBaseChange` followed by the projection
`pullback.fst` to the quotient stage is the image of the projection `proj` of the chosen model. -/
@[reassoc (attr := simp)]
theorem isoStageBaseChange_hom_fst (J : WeakIdeals R) :
    (isoStageBaseChange D v hY hV hv J).hom ≫
        pullback.fst (formalSpectrumInclusion D J) v =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModel D v hY hV hv J).proj :=
  (stageBaseChangeModel D v hY hV hv J).isPullback.flip.isoPullback_hom_fst

/-- The coordinate ring `\bar A_J` of the chosen affine model of `Spec (R ⧸ J) ×_{Spf R} V`. -/
noncomputable def stageBaseChangeRing (J : WeakIdeals R) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme 𝔅 S hS).obj (stageBaseChangeModel D v hY hV hv J).obj, ⊤)

/-- The ring map `R ⧸ J → \bar A_J` induced on global sections by the projection of the chosen
affine model of `Spec (R ⧸ J) ×_{Spf R} V` to `Spec (R ⧸ J)`. -/
noncomputable def stageBaseChangeRingHom (J : WeakIdeals R) :
    (R ⧸ (OrderDual.ofDual J).1) →+* stageBaseChangeRing D v hY hV hv J :=
  ((BigFppfOver.toScheme 𝔅 S hS).map
      (stageBaseChangeModel D v hY hV hv J).proj).appTop.hom.comp
    (Scheme.ΓSpecIso (.of (R ⧸ (OrderDual.ofDual J).1))).inv.hom

/-- **The chosen affine model of `Spec (R ⧸ J) ×_{Spf R} V` is étale over `Spec (R ⧸ J)`, as a
ring map.** -/
theorem etale_stageBaseChangeRingHom (J : WeakIdeals R) :
    RingHom.Etale (stageBaseChangeRingHom D v hY hV hv J) := by
  have _ := isAffine_toScheme_stage D (hS := hS) J
  have _ := (stageBaseChangeModel D v hY hV hv J).isAffine
  have h := HasRingHomProperty.appTop @Etale
    ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModel D v hY hV hv J).proj)
    (stageBaseChangeModel D v hY hV hv J).etale
  exact RingHom.Etale.stableUnderComposition
    (Scheme.ΓSpecIso (.of (R ⧸ (OrderDual.ofDual J).1))).inv.hom
    ((BigFppfOver.toScheme 𝔅 S hS).map
      (stageBaseChangeModel D v hY hV hv J).proj).appTop.hom
    (RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of (R ⧸ (OrderDual.ofDual J).1))).inv)) h

/-- The transition morphism of the chosen affine models over an inclusion `K ⊆ J` of weak
ideals of definition: the transition of the stage base changes, transported through
`AlgebraicGeometry.FormalSpace.isoStageBaseChange` and the full faithfulness of the sheafified
Yoneda embedding. -/
noncomputable def stageBaseChangeModelMap {J K : WeakIdeals R} (g : J ⟶ K) :
    (stageBaseChangeModel D v hY hV hv J).obj ⟶ (stageBaseChangeModel D v hY hV hv K).obj :=
  (sheafifiedYonedaFF 𝔅 S hS).preimage
    ((isoStageBaseChange D v hY hV hv J).hom ≫ (stageBaseChangeDiagram D v).map g ≫
      (isoStageBaseChange D v hY hV hv K).inv)

/-- **The chosen affine models of the stage base changes form a diagram of affine objects of
the site**, indexed by the weak ideals of definition of `R` ordered by reverse inclusion. -/
noncomputable def stageBaseChangeModelDiagram : WeakIdeals R ⥤ BigFppfOver 𝔅 S hS where
  obj J := (stageBaseChangeModel D v hY hV hv J).obj
  map g := stageBaseChangeModelMap D v hY hV hv g
  map_id _ := by
    simp only [stageBaseChangeModelMap, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.hom_inv_id, Functor.FullyFaithful.preimage_id]
  map_comp _ _ := by
    simp only [stageBaseChangeModelMap, ← Functor.FullyFaithful.preimage_comp,
      Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]

/-- The image under the sheafified Yoneda embedding of a transition morphism of
`AlgebraicGeometry.FormalSpace.stageBaseChangeModelDiagram` is the transition morphism of
`AlgebraicGeometry.FormalSpace.stageBaseChangeDiagram`, conjugated by
`AlgebraicGeometry.FormalSpace.isoStageBaseChange`. -/
theorem map_stageBaseChangeModelDiagram_map {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        ((stageBaseChangeModelDiagram D v hY hV hv).map g) =
      (isoStageBaseChange D v hY hV hv J).hom ≫ (stageBaseChangeDiagram D v).map g ≫
        (isoStageBaseChange D v hY hV hv K).inv :=
  (sheafifiedYonedaFF 𝔅 S hS).map_preimage _

/-- **The diagram of chosen affine models represents the diagram of stage base changes**, with
components `AlgebraicGeometry.FormalSpace.isoStageBaseChange`. -/
noncomputable def stageBaseChangeModelDiagramIso :
    stageBaseChangeModelDiagram D v hY hV hv ⋙
        Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS) ≅ stageBaseChangeDiagram D v :=
  NatIso.ofComponents (isoStageBaseChange D v hY hV hv) fun g ↦ by
    rw [Functor.comp_map, map_stageBaseChangeModelDiagram_map]
    exact comp_assoc_inv_hom_id _ _ _

end AlgebraicGeometry.FormalSpace

end
