module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.MapDerivationAction
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageChartProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InverseImageRingChartIso
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleThickeningEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpChartOverBase
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine

/-!
# A morphism between two thickenings of one space from a map of inverse-image rings

Let `i₁ : Z ⟶ T₁` and `i₂ : Z ⟶ T₂` be thickenings of algebraic spaces over a scheme `S`, and let
`φ : i₂⁻¹𝒪_{T₂} ⟶ i₁⁻¹𝒪_{T₁}` be a map of sheaves of commutative rings on the small étale site
of `Z`. Base change along `i₁` and along `i₂` identifies the small étale sites of `T₁` and of
`T₂` with that of `Z` ([Stacks Project, Tag 05ZS]), so an étale scheme chart `V` of `T₁` has a
partner chart `V'` of `T₂` with `Z ×_{T₂} V' ≅ Z ×_{T₁} V`, and the two charts are thickenings of
one scheme. Reading `φ` on the sections over that scheme through the identifications
`𝒪(V) ≅ (i⁻¹𝒪)(Z ×_T V)` of `AlgebraicGeometry.Space.inverseImageRingChartIso` gives a map of
rings `Γ(V', 𝒪) ⟶ Γ(V, 𝒪)`, natural in `V`; for `V` affine, `V'` is affine too, and the ring map is
a morphism of schemes `V ⟶ V'`.

These chart morphisms are the local pieces of the morphism `T₁ ⟶ T₂` that [Stacks Project,
Tag 05ZN] attaches to `φ`, and are what the step "`Xₙ ≅ X' ×_Y Yₙ`" of the proof of
[Stacks Project, Tag 0D3X] glues.

## Main definitions

* `AlgebraicGeometry.Space.thickeningChartTransfer`: the functor `V ↦ V'` from the small étale
  site of `T₁` to that of `T₂`, with `thickeningChartTransferIso : Z ×_{T₂} V' ≅ Z ×_{T₁} V`.
* `AlgebraicGeometry.Space.thickeningChartRingHom`: the natural ring map `Γ(V', 𝒪) ⟶ Γ(V, 𝒪)`.
* `AlgebraicGeometry.Space.thickeningChartHom`: the morphism of schemes `V ⟶ V'`, for `V`
  affine.

## Main results

* `AlgebraicGeometry.Space.isAffine_thickeningChartTransfer`: `V'` is affine when `V` is.
* `AlgebraicGeometry.Space.thickeningChartHom_naturality`: the chart morphisms commute with the
  morphisms of affine charts.

## References

* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 05ZS](https://stacks.math.columbia.edu/tag/05ZS)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Z T₁ T₂ : AlgebraicSpaces B S hS} {i₁ : Z ⟶ T₁} {i₂ : Z ⟶ T₂}
  (hi₁ : IsThickeningHom B S hS i₁) (hi₂ : IsThickeningHom B S hS i₂)

/-- **The partner chart.** The functor `V ↦ V'` from the small étale site of `T₁` to that of
`T₂`: base change along `i₁` followed by an inverse of base change along `i₂`, which is an
equivalence by Stacks 05ZS. -/
def thickeningChartTransfer : SmallEtale B S hS T₁.1 ⥤ SmallEtale B S hS T₂.1 :=
  letI := isEquivalence_smallBaseChange_of_isThickeningHom B S hS i₂ hi₂
  smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep ⋙
    (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).inv

/-- `Z ×_{T₂} V' ≅ Z ×_{T₁} V`, naturally in the étale chart `V` of `T₁`. -/
def thickeningChartTransferIso :
    thickeningChartTransfer B S hS hi₁ hi₂ ⋙ smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep ≅
      smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep :=
  letI := isEquivalence_smallBaseChange_of_isThickeningHom B S hS i₂ hi₂
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).asEquivalence.counitIso ≪≫
    Functor.rightUnitor _

variable (φ : (smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O ⟶
    (smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O)

/-- **The ring map of the partner charts**, `Γ(V', 𝒪) ⟶ Γ(V, 𝒪)` naturally in the étale chart
`V` of `T₁`: `𝒪_{T₂}(V') ≅ (i₂⁻¹𝒪_{T₂})(Z ×_{T₂} V')`, then `φ`, then
`(i₁⁻¹𝒪_{T₁})(Z ×_{T₂} V') ≅ (i₁⁻¹𝒪_{T₁})(Z ×_{T₁} V) ≅ 𝒪_{T₁}(V)`. -/
def thickeningChartRingHom :
    (thickeningChartTransfer B S hS hi₁ hi₂).op ⋙ (smallEtaleRingedTopos B S hS T₂).O.obj ⟶
      (smallEtaleRingedTopos B S hS T₁).O.obj :=
  Functor.whiskerLeft (thickeningChartTransfer B S hS hi₁ hi₂).op
      (inverseImageRingChartIso B S hS i₂ hi₂.isClosedImmersion hi₂.surjective
        (smallEtaleRingedTopos B S hS T₂).O).hom ≫
    Functor.whiskerLeft (thickeningChartTransfer B S hS hi₁ hi₂ ⋙
        smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).op φ.hom ≫
    Functor.whiskerRight (NatTrans.op (thickeningChartTransferIso B S hS hi₁ hi₂).inv)
      ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj ≫
    (inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
        (smallEtaleRingedTopos B S hS T₁).O).inv

/-- The base change of an affine étale chart along a closed immersion is affine. -/
theorem isAffine_smallBaseChange_of_isClosedImmersion {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f.hom) (V : SmallEtale B S hS Y.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Y.1).obj V))] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj ((smallBaseChange B S hS f hf.rep).obj V))) := by
  have h : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.rep.snd V.1.hom)) := hf.property_snd V.1.hom
  exact @_root_.AlgebraicGeometry.isAffine_of_isAffineHom _ _ _
    (isAffineHom_of_isInducing _ h.isClosedEmbedding.isInducing h.isClosedEmbedding.isClosed_range)
    (by assumption)

/-- **The partner chart of an affine chart is affine**: `Z ×_{T₂} V' ⟶ V'` is a thickening of
schemes and `Z ×_{T₂} V' ≅ Z ×_{T₁} V` is closed in the affine scheme `V`. -/
theorem isAffine_thickeningChartTransfer (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₂.1).obj
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))) := by
  let V' := (thickeningChartTransfer B S hS hi₁ hi₂).obj V
  have := isAffine_smallBaseChange_of_isClosedImmersion B S hS i₁ hi₁.isClosedImmersion V
  have h₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS Z.1).obj
      ((smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep).obj V'))) :=
    IsAffine.of_isIso ((BigFppfOver.toScheme B S hS).mapIso ((SmallEtale.toOver B S hS Z.1).mapIso
      ((thickeningChartTransferIso B S hS hi₁ hi₂).app V))).hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (hi₂.isClosedImmersion.rep.pullback V'.1.hom)) := h₀
  have hthick : Stacks.Thickenings.IsThickening
      ((BigFppfOver.toScheme B S hS).map (hi₂.isClosedImmersion.rep.snd V'.1.hom)) :=
    ⟨hi₂.isClosedImmersion.property_snd V'.1.hom, (hi₂.surjective.property_snd V'.1.hom).surj⟩
  exact Stacks.Thickenings.isAffine_of_isThickening hthick

/-- **The morphism of partner charts** `V ⟶ V'` for an affine étale chart `V` of `T₁`: the
morphism into the affine scheme `V'` whose map of global regular functions is
`AlgebraicGeometry.Space.thickeningChartRingHom`. -/
def thickeningChartHom (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V) ⟶
      (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₂.1).obj
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)) :=
  haveI := isAffine_thickeningChartTransfer B S hS hi₁ hi₂ V
  Stacks.Thickenings.homOfAppTop ((thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V))

/-- The morphism of partner charts acts on global regular functions as the ring map. -/
theorem thickeningChartHom_appTop (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    (thickeningChartHom B S hS hi₁ hi₂ φ V).appTop =
      (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) :=
  have := isAffine_thickeningChartTransfer B S hS hi₁ hi₂ V
  Stacks.Thickenings.homOfAppTop_appTop _

/-- **The chart morphisms commute with the morphisms of affine charts**: for `r : V₀ ⟶ V`, the
two composites `V₀ ⟶ V'` agree, both having the map of regular functions given by naturality of
`AlgebraicGeometry.Space.thickeningChartRingHom`. -/
theorem thickeningChartHom_naturality {V₀ V : SmallEtale B S hS T₁.1} (r : V₀ ⟶ V)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V₀))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    thickeningChartHom B S hS hi₁ hi₂ φ V₀ ≫ (BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS T₂.1).map ((thickeningChartTransfer B S hS hi₁ hi₂).map r)) =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS T₁.1).map r) ≫
        thickeningChartHom B S hS hi₁ hi₂ φ V := by
  have := isAffine_thickeningChartTransfer B S hS hi₁ hi₂ V
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, thickeningChartHom_appTop,
    thickeningChartHom_appTop]
  have h := (thickeningChartRingHom B S hS hi₁ hi₂ φ).naturality r.op
  simp only [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, smallEtaleRingedTopos,
    structureSheaf_obj, structurePresheaf, Scheme.Γ_map_op] at h
  exact h

/-- **The reduction compatibility of a transported ring map, abstractly.** For functors
`Φ : A ⥤ A₂`, `b₁ : A ⥤ Z`, `b₂ : A₂ ⥤ Z` with `ε : Φ ⋙ b₂ ≅ b₁`, presheaves identified by
`ι₁ : O₁ ≅ b₁ᵒᵖ ⋙ P₁` and `ι₂ : O₂ ≅ b₂ᵒᵖ ⋙ P₂`, and `φ : P₂ ⟶ P₁` with `φ ≫ s₁ = s₂`, the
transported map `Φᵒᵖ ⋙ O₂ ⟶ O₁` followed by `ι₁` and `s₁` is `ι₂` and `s₂` followed by
restriction along `ε⁻¹`. Stated for abstract categories so that it is matched up to definitional
unfolding at concrete sheaves. -/
theorem transport_comp_reduction_app {A A₂ Zc R : Type*} [Category A] [Category A₂]
    [Category Zc] [Category R] (Φ : A ⥤ A₂) (b₁ : A ⥤ Zc) (b₂ : A₂ ⥤ Zc) (ε : Φ ⋙ b₂ ≅ b₁)
    (O₁ : Aᵒᵖ ⥤ R) (O₂ : A₂ᵒᵖ ⥤ R) (P₁ P₂ OZ : Zcᵒᵖ ⥤ R) (ι₁ : O₁ ≅ b₁.op ⋙ P₁)
    (ι₂ : O₂ ≅ b₂.op ⋙ P₂) (φ : P₂ ⟶ P₁) (s₁ : P₁ ⟶ OZ) (s₂ : P₂ ⟶ OZ) (hφ : φ ≫ s₁ = s₂)
    (V : A) :
    (Functor.whiskerLeft Φ.op ι₂.hom ≫ Functor.whiskerLeft (Φ ⋙ b₂).op φ ≫
        Functor.whiskerRight (NatTrans.op ε.inv) P₁ ≫ ι₁.inv).app (op V) ≫
      (ι₁.hom.app (op V) ≫ s₁.app (op (b₁.obj V))) =
    (ι₂.hom.app (op (Φ.obj V)) ≫ s₂.app (op (b₂.obj (Φ.obj V)))) ≫
      OZ.map (ε.inv.app V).op := by
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatTrans.op_app, Category.assoc, Iso.inv_hom_id_app_assoc, ← hφ, NatTrans.comp_app]
  congr 2
  exact s₁.naturality (ε.inv.app V).op

/-- **The inverse-image structure map on the charts of the ambient space is pullback of
regular functions along the cartesian projection**: `𝒪_T(V) ≅ (i⁻¹𝒪_T)(Z ×_T V) --i♯-->
𝒪_Z(Z ×_T V)` is `Γ(Z ×_T V ⟶ V)`. This is
`AlgebraicGeometry.Space.inverseImageRingChartIso_hom_comp_fSharpInverseImage` combined with
Stacks 03G8, part (2),
`AlgebraicGeometry.Space.fSharp_comp_smallEtaleRingedToposHom_representableRing`. -/
theorem inverseImageRingChartIso_hom_app_comp_fSharpInverseImage {X Y : AlgebraicSpaces B S hS}
    (i : X ⟶ Y) (hi : IsThickeningHom B S hS i) (V : SmallEtale B S hS Y.1) :
    (inverseImageRingChartIso B S hS i hi.isClosedImmersion hi.surjective
        (smallEtaleRingedTopos B S hS Y).O).hom.app (op V) ≫
      (smallEtaleRingedToposHom B S hS i).fSharpInverseImage.hom.app
        (op ((smallBaseChange B S hS i hi.isClosedImmersion.rep).obj V)) =
    ((BigFppfOver.toScheme B S hS).map
      ((cartesianProjectionOver B S hS i hi.isClosedImmersion.rep).app V)).appTop := by
  have h := NatTrans.congr_app (inverseImageRingChartIso_hom_comp_fSharpInverseImage B S hS i
    hi.isClosedImmersion hi.surjective) (op V)
  rw [fSharp_comp_smallEtaleRingedToposHom_representableRing] at h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.op_obj,
    cartesianProjectionSharpCommRing, cartesianProjection, Functor.whiskerRight_app,
    NatTrans.op_app, Scheme.Γ_map_op] using h

/-- **The partner-chart ring map is compatible with the reductions** as soon as `φ` is: if
`φ ≫ i₁♯ = i₂♯`, then `Γ(V') ⟶ Γ(V) ⟶ Γ(Z ×_{T₁} V)` is `Γ(V') ⟶ Γ(Z ×_{T₂} V') ≅
Γ(Z ×_{T₁} V)`. -/
theorem thickeningChartRingHom_comp_appTop_cartesianProjection
    (hφ : φ ≫ (smallEtaleRingedToposHom B S hS i₁).fSharpInverseImage =
      (smallEtaleRingedToposHom B S hS i₂).fSharpInverseImage) (V : SmallEtale B S hS T₁.1) :
    (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) ≫
        ((BigFppfOver.toScheme B S hS).map
          ((cartesianProjectionOver B S hS i₁ hi₁.isClosedImmersion.rep).app V)).appTop =
      ((BigFppfOver.toScheme B S hS).map
          ((cartesianProjectionOver B S hS i₂ hi₂.isClosedImmersion.rep).app
            ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))).appTop ≫
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map
          ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V))).appTop := by
  rw [← inverseImageRingChartIso_hom_app_comp_fSharpInverseImage B S hS i₁ hi₁ V,
    ← inverseImageRingChartIso_hom_app_comp_fSharpInverseImage B S hS i₂ hi₂
      ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)]
  exact transport_comp_reduction_app (thickeningChartTransfer B S hS hi₁ hi₂)
    (smallBaseChange B S hS i₁ hi₁.isClosedImmersion.rep)
    (smallBaseChange B S hS i₂ hi₂.isClosedImmersion.rep)
    (thickeningChartTransferIso B S hS hi₁ hi₂)
    (smallEtaleRingedTopos B S hS T₁).O.obj (smallEtaleRingedTopos B S hS T₂).O.obj
    ((smallEtaleInverseImageRing B S hS i₁).obj (smallEtaleRingedTopos B S hS T₁).O).obj
    ((smallEtaleInverseImageRing B S hS i₂).obj (smallEtaleRingedTopos B S hS T₂).O).obj
    (smallEtaleRingedTopos B S hS Z).O.obj
    (inverseImageRingChartIso B S hS i₁ hi₁.isClosedImmersion hi₁.surjective
      (smallEtaleRingedTopos B S hS T₁).O)
    (inverseImageRingChartIso B S hS i₂ hi₂.isClosedImmersion hi₂.surjective
      (smallEtaleRingedTopos B S hS T₂).O)
    φ.hom (smallEtaleRingedToposHom B S hS i₁).fSharpInverseImage.hom
    (smallEtaleRingedToposHom B S hS i₂).fSharpInverseImage.hom
    (congrArg (fun f => f.hom) hφ) V

/-! ### Gluing chart morphisms: the glued morphism restricts correctly on every affine chart -/

section Glue

variable {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
  (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
    ∀ b : yoneda.obj T ⟶ F, IsEtale B S hS b → (yoneda.obj T ⟶ W))
  (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ F)
    (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
    yoneda.map r ≫ k U hU b hb = k T hT (yoneda.map r ≫ b) hrb)

include hF hW hk in
/-- **A compatible family of morphisms on the affine étale charts of an algebraic space glues to
a morphism restricting to the family on every affine étale chart.** This strengthens
`AlgebraicGeometry.Space.exists_hom_of_chartHoms`, whose glued morphism is described only on the
charts factoring through the atlas used to glue: an arbitrary affine chart `w : T ⟶ F` is
compared with the atlas over the fibre product `R = T ×_F U`, whose projection to `T` is a
surjective étale atlas of `T` and whose affine étale charts factor through `U`. -/
theorem exists_hom_forall_chartHoms :
    ∃ l : F ⟶ W, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (w : yoneda.obj T ⟶ F) (hw : IsEtale B S hS w), w ≫ l = k T hT w hw := by
  obtain ⟨U, b, hbsurj, hbet⟩ := hF.exists_atlas
  have hbE : IsEtale B S hS b := (isEtale_iff_presheaf_of_yoneda B S hS b).2 hbet
  obtain ⟨l, hl⟩ := exists_hom_of_chartHoms B S hS hW k hk hF.isSheaf U b hbE hbsurj
  refine ⟨l, fun T hT w hw => ?_⟩
  have hrep := relativelyRepresentable_of_isAlgebraicSpace B S hS hF b
  let R := hrep.pullback w
  let f' : R ⟶ U := yoneda.preimage (hrep.fst w)
  have hf' : yoneda.map f' = hrep.fst w := yoneda.map_preimage _
  have hsq : IsPullback (yoneda.map (hrep.snd w)) (yoneda.map f') w b := by
    rw [hf']; exact (hrep.isPullback w).flip
  have hsndE : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hrep.snd w)) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (hrep.isPullback w) hbet
  have hsndS : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (hrep.snd w)) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (hrep.isPullback w) hbsurj
  refine hom_ext_of_etale_atlas B S hS (isAlgebraicSpace_yoneda B S hS T).isSheaf hW
    (yoneda.map (hrep.snd w)) hsndS hsndE ?_
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS R
  refine hom_ext_of_cover B S hS hW R V π hcover fun i => ?_
  have h1 : IsEtale B S hS (yoneda.map (π i ≫ hrep.snd w) ≫ w) := by
    simpa only [Functor.map_comp, Category.assoc] using isEtale_comp B S hS (hπ i)
      (isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS _).2 hsndE) hw)
  have hfw : yoneda.map (π i ≫ f') ≫ b = yoneda.map (π i ≫ hrep.snd w) ≫ w := by
    simp only [Functor.map_comp, Category.assoc, hsq.w]
  have h2 : IsEtale B S hS (yoneda.map (π i ≫ f') ≫ b) := hfw ▸ h1
  calc yoneda.map (π i) ≫ yoneda.map (hrep.snd w) ≫ w ≫ l
      = yoneda.map (π i ≫ f') ≫ b ≫ l := by
        simp only [← Category.assoc, ← Functor.map_comp, hfw]
    _ = k (V i) (hV i) (yoneda.map (π i ≫ f') ≫ b) h2 := hl (V i) (hV i) _ h2
    _ = k (V i) (hV i) (yoneda.map (π i ≫ hrep.snd w) ≫ w) h1 := by congr 1
    _ = yoneda.map (π i) ≫ yoneda.map (hrep.snd w) ≫ k T hT w hw := by
        simpa only [Functor.map_comp, Category.assoc] using
          (hk (V i) T (hV i) hT (π i ≫ hrep.snd w) w hw h1).symm

end Glue

/-! ### The chart morphisms over an affine base, and the glued morphism -/

section Base

variable {D : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj D)]
  (p₁ : T₁.1 ⟶ yoneda.obj D) (p₂ : T₂.1 ⟶ yoneda.obj D)
  (hbase : ∀ V : SmallEtale B S hS T₁.1,
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂))).appTop ≫
      (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) =
    ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁))).appTop)

include hbase in
/-- **The chart morphism lies over the base**: `V ⟶ V' ⟶ D` is `V ⟶ D`, both being morphisms
into the affine scheme `D` with the same map of regular functions. -/
theorem thickeningChartHom_comp_base (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    thickeningChartHom B S hS hi₁ hi₂ φ V ≫ (BigFppfOver.toScheme B S hS).map (yoneda.preimage
        (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂)) =
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁)) := by
  refine ext_of_isAffine ?_
  rw [Scheme.Hom.comp_appTop, thickeningChartHom_appTop]
  exact hbase V

include hbase in
/-- The chart morphism commutes with the structure morphisms to `S`. -/
theorem thickeningChartHom_comp_structureHom (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    thickeningChartHom B S hS hi₁ hi₂ φ V ≫ B.inclusion.map ((SmallEtale.toOver B S hS T₂.1).obj
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V)).hom =
      B.inclusion.map ((SmallEtale.toOver B S hS T₁.1).obj V).hom :=
  calc _ = thickeningChartHom B S hS hi₁ hi₂ φ V ≫ ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂)) ≫
            B.inclusion.map D.hom) :=
        congrArg _ (BigFppfOver.toScheme_map_comp_inclusion_map_structureHom B S hS _).symm
    _ = (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.1.hom ≫ p₁)) ≫
          B.inclusion.map D.hom := by
        rw [← Category.assoc, thickeningChartHom_comp_base B S hS hi₁ hi₂ φ p₁ p₂ hbase V]
    _ = _ := BigFppfOver.toScheme_map_comp_inclusion_map_structureHom B S hS _

/-- **The chart morphism `V ⟶ V'` as a morphism of the big fppf site of `S`.** -/
def thickeningChartSiteHom (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    (SmallEtale.toOver B S hS T₁.1).obj V ⟶
      (SmallEtale.toOver B S hS T₂.1).obj ((thickeningChartTransfer B S hS hi₁ hi₂).obj V) :=
  Over.homMk (B.inclusion.preimage (thickeningChartHom B S hS hi₁ hi₂ φ V))
    (B.inclusion.map_injective (by
      rw [Functor.map_comp, Functor.map_preimage]
      exact thickeningChartHom_comp_structureHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V))

/-- The site morphism has the chart morphism as underlying morphism of schemes. -/
theorem toScheme_map_thickeningChartSiteHom (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    (BigFppfOver.toScheme B S hS).map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) =
      thickeningChartHom B S hS hi₁ hi₂ φ V :=
  B.inclusion.map_preimage _

/-- The site morphisms commute with the morphisms of affine charts. -/
theorem thickeningChartSiteHom_naturality {V₀ V : SmallEtale B S hS T₁.1} (r : V₀ ⟶ V)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V₀))]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V₀ ≫
        (SmallEtale.toOver B S hS T₂.1).map ((thickeningChartTransfer B S hS hi₁ hi₂).map r) =
      (SmallEtale.toOver B S hS T₁.1).map r ≫
        thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V :=
  (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, Functor.map_comp, toScheme_map_thickeningChartSiteHom,
      toScheme_map_thickeningChartSiteHom]
    exact thickeningChartHom_naturality B S hS hi₁ hi₂ φ r)

/-- The site morphism lies over the base `D`. -/
theorem thickeningChartSiteHom_comp_base (V : SmallEtale B S hS T₁.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))] :
    yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂ = V.1.hom ≫ p₁ := by
  have h : thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V ≫
      yoneda.preimage (((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom ≫ p₂) =
        yoneda.preimage (V.1.hom ≫ p₁) :=
    (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, toScheme_map_thickeningChartSiteHom]
      exact thickeningChartHom_comp_base B S hS hi₁ hi₂ φ p₁ p₂ hbase V)
  simpa only [Functor.map_comp, Functor.map_preimage] using congrArg yoneda.map h

/-- The étale chart of `T₁` given by an étale morphism from a represented presheaf. -/
abbrev chartOfEtale {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : BigFppfOver B S hS)
    (w : yoneda.obj T ⟶ F) (hw : IsEtale B S hS w) : SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk w, (isEtale_iff_presheaf_of_yoneda B S hS w).1 hw⟩

/-- The local piece of the morphism `T₁ ⟶ T₂` over an affine étale chart `w : T ⟶ T₁`:
`T ⟶ T' ⟶ T₂`. -/
def thickeningChartLocalHom (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (w : yoneda.obj T ⟶ T₁.1) (hw : IsEtale B S hS w) : yoneda.obj T ⟶ T₂.1 :=
  haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS T₁.1).obj (chartOfEtale B S hS T w hw))) := hT
  yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase
      (chartOfEtale B S hS T w hw)) ≫
    ((thickeningChartTransfer B S hS hi₁ hi₂).obj (chartOfEtale B S hS T w hw)).1.hom

/-- The local pieces are compatible with the morphisms of affine charts. -/
theorem thickeningChartLocalHom_comp (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (hU : IsAffineOver B S hS U) (r : T ⟶ U) (w : yoneda.obj U ⟶ T₁.1)
    (hw : IsEtale B S hS w) (hrw : IsEtale B S hS (yoneda.map r ≫ w)) :
    yoneda.map r ≫ thickeningChartLocalHom B S hS hi₁ hi₂ φ p₁ p₂ hbase U hU w hw =
      thickeningChartLocalHom B S hS hi₁ hi₂ φ p₁ p₂ hbase T hT (yoneda.map r ≫ w) hrw := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS T₁.1).obj (chartOfEtale B S hS T _ hrw))) := hT
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS T₁.1).obj (chartOfEtale B S hS U w hw))) := hU
  let m : chartOfEtale B S hS T _ hrw ⟶ chartOfEtale B S hS U w hw :=
    ObjectProperty.homMk (CostructuredArrow.homMk r rfl)
  unfold thickeningChartLocalHom
  calc _ = yoneda.map ((SmallEtale.toOver B S hS T₁.1).map m ≫
        thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase (chartOfEtale B S hS U w hw)) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj (chartOfEtale B S hS U w hw)).1.hom := by
        rw [Functor.map_comp_assoc]; rfl
    _ = yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase
          (chartOfEtale B S hS T _ hrw) ≫ (SmallEtale.toOver B S hS T₂.1).map
            ((thickeningChartTransfer B S hS hi₁ hi₂).map m)) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj (chartOfEtale B S hS U w hw)).1.hom := by
        rw [thickeningChartSiteHom_naturality B S hS hi₁ hi₂ φ p₁ p₂ hbase m]
    _ = _ := by
        rw [Functor.map_comp_assoc]
        exact congrArg _ (CostructuredArrow.w ((thickeningChartTransfer B S hS hi₁ hi₂).map m).hom)

/-- **The morphism `T₁ ⟶ T₂` attached to `φ` over the affine base `D`**: on every affine étale
chart `V` of `T₁` it is `V ⟶ V' ⟶ T₂`. -/
theorem exists_hom_of_thickeningChartSiteHom :
    ∃ g : T₁ ⟶ T₂, ∀ (V : SmallEtale B S hS T₁.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))],
      V.1.hom ≫ g.hom = yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom := by
  obtain ⟨l, hl⟩ := exists_hom_forall_chartHoms B S hS T₁.2 T₂.2.isSheaf
    (thickeningChartLocalHom B S hS hi₁ hi₂ φ p₁ p₂ hbase)
    (thickeningChartLocalHom_comp B S hS hi₁ hi₂ φ p₁ p₂ hbase)
  refine ⟨ObjectProperty.homMk l, fun V hV => ?_⟩
  exact hl V.1.left hV V.1.hom ((isEtale_iff_presheaf_of_yoneda B S hS _).2 V.2)

/-- **A morphism out of an algebraic space into a sheaf is determined on the affine étale
charts.** -/
theorem hom_ext_of_affineEtaleCharts {F : AlgebraicSpaces B S hS}
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W) {a b : F.1 ⟶ W}
    (hab : ∀ V : SmallEtale B S hS F.1,
      IsAffineOver B S hS ((SmallEtale.toOver B S hS F.1).obj V) → V.1.hom ≫ a = V.1.hom ≫ b) :
    a = b := by
  have hY : yoneda.relativelyRepresentable (Over.mk (𝟙 F)).hom.hom :=
    Functor.relativelyRepresentable.of_isIso (F := yoneda) (𝟙 F.1)
  refine hom_ext_of_affineChartBaseChange B S hS (Over.mk (𝟙 F)) hY hW fun V hV => ?_
  have hw : hY.fst V.1.hom = yoneda.map (hY.snd V.1.hom) ≫ V.1.hom :=
    (Category.comp_id _).symm.trans (hY.w V.1.hom)
  show hY.fst V.1.hom ≫ a = hY.fst V.1.hom ≫ b
  rw [hw, Category.assoc, Category.assoc, hab V hV]

variable (hred : ∀ V : SmallEtale B S hS T₁.1,
    (thickeningChartRingHom B S hS hi₁ hi₂ φ).app (op V) ≫
        ((BigFppfOver.toScheme B S hS).map
          ((cartesianProjectionOver B S hS i₁ hi₁.isClosedImmersion.rep).app V)).appTop =
      ((BigFppfOver.toScheme B S hS).map
          ((cartesianProjectionOver B S hS i₂ hi₂.isClosedImmersion.rep).app
            ((thickeningChartTransfer B S hS hi₁ hi₂).obj V))).appTop ≫
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS Z.1).map
          ((thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V))).appTop)

include hred in
/-- **The glued morphism restricts to `i₂` along `i₁`**: on the base change `Z ×_{T₁} V` of an
affine étale chart, `Z ×_{T₁} V ⟶ V ⟶ V'` and `Z ×_{T₁} V ≅ Z ×_{T₂} V' ⟶ V'` have the same
map of regular functions, which is the hypothesis `hred`. -/
theorem comp_eq_of_thickeningChartSiteHom (g : T₁ ⟶ T₂)
    (hg : ∀ (V : SmallEtale B S hS T₁.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))],
      V.1.hom ≫ g.hom = yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom) :
    i₁ ≫ g = i₂ := by
  refine ObjectProperty.hom_ext _ ?_
  have hY : yoneda.relativelyRepresentable (Over.mk i₁).hom.hom := hi₁.isClosedImmersion.rep
  refine hom_ext_of_affineChartBaseChange B S hS (Over.mk i₁) hY T₂.2.isSheaf fun V hV => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V)) :=
    hV
  have := isAffine_thickeningChartTransfer B S hS hi₁ hi₂ V
  let rep₁ := hi₁.isClosedImmersion.rep
  let rep₂ := hi₂.isClosedImmersion.rep
  let V' := (thickeningChartTransfer B S hS hi₁ hi₂).obj V
  let e := (thickeningChartTransferIso B S hS hi₁ hi₂).inv.app V
  let e' : rep₁.pullback V.1.hom ⟶ rep₂.pullback V'.1.hom := (SmallEtale.toOver B S hS Z.1).map e
  have hew : yoneda.map e' ≫ rep₂.fst V'.1.hom = rep₁.fst V.1.hom := CostructuredArrow.w e.hom
  show rep₁.fst V.1.hom ≫ i₁.hom ≫ g.hom = rep₁.fst V.1.hom ≫ i₂.hom
  have key : yoneda.map (rep₁.snd V.1.hom) ≫
      yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) =
        yoneda.map e' ≫ yoneda.map (rep₂.snd V'.1.hom) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    refine congrArg yoneda.map ?_
    refine (BigFppfOver.toScheme B S hS).map_injective (ext_of_isAffine ?_)
    rw [Functor.map_comp, Scheme.Hom.comp_appTop, toScheme_map_thickeningChartSiteHom,
      thickeningChartHom_appTop]
    simp only [Functor.map_comp, Scheme.Hom.comp_appTop]
    exact hred V
  rw [← Category.assoc, rep₁.w, Category.assoc, hg V, ← Category.assoc, key, Category.assoc,
    ← rep₂.w, ← Category.assoc, hew]

include hbase in
/-- **The glued morphism lies over the base `D`.** -/
theorem comp_base_eq_of_thickeningChartSiteHom (g : T₁ ⟶ T₂)
    (hg : ∀ (V : SmallEtale B S hS T₁.1)
      [IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V))],
      V.1.hom ≫ g.hom = yoneda.map (thickeningChartSiteHom B S hS hi₁ hi₂ φ p₁ p₂ hbase V) ≫
        ((thickeningChartTransfer B S hS hi₁ hi₂).obj V).1.hom) :
    g.hom ≫ p₂ = p₁ := by
  refine hom_ext_of_affineEtaleCharts B S hS (isAlgebraicSpace_yoneda B S hS D).isSheaf
    fun V hV => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS T₁.1).obj V)) :=
    hV
  rw [← Category.assoc, hg V, Category.assoc]
  exact thickeningChartSiteHom_comp_base B S hS hi₁ hi₂ φ p₁ p₂ hbase V

end Base

end AlgebraicGeometry.Space

end
