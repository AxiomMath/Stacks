module

public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.AffineStage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SchemeStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteLocallyFreeStageModel
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCoverTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleOpenLocusOfApproximation

/-!
# Stacks 0D3D from a Noetherian approximation indexed below the cofinality of the cutoff

`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
proves Stacks 0D3D from its inputs with the standing convention of Section 70.2 (tag 07SD) read
as an abstract property `Conv` of inverse systems. This file instantiates `Conv` with the form
the library gives that convention: the index category has fewer objects, and fewer morphisms
between any two objects, than the cofinality of the site's size cutoff (the hypothesis `hI` of
Stacks 07SQ, `AlgebraicGeometry.Space.DescentSituation.exists_isAffineSpace_system_obj`, and of
Stacks 07SR, `AlgebraicGeometry.Space.DescentSituation.exists_isRepresentable_system_obj`).
With that choice the inputs Stacks 07SQ, 07SR, 07SF, 0D2X and the two consequences of the
convention are all proved, and the statement depends only on Stacks 0A0X, for a system indexed
below the cofinality, and on Stacks 0D3A.

## Main results

* `AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift`: the underlying scheme functor
  preserves the limit of the stages over a fixed stage of a system with affine transition
  morphisms, once those stages are represented by objects of the site.
* `AlgebraicGeometry.Space.DescentSituation.exists_isInvertibleModule_stage_model`: Stacks 0D2X,
  part (2), in the situation of Stacks 084R, with the chosen limit of the situation.
* `Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_boundedApproximation`: the
  statement of Stacks 0D3D from Stacks 0A0X, for systems indexed below the cofinality of the site's
  size cutoff, and Stacks 0D3A.

## Implementation notes

The approximation asked for in `h0A0X` is indexed below the cofinality of the site's cutoff.
It need not exist on every site (for a field `F` of size at least that cofinality, `Spec F`
admits no such approximation by schemes of finite presentation over `ℤ`), so this form of the
statement is useful only on sites where it does, or once the inputs are recast in a
cofinality-free form. Nothing here is registered.

## References

* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
* [Stacks Project, Tag 0A0X](https://stacks.math.columbia.edu/tag/0A0X)
* [Stacks Project, Tag 0D2X](https://stacks.math.columbia.edu/tag/0D2X)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A lift `W` of the stages over `i₀` of a system of presheaves with affine transition
morphisms has affine transition morphisms of underlying schemes. -/
private theorem isAffineHom_underlyingDiagram_map_of_iso {J : Type u} [Category.{u} J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : J)
    (W : Over i₀ ⥤ BigFppfOver B S hS) (e : W ⋙ yoneda ≅ Over.forget i₀ ⋙ D)
    {a b : Over i₀} (f : a ⟶ b) :
    _root_.AlgebraicGeometry.IsAffineHom ((AlgebraicGeometry.underlyingDiagram W).map f) := by
  apply isAffineHom_toScheme_map_of_isAffineHom B S hS
  have h : yoneda.map (W.map f) = e.hom.app a ≫ D.map f.left ≫ e.inv.app b := by
    have hn := e.hom.naturality f
    simp only [Functor.comp_map, Over.forget_map] at hn
    rw [← reassoc_of% hn]
    simp
  rw [h]
  exact isAffineHom_comp B S hS _ _ (isAffineHom_of_isIso _)
    (isAffineHom_comp B S hS _ _ (hAffine f.left) (isAffineHom_of_isIso _))

/-- A limit of the underlying schemes of a cofiltered diagram in the big fppf site with affine
transition morphisms, indexed below the cofinality of the site's cutoff, lies in the site. -/
private theorem size_lt_cutoff_of_isLimit_underlyingDiagram {K : Type u} [Category.{u} K]
    [IsCofiltered K] (hK : #K < B.cutoff.ord.cof)
    (hKH : ∀ a b : K, #(a ⟶ b) < B.cutoff.ord.cof) (W : K ⥤ BigFppfOver B S hS)
    (hW : ∀ {a b : K} (f : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom ((AlgebraicGeometry.underlyingDiagram W).map f))
    (c : Cone (AlgebraicGeometry.underlyingDiagram W)) (hc : IsLimit c) :
    c.pt.size < B.cutoff := by
  classical
  let E := AlgebraicGeometry.underlyingDiagram W
  have hE : ∀ k, (E.obj k).size < B.cutoff := fun k => (W.obj k).left.property
  obtain ⟨j⟩ := IsCofiltered.nonempty (C := K)
  let μ := ⨆ k, (E.obj k).size
  have hμ : μ < B.cutoff := Cardinal.iSup_lt_of_lt_cof_ord hK hE
  have hμle : ∀ k, (E.obj k).size ≤ μ := fun k => le_ciSup Cardinal.bddAbove_of_small k
  have hOj : #(Over j) < B.cutoff :=
    (mk_over_lt B.aleph0_lt_cutoff_cof hK hKH j).trans_le (Ordinal.cof_ord_le _)
  have hb : max ℵ₀ (#(Over j) * μ) < B.cutoff :=
    max_lt B.aleph0_lt_cutoff (Cardinal.mul_lt_of_lt B.aleph0_lt_cutoff.le hOj hμ)
  have hπ : _root_.AlgebraicGeometry.IsAffineHom (c.π.app j) :=
    _root_.AlgebraicGeometry.isAffineHom_π_app E c hc j
  have : Nonempty (E.obj j).affineOpens := ⟨⟨⊥, isAffineOpen_bot _⟩⟩
  refine (Scheme.size_le_of_iSup_eq_top
    (fun U : (E.obj j).affineOpens => c.π.app j ⁻¹ᵁ U.1)
    ((c.π.app j).iSup_preimage_eq_top (iSup_affineOpens_eq_top _))).trans_lt ?_
  refine max_lt ((Scheme.mk_affineOpens_le_size _).trans_lt (hE j))
    ((ciSup_le' fun U => ?_).trans_lt hb)
  let O := AlgebraicGeometry.opensDiagram E j U.1
  let oC := AlgebraicGeometry.opensCone E c j U.1
  change oC.pt.size ≤ _
  exact Scheme.size_le_of_isLimit_of_isAffine O (fun k => U.2.preimage (E.map k.hom))
    (fun k => (Scheme.size_coe_opens_le _ _).trans (hμle k.left))
    (AlgebraicGeometry.isLimitOpensCone E c hc j U.1)

/-- **The limit of the stages over a fixed stage, read in schemes.** Let `D` be a cofiltered
inverse system of presheaves on the big fppf site of `S` with affine transition morphisms,
indexed by a category with fewer objects and morphisms than the cofinality of the site's size
cutoff, and let `W` lift the stages over a fixed stage `i₀` to objects of the site. Then the
underlying scheme functor preserves the limit of `W`.

The transition morphisms of `W` are affine morphisms of schemes, so the diagram of underlying
schemes has a limit (Stacks 01YX). It is covered by the inverse images of the affine opens of
one stage, each of which is the limit of the affine inverse images in the stages; their sizes
are bounded by one cardinal below the cutoff, so the limit lies in the site, which therefore
creates it. -/
theorem preservesLimit_toScheme_of_overLift {J : Type u} [Category.{u} J] [IsCofiltered J]
    (D : J ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hSize : #J < B.cutoff.ord.cof)
    (hHomSize : ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof)
    (hAffine : ∀ {i j : J} (f : i ⟶ j), IsAffineHom B S hS (D.map f)) (i₀ : J)
    (W : Over i₀ ⥤ BigFppfOver B S hS) (e : W ⋙ yoneda ≅ Over.forget i₀ ⋙ D) :
    PreservesLimit W (BigFppfOver.toScheme B S hS) := by
  have hW : ∀ {a b : Over i₀} (f : a ⟶ b), _root_.AlgebraicGeometry.IsAffineHom
      ((AlgebraicGeometry.underlyingDiagram W).map f) :=
    isAffineHom_underlyingDiagram_map_of_iso D hAffine i₀ W e
  have hJ : #(Over i₀) < B.cutoff.ord.cof :=
    mk_over_lt B.aleph0_lt_cutoff_cof hSize hHomSize i₀
  have hJH : ∀ a b : Over i₀, #(a ⟶ b) < B.cutoff.ord.cof := fun a b =>
    (Cardinal.mk_le_of_injective (f := fun φ : a ⟶ b => φ.left)
      fun _ _ h => Over.OverMorphism.ext h).trans_lt (hHomSize _ _)
  let E' := W ⋙ BigFppfOver.forget B S hS
  have : IsConnected (Over i₀) := IsCofiltered.isConnected _
  have : ∀ {a b : Over i₀} (f : a ⟶ b),
      _root_.AlgebraicGeometry.IsAffineHom ((E' ⋙ B.inclusion).map f) := hW
  have : HasLimit (E' ⋙ B.inclusion) := inferInstance
  let : CreatesLimit E' B.inclusion := createsLimitFullSubcategoryInclusion E'
    (size_lt_cutoff_of_isLimit_underlyingDiagram hJ hJH W hW (limit.cone _) (limit.isLimit _))
  have : HasLimit E' := hasLimit_of_created E' B.inclusion
  have : PreservesLimit E' B.inclusion := inferInstance
  apply comp_preservesLimit

/-- A preorder is indexed below the cofinality of the cutoff iff its opposite is. -/
private theorem card_op_lt_cutoff_cof_iff {I : Type u} [Preorder I] :
    #Iᵒᵖ < B.cutoff.ord.cof ↔ #I < B.cutoff.ord.cof := by
  rw [mk_congr (Opposite.equivToOpposite (α := I)).symm]

/-- The morphism sets of the opposite of a preorder are below the cofinality of the cutoff. -/
private theorem card_hom_op_lt_cutoff_cof {I : Type u} [Preorder I] (i j : Iᵒᵖ) :
    #(i ⟶ j) < B.cutoff.ord.cof :=
  have : Finite (i ⟶ j) := Finite.of_subsingleton
  (lt_aleph0_of_finite _).trans B.aleph0_lt_cutoff_cof

namespace DescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})}

/-- **Stacks 0D2X, part (2), in the situation of Stacks 084R.** Let `D` be a directed inverse
system of quasi-compact and quasi-separated algebraic spaces over `S` with affine transition
morphisms and a chosen limit `X`, indexed by a set smaller than the cofinality of the site's
size cutoff. Every invertible `𝒪_X`-module is the pullback of an invertible module on some
stage.

This is `AlgebraicGeometry.Space.exists_isInvertibleModule_stage_model`, transported from the
limit of the system to the chosen limit of the situation. -/
theorem exists_isInvertibleModule_stage_model {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation B S hS hZ I) (hI : #I < B.cutoff.ord.cof)
    (L : Modules.{u, u} B S hS D.limitCone.pt D.limitAlgebraicSpace)
    (hL : IsInvertibleModule ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ L) :
    ∃ (i : I) (Lᵢ : Modules.{u, u} B S hS (D.system.obj (op i)) (D.algebraicSpace i)),
      IsInvertibleModule ⟨D.system.obj (op i), D.algebraicSpace i⟩ Lᵢ ∧
        Nonempty (L ≅ (modulePullback B S hS (ObjectProperty.homMk (D.limitCone.π.app (op i)) :
          (⟨D.limitCone.pt, D.limitAlgebraicSpace⟩ : AlgebraicSpaces B S hS) ⟶
            ⟨D.system.obj (op i), D.algebraicSpace i⟩)).obj Lᵢ) := by
  have _ : Nonempty I := ⟨D.base⟩
  have hSize : #Iᵒᵖ < B.cutoff.ord.cof := card_op_lt_cutoff_cof_iff.2 hI
  have hHomSize : ∀ i j : Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof := card_hom_op_lt_cutoff_cof
  let hD : ∀ i : Iᵒᵖ, IsAlgebraicSpace B S hS (D.system.obj i) := fun i => D.algebraicSpace i.unop
  let XL := Space.limitAlgebraicSpace B S hS D.system hSize hHomSize hD D.transition_affine
  let XD : AlgebraicSpaces B S hS := ⟨D.limitCone.pt, D.limitAlgebraicSpace⟩
  let eA : XL ≅ XD := ObjectProperty.isoMk _
    ((limit.isLimit D.system).conePointUniqueUpToIso D.isLimit)
  let L' := (modulePullback B S hS eA.hom).obj L
  have hL' : IsInvertibleModule XL L' :=
    Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := smallEtaleRingedToposModulesHom B S hS eA.hom) (L := L) (hL := hL)
  obtain ⟨i, Lᵢ, hLᵢ, ⟨eL⟩⟩ := Space.exists_isInvertibleModule_stage_model B S hS D.system
    hSize hHomSize hD D.transition_affine hZ (fun i => D.quasiCompact i.unop)
    (fun i => D.quasiSeparated i.unop) L' hL'
  have hπ : eA.inv ≫ Space.limitProjection B S hS D.system hSize hHomSize hD D.transition_affine i =
      (ObjectProperty.homMk (D.limitCone.π.app i) : XD ⟶ ⟨D.system.obj i, hD i⟩) := by
    ext1
    exact IsLimit.conePointUniqueUpToIso_inv_comp (limit.isLimit D.system) D.isLimit i
  exact ⟨i.unop, Lᵢ, hLᵢ, ⟨((modulePullbackIdIso B S hS XD).app L).symm ≪≫
    eqToIso (congrArg (fun (m : XD ⟶ XD) => (modulePullback B S hS m).obj L)
      eA.inv_hom_id.symm) ≪≫
    ((modulePullbackCompIso B S hS eA.inv eA.hom).app L).symm ≪≫
    (modulePullback B S hS eA.inv).mapIso eL ≪≫
    (modulePullbackCompIso B S hS eA.inv _).app Lᵢ ≪≫
    eqToIso (congrArg (fun (m : XD ⟶ ⟨D.system.obj i, hD i⟩) => (modulePullback B S hS m).obj Lᵢ)
      hπ)⟩⟩

end DescentSituation

/-- **Stacks 0D3D, from a Noetherian approximation indexed below the cofinality of the
cutoff.** Let `S` be a scheme, `f : X ⟶ Y` a proper morphism of algebraic spaces over `S` and
`L` an invertible `𝒪_X`-module. There is an open subspace `V ⊆ Y` such that a morphism
`g : Y' ⟶ Y` of algebraic spaces factors through `V` if and only if the pullback of `L` to
`X' = Y' ×_Y X` is ample on `X'/Y'` (Stacks 0D31).

This is
`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation`
with the convention read as the bound the library puts on the index category of Stacks 07SQ and
07SR: fewer objects, and fewer morphisms between any two objects, than the cofinality of the
site's size cutoff. Stacks 07SQ, 07SR and 07SF, part (1), are then the library's theorems;
Stacks 0D2X, part (2), is
`AlgebraicGeometry.Space.DescentSituation.exists_isInvertibleModule_stage_model`; the bound
passes to the system of fibres, which has the same index category; and the scheme limit of the
stages over a representable stage is
`AlgebraicGeometry.Space.preservesLimit_toScheme_of_overLift`.

What remains are two inputs, stated over the integers: `h0A0X`, Stacks 0A0X for a proper
morphism to an affine scheme, with the approximating systems indexed by a set below the
cofinality of the cutoff; and `h0D3A`, Stacks 0D3A at a residue field over a Noetherian scheme of
the site. Such an approximation need not exist on every site (see the module documentation), so
this is not Stacks 0D3D in full and is not registered. -/
theorem exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_boundedApproximation
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0A0X : ∀ (U : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      IsAffine ((BigFppfOver.toScheme B _ hZ).obj U) →
      ∀ {X' : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (f' : X' ⟶ representedAlgebraicSpace B _ hZ U), IsProper B _ hZ f'.hom →
      ∃ (I : Type u) (_ : Preorder I) (_ : IsDirected I (· ≤ ·))
        (DX DY : DescentSituation B (⊤_ Scheme.{u}) hZ hZ I) (φ : DX.system ⟶ DY.system)
        (eX : DX.limitCone.pt ≅ X'.1) (eY : DY.limitCone.pt ≅ yoneda.obj U),
        (∀ i : I, DX.limitCone.π.app (op i) ≫ φ.app (op i) =
          eX.hom ≫ f'.hom ≫ eY.inv ≫ DY.limitCone.π.app (op i)) ∧
        (∀ i : I, IsProper B _ hZ (φ.app (op i)) ∧ IsFinitePresentation B _ hZ (φ.app (op i))) ∧
        (∀ i : I, IsFinitePresentation B _ hZ (terminal.from (DY.system.obj (op i)))) ∧
        #I < B.cutoff.ord.cof)
    (h0D3A : ∀ (T : BigFppfOver B (⊤_ Scheme.{u}) hZ),
      _root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B _ hZ).obj T) →
      ∀ {Xᵢ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ}
        (fᵢ : Xᵢ ⟶ representedAlgebraicSpace B _ hZ T), IsProper B _ hZ fᵢ.hom →
      ∀ (Lᵢ : Modules.{u, u} B _ hZ Xᵢ.1 Xᵢ.2),
        Stacks.SheafOfModules.IsInvertible (structurePresheaf B _ hZ Xᵢ.1)
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B _ hZ Xᵢ.1 Xᵢ.2).O)).property Lᵢ →
      ∀ y : (BigFppfOver.toScheme B _ hZ).obj T,
        (∀ ⦃X₀ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₀ : X₀ ⟶ Xᵢ)
          (f₀ : X₀ ⟶ representedAlgebraicSpace B _ hZ
            (residueFieldObject B _ hZ T y (B.residueField_spec_contains T.left.property y))),
          IsPullback p₀ f₀ fᵢ (ObjectProperty.homMk (yoneda.map
            (residueFieldMap B _ hZ T y (B.residueField_spec_contains T.left.property y)))) →
          IsRelativelyAmple B _ hZ f₀ ((modulePullback B _ hZ p₀).obj Lᵢ)) →
        ∃ V : ((BigFppfOver.toScheme B _ hZ).obj T).Opens, y ∈ V ∧
          ∀ ⦃X₁ : AlgebraicSpaces B (⊤_ Scheme.{u}) hZ⦄ (p₁ : X₁ ⟶ Xᵢ)
            (f₁ : X₁ ⟶ representedAlgebraicSpace B _ hZ (openSub T V)),
            IsPullback p₁ f₁ fᵢ (ObjectProperty.homMk (yoneda.map (openSubHom T V))) →
            IsRelativelyAmple B _ hZ f₁ ((modulePullback B _ hZ p₁).obj Lᵢ))
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (hf : IsProper B S hS f.hom)
    {L : Modules.{u, u} B S hS X.1 X.2}
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).property L) :
    ∃ V : Subfunctor Y.1, IsOpenSubspace B S hS V ∧
      ∀ ⦃X' Y' : AlgebraicSpaces B S hS⦄ (g : Y' ⟶ Y) (p : X' ⟶ X) (f' : X' ⟶ Y'),
        IsPullback p f' f g →
          ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
            IsRelativelyAmple B S hS f' ((modulePullback B S hS p).obj L)) := by
  have hlift : ∀ {I : Type u}, #I < B.cutoff.ord.cof →
      Cardinal.lift.{u} #I < Cardinal.lift.{u} B.cutoff.ord.cof := fun hI => by
    simpa only [Cardinal.lift_id] using hI
  refine exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_approximation hZ
    (fun {J} [Category.{u} J] _ => #J < B.cutoff.ord.cof ∧ ∀ i j : J, #(i ⟶ j) < B.cutoff.ord.cof)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ h0D3A hf hL
  · intro U hU X' f' hf'
    obtain ⟨I, _, _, DX, DY, φ, eX, eY, h₁, h₂, h₃, hI⟩ := h0A0X U hU f' hf'
    have h : #Iᵒᵖ < B.cutoff.ord.cof ∧ ∀ i j : Iᵒᵖ, #(i ⟶ j) < B.cutoff.ord.cof :=
      ⟨card_op_lt_cutoff_cof_iff.2 hI, card_hom_op_lt_cutoff_cof⟩
    exact ⟨I, _, _, DX, DY, φ, eX, eY, h₁, h₂, h₃, h, h⟩
  · intro I _ _ D hc hX
    exact D.exists_isAffineSpace_system_obj (hlift (card_op_lt_cutoff_cof_iff.1 hc.1)) hX
  · intro I _ _ D hc hX
    exact D.exists_isRepresentable_system_obj (hlift (card_op_lt_cutoff_cof_iff.1 hc.1)) hX
  · intro J _ _ D hc hA i
    exact isAffineHom_limitπ B _ hZ D hc.1 hc.2 hA i
  · intro I _ _ D hc L hL
    exact D.exists_isInvertibleModule_stage_model (card_op_lt_cutoff_cof_iff.1 hc.1) L hL
  · intro I _ _ _ DX DY φ V hV k hX hY
    exact hX
  · intro I _ _ D hc i₀ _ W ⟨e⟩
    have _ : Nonempty I := ⟨D.base⟩
    exact preservesLimit_toScheme_of_overLift D.system hc.1 hc.2 D.transition_affine (op i₀) W e

end AlgebraicGeometry.Space

end
