module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeBeckChevalley
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImageSiteRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleRestrictionQuasicoherentRing
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePushforwardFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentRestrictScalars

/-!
# Stacks 08AI: direct image along an affine morphism is an equivalence on quasi-coherent modules

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and `𝒜 = f_*𝒪_Y`.  This file proves the first assertion of Stacks 08AI: the
functor `ℱ ↦ f_*ℱ` from quasi-coherent `𝒪_Y`-modules to quasi-coherent `𝒜`-modules is an
equivalence of categories.  The second assertion of the tag — an `𝒜`-module is quasi-coherent
over `𝒪_X` iff it is quasi-coherent over `𝒜` — is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff`.

## The proof

The functor has the left adjoint `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` of Stacks 03D4
(`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction`), which preserves
quasi-coherence; so it suffices that unit and counit are invertible at quasi-coherent modules.
That is local: on `X` along the affine étale charts `V`, and on `Y` along their base changes
`V ×_X Y`.  For an affine chart `V` the base change `f' : V ×_X Y ⟶ V` has an affine
representable target, where the invertibility is
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation`
and its counit companion.  What carries the statement from `f'` to `f` is the compatibility of
the adjunction with restriction to the chart.

That compatibility is proved on the level of sites.  For a representable morphism the direct
image of Stacks 03D1 is restriction along base change of charts
(`AlgebraicGeometry.Space.moduleDirectImageIsoSiteDirectImage`), so the adjunction may be
transported to one whose right adjoint is a restriction functor
(`CategoryTheory.Adjunction.transportRight`).  The square of sites formed by base change and
étale postcomposition satisfies Beck–Chevalley
(`AlgebraicGeometry.Space.isIso_chartSquareMate`), so by
`StacksFrontier/CategoryTheory/Sites/Modules/PushforwardBaseChangeSquare.lean` restriction to the
chart commutes with direct image and the restricted unit and counit are those of `f'` up to
isomorphisms (`CategoryTheory.Adjunction.unit_comp_map_conjugate`,
`CategoryTheory.Adjunction.map_squareBaseChange_comp_counit`).

## Main results

* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom`,
  `...counit_app_of_isAffineHom`: unit and counit are invertible at quasi-coherent modules.
* `AlgebraicGeometry.Space.isEquivalence_affineQuasicoherentDirectImage`: **Stacks 08AI**, the
  functor `ℱ ↦ f_*ℱ` on quasi-coherent modules is an equivalence.
* `AlgebraicGeometry.Space.affineQuasicoherentDirectImageEquivalence`: the equivalence itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback

universe u

/-! ### Transporting an adjunction along an equivalence on the source of the right adjoint -/

namespace CategoryTheory.Adjunction

variable {C : Type*} {C' : Type*} {D : Type*} [Category C] [Category C'] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (E : C' ≌ C) {R' : D ⥤ C'} (e : R ≅ R' ⋙ E.functor)

/-- An adjunction `L ⊣ R` with `R ≅ R' ⋙ E.functor` for an equivalence `E` gives
`E.functor ⋙ L ⊣ R'`. -/
def transportRight : E.functor ⋙ L ⊣ R' :=
  (E.toAdjunction.comp adj).ofNatIsoRight
    (Functor.isoWhiskerRight e E.inverse ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft R' E.unitIso.symm ≪≫ Functor.rightUnitor R')

/-- The unit of the transported adjunction at `G` is invertible exactly when the unit of the
original one is, at `E.functor G`. -/
theorem isIso_transportRight_unit_app_iff (G : C') :
    IsIso ((adj.transportRight E e).unit.app G) ↔ IsIso (adj.unit.app (E.functor.obj G)) := by
  simp only [Functor.id_obj, Functor.comp_obj, transportRight, ofNatIsoRight_unit, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.whiskerLeft_comp,
    Functor.whiskerLeft_twice, Category.assoc, NatTrans.comp_app, comp_unit_app,
    Equivalence.toAdjunction_unit, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_hom_app,
    Category.comp_id, Category.id_comp, isIso_comp_left_iff, isIso_comp_right_iff]
  exact isIso_iff_of_reflects_iso _ E.inverse

/-- The counit of the transported adjunction is invertible exactly where the original one is. -/
theorem isIso_transportRight_counit_app_iff (M : D) :
    IsIso ((adj.transportRight E e).counit.app M) ↔ IsIso (adj.counit.app M) := by
  dsimp only [transportRight]
  simp only [ofNatIsoRight_counit, comp_counit, NatTrans.comp_app]
  have : IsIso E.toAdjunction.counit := inferInstanceAs (IsIso E.counitIso.hom)
  simp only [isIso_comp_left_iff]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Invertibility is local on the étale charts -/

/-- A morphism of sheaves of modules which is invertible on sections, as a morphism of abelian
groups, over every postcomposed chart of a family of charts covering the final object, is an
isomorphism. -/
theorem isIso_of_isIso_toPresheaf_app_postcomp {Z : AlgebraicSpaces B S hS}
    (R : Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u}) {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) {ι : Type*} (U : ι → SmallEtale B S hS Z.1)
    (hU : (SmallEtale.topology B S hS Z.1).CoversTop U)
    (h : ∀ j (W : SmallEtale B S hS (chartSpace B S hS Z (U j)).1),
      IsIso (((PresheafOfModules.toPresheaf R.obj).map φ.val).app
        (op ((smallEtalePostcomp B S hS (chartToSpace B S hS Z (U j))
          (isEtale_chartToSpace B S hS Z (U j))).obj W)))) :
    IsIso φ := by
  refine Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map hU φ fun j => ?_
  have : IsIso ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
      ((SheafOfModules.overFunctor R (U j)).map φ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    let E := SmallEtale.chartLocalizationEquivalence B S hS Z.1 (U j)
    let e : (smallEtalePostcomp B S hS (chartToSpace B S hS Z (U j))
        (isEtale_chartToSpace B S hS Z (U j))).obj (E.inverse.obj T.unop) ≅ T.unop.left :=
      (Over.forget (U j)).mapIso (E.counitIso.app T.unop)
    show IsIso (((PresheafOfModules.toPresheaf R.obj).map φ.val).app (op T.unop.left))
    rw [NatTrans.isIso_app_iff_of_iso _ e.op]
    exact h j _
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _)

/-- An isomorphism after restriction along a functor of sites is an isomorphism on the sections
over the objects in its image. -/
theorem isIso_toPresheaf_app_of_isIso_pushforward_map {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} (G : C ⥤ D) [G.IsContinuous J K]
    {T : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (ψ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (hφ : IsIso ((SheafOfModules.pushforward.{u} ψ).map φ))
    (W : C) : IsIso (((PresheafOfModules.toPresheaf R.obj).map φ.val).app (op (G.obj W))) := by
  have h := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map_isIso
    ((SheafOfModules.pushforward.{u} ψ).map φ)
  rw [NatTrans.isIso_iff_isIso_app] at h
  exact h (op W)

/-- **Invertibility is local on the étale charts**: a morphism of sheaves of modules whose
restriction along postcomposition with every member of a family of charts covering the final
object is invertible, through any ring maps, is invertible. -/
theorem isIso_of_isIso_pushforward_postcomp {Z : AlgebraicSpaces B S hS}
    (R : Sheaf (SmallEtale.topology B S hS Z.1) RingCat.{u}) {M N : SheafOfModules.{u} R}
    (φ : M ⟶ N) {ι : Type*} (U : ι → SmallEtale B S hS Z.1)
    (hU : (SmallEtale.topology B S hS Z.1).CoversTop U)
    {T : ∀ j, Sheaf (SmallEtale.topology B S hS (chartSpace B S hS Z (U j)).1) RingCat.{u}}
    (ψ : ∀ j, T j ⟶ ((smallEtalePostcomp B S hS (chartToSpace B S hS Z (U j))
      (isEtale_chartToSpace B S hS Z (U j))).sheafPushforwardContinuous RingCat.{u}
        (SmallEtale.topology B S hS (chartSpace B S hS Z (U j)).1)
        (SmallEtale.topology B S hS Z.1)).obj R)
    (h : ∀ j, IsIso ((SheafOfModules.pushforward.{u} (ψ j)).map φ)) : IsIso φ :=
  isIso_of_isIso_toPresheaf_app_postcomp B S hS R φ U hU fun j W =>
    isIso_toPresheaf_app_of_isIso_pushforward_map _ (ψ j) φ (h j) W

/-! ### The chart square -/

section Chart

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)
  (V : SmallEtale B S hS X.1)

attribute [local instance] isContinuous_smallBaseChange

/-- The comparison `p ⋙ u ≅ uV ⋙ pY` of the chart square: the inverse of its Beck–Chevalley
mate. -/
abbrev chartSquareIso :
    smallEtalePostcomp B S hS (chartToSpace B S hS X V) (isEtale_chartToSpace B S hS X V) ⋙
        smallBaseChange B S hS f hf ≅
      smallBaseChange B S hS (chartSquareMap B S hS f hf V)
          (relativelyRepresentable_chartSquareMap B S hS f hf V) ⋙
        smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
          (isEtale_chartToSpace B S hS Y _) :=
  (asIso (chartSquareMate B S hS f hf V)).symm

/-- The base change transformation of the chart square, for the comparison `chartSquareIso`, is
an isomorphism. -/
instance isIso_chartSquare_baseChangeTransformation :
    IsIso (ChangeOfSitesSquare.baseChangeTransformation (chartSquareAdjX B S hS V)
      (chartSquareAdjY B S hS f hf V) (chartSquareIso B S hS f hf V)) := by
  change IsIso ((mateEquiv (chartSquareAdjX B S hS V) (chartSquareAdjY B S hS f hf V)
    (TwoSquare.mk _ _ _ _ (chartSquareMate B S hS f hf V))).natTrans)
  rw [mateEquiv_chartSquareMate]
  infer_instance

/-- Restriction of `u_*𝒪_Y`-modules to the chart `V`. -/
abbrev chartSquareRestriction :=
  ChangeOfSitesSquare.restrictionX (SmallEtale.topology B S hS X.1)
    (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
    (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1)
    (chartSquareIso B S hS f hf V) (structureRingSheaf B S hS Y)

/-- Restriction to the chart `V` and base-changed chart carries invertibility of the unit and
counit of an adjunction for `f` over from the ones for the base change `f'`. -/
private theorem isIso_chartSquare_map_unit_and_counit {L : _ ⥤ _}
    (adj : L ⊣ siteDirectImage B S hS f hf) {LV : _ ⥤ _}
    (adjV : LV ⊣ siteDirectImage B S hS (chartSquareMap B S hS f hf V)
      (relativelyRepresentable_chartSquareMap B S hS f hf V)) :
    (∀ G : SheafOfModules.{u} (siteDirectImageRing B S hS f hf),
      IsIso (adjV.unit.app ((chartSquareRestriction B S hS f hf V).obj G)) →
      IsIso ((SheafOfModules.pushforward.{u} (ChangeOfSitesSquare.ringMapV
        (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
        (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
        (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1)
        (chartSquareIso B S hS f hf V) (structureRingSheaf B S hS Y))).map (adj.unit.app G))) ∧
    (∀ M : SheafOfModules.{u} (structureRingSheaf B S hS Y),
      IsIso (adjV.counit.app ((etaleModulePullback B S hS
        (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
        (isEtale_chartToSpace B S hS Y _)).obj M)) →
      IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
        (isEtale_chartToSpace B S hS Y _)).map (adj.counit.app M))) := by
  let T := SmallEtale.topology B S hS
  let aC := ChangeOfSitesSquare.adjunctionX (T X.1) (T Y.1) (T (chartSpace B S hS X V).1)
    (T (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1) (chartSquareAdjX B S hS V)
    (chartSquareIso B S hS f hf V) (structureRingSheaf B S hS Y)
  let aD := ChangeOfSitesSquare.adjunctionY (T Y.1)
    (T (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1)
    (chartSquareAdjY B S hS f hf V) (structureRingSheaf B S hS Y)
  have hδ := ChangeOfSitesSquare.isIso_baseChangeMap (T X.1) (T Y.1) (T (chartSpace B S hS X V).1)
    (T (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1) (chartSquareAdjX B S hS V)
    (chartSquareAdjY B S hS f hf V) (chartSquareIso B S hS f hf V) (structureRingSheaf B S hS Y)
  exact ⟨fun G => Adjunction.isIso_map_unit_of_isIso adj adjV aC aD _ (Iso.isIso_hom _) hδ G,
    fun M => Adjunction.isIso_map_counit_of_isIso adj adjV aC aD _ (Iso.isIso_hom _) hδ M⟩

/-- **The restriction to a chart of the unit of an adjunction for the site direct image is
invertible** as soon as the unit of an adjunction for the base change to the chart is. -/
theorem isIso_chartSquareRestriction_map_unit {L : _ ⥤ _} (adj : L ⊣ siteDirectImage B S hS f hf)
    {LV : _ ⥤ _} (adjV : LV ⊣ siteDirectImage B S hS (chartSquareMap B S hS f hf V)
      (relativelyRepresentable_chartSquareMap B S hS f hf V))
    (G : SheafOfModules.{u} (siteDirectImageRing B S hS f hf))
    (hG : IsIso (adjV.unit.app ((chartSquareRestriction B S hS f hf V).obj G))) :
    IsIso ((SheafOfModules.pushforward.{u} (ChangeOfSitesSquare.ringMapV
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hf V)).1)
      (chartSquareIso B S hS f hf V) (structureRingSheaf B S hS Y))).map (adj.unit.app G)) :=
  (isIso_chartSquare_map_unit_and_counit B S hS f hf V adj adjV).1 G hG

/-- **The restriction to the base-changed chart of the counit of an adjunction for the site
direct image is invertible** as soon as the counit of an adjunction for the base change is. -/
theorem isIso_etaleModulePullback_map_counit {L : _ ⥤ _}
    (adj : L ⊣ siteDirectImage B S hS f hf)
    {LV : _ ⥤ _} (adjV : LV ⊣ siteDirectImage B S hS (chartSquareMap B S hS f hf V)
      (relativelyRepresentable_chartSquareMap B S hS f hf V))
    (M : SheafOfModules.{u} (structureRingSheaf B S hS Y))
    (hM : IsIso (adjV.counit.app ((etaleModulePullback B S hS
      (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
      (isEtale_chartToSpace B S hS Y _)).obj M))) :
    IsIso ((etaleModulePullback B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hf V))
      (isEtale_chartToSpace B S hS Y _)).map (adj.counit.app M)) :=
  (isIso_chartSquare_map_unit_and_counit B S hS f hf V adj adjV).2 M hM

end Chart

/-! ### The affine-target case at an étale chart -/

section ChartTarget

variable {X Y' : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1)
  (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
  (f' : Y' ⟶ chartSpace B S hS X V) (hf' : IsAffineHom B S hS f'.hom)

include hV hf' in
/-- The unit of Stacks 03D4 is invertible at a quasi-coherent module, for an affine morphism to
an affine étale chart. -/
theorem isIso_directImageAlgebraPullbackAdjunction_unit_app_chart
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f'))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f').unit.app G) := by
  obtain ⟨P⟩ := nonempty_presentation_directImageAlgebra_of_isAffine B S hS
    ((SmallEtale.toOver B S hS X.1).obj V) hV f' hf' G hG
  have e : directImageAlgebraPullbackAdjunction B S hS f' =
      directImageAlgebraPullbackAdjunction B S hS (Y := Y')
        (X := schemeSpace ((SmallEtale.toOver B S hS X.1).obj V)) f' := rfl
  rw [e]
  exact isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation B S hS
    ((SmallEtale.toOver B S hS X.1).obj V) f' hf' G P

include hV hf' in
/-- The counit of Stacks 03D4 is invertible at a quasi-coherent module, for an affine morphism
to an affine étale chart. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_chart
    (M : Modules.{u, u} B S hS Y'.1 Y'.2) (hM : M.IsQuasicoherentOnSite) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f').counit.app M) := by
  obtain ⟨P⟩ := nonempty_presentation_of_isAffineHom_of_isAffine B S hS
    ((SmallEtale.toOver B S hS X.1).obj V) hV f' hf' M hM
  exact isIso_directImageAlgebraPullbackAdjunction_counit_app_of_presentation B S hS
    ((SmallEtale.toOver B S hS X.1).obj V) f' hf' M P

end ChartTarget

/-! ### The equivalence -/

section Main

variable {X Y : AlgebraicSpaces B S hS}

attribute [local instance] isContinuous_smallBaseChange

/-- The adjunction of Stacks 03D4 for a representable morphism, transported so that its right
adjoint is restriction along base change of charts. -/
def siteAdjunction (f : Y ⟶ X) (hrep : yoneda.relativelyRepresentable f.hom) :
    (directImageRingEquivalence B S hS f hrep).functor ⋙ directImageAlgebraPullback B S hS f ⊣
      siteDirectImage B S hS f hrep :=
  (directImageAlgebraPullbackAdjunction B S hS f).transportRight
    (directImageRingEquivalence B S hS f hrep) (moduleDirectImageIsoSiteDirectImage B S hS f hrep)

/-- Restriction of scalars along an isomorphism of sheaves of rings preserves quasi-coherence, in
the form of the functor of `Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso`. -/
theorem isQuasicoherentOnSite_restrictScalarsEquivalenceOfIso_functor {C : Type (u + 1)}
    [Category.{u} C] {J : GrothendieckTopology C} {R R' : Sheaf J RingCat.{u}} (e : R ≅ R')
    (M : SheafOfModules.{u} R) (hM : M.IsQuasicoherentOnSite) :
    ((Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso e).functor.obj
      M).IsQuasicoherentOnSite := by
  show ((SheafOfModules.restrictScalars e.inv).obj M).IsQuasicoherentOnSite
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso e.inv M hM

/-- Restriction along a functor of sites through an isomorphism of sheaves of rings preserves
quasi-coherence as soon as restriction through the identity does. -/
theorem isQuasicoherentOnSite_pushforward_of_isIso {C D : Type (u + 1)} [Category.{u} C]
    [Category.{u} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} (G : C ⥤ D)
    [G.IsContinuous J K] {T : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    (φ : T ⟶ (G.sheafPushforwardContinuous RingCat.{u} J K).obj R) [IsIso φ]
    (M : SheafOfModules.{u} R)
    (h : ((SheafOfModules.pushforward.{u} (𝟙 ((G.sheafPushforwardContinuous RingCat.{u} J K).obj
      R))).obj M).IsQuasicoherentOnSite) :
    ((SheafOfModules.pushforward.{u} φ).obj M).IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso φ _ h

/-- The functor of `directImageRingEquivalence` preserves quasi-coherence. -/
theorem isQuasicoherentOnSite_directImageRingEquivalence_functor (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (G : SheafOfModules.{u} (siteDirectImageRing B S hS f hrep)) (hG : G.IsQuasicoherentOnSite) :
    ((directImageRingEquivalence B S hS f hrep).functor.obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_restrictScalarsEquivalenceOfIso_functor
    (asIso (directImageRingMap B S hS f hrep)).symm _
    (isQuasicoherentOnSite_restrictScalarsEquivalenceOfIso_functor
      (restrictionRingIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
        (smallBaseChange B S hS f hrep) (structureRingSheaf B S hS Y)).symm G hG)

/-- The inverse of `directImageRingEquivalence` preserves quasi-coherence. -/
theorem isQuasicoherentOnSite_directImageRingEquivalence_inverse (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) :
    ((directImageRingEquivalence B S hS f hrep).inverse.obj G).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_restrictScalarsEquivalenceOfIso_functor
    (restrictionRingIso (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
        (smallBaseChange B S hS f hrep) (structureRingSheaf B S hS Y)).symm.symm _
    (isQuasicoherentOnSite_restrictScalarsEquivalenceOfIso_functor
      (asIso (directImageRingMap B S hS f hrep)).symm.symm G hG)

variable (f : Y ⟶ X)

/-- The base change of an affine morphism to an étale chart is affine. -/
theorem isAffineHom_chartSquareMap (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (V : SmallEtale B S hS X.1) : IsAffineHom B S hS (chartSquareMap B S hS f hrep V).hom :=
  IsAffineHom.of_isPullback (isPullback_chartSquare B S hS f hrep V) hf

/-- The unit of the site adjunction of the base change to an affine chart is invertible at a
quasi-coherent module. -/
theorem isIso_siteAdjunction_unit_app_chart (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
    (G : SheafOfModules.{u} (siteDirectImageRing B S hS (chartSquareMap B S hS f hrep V)
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((siteAdjunction B S hS (chartSquareMap B S hS f hrep V)
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)).unit.app G) := by
  refine (Adjunction.isIso_transportRight_unit_app_iff
    (directImageAlgebraPullbackAdjunction B S hS (chartSquareMap B S hS f hrep V))
    (directImageRingEquivalence B S hS _ (relativelyRepresentable_chartSquareMap B S hS f hrep V))
    (moduleDirectImageIsoSiteDirectImage B S hS _
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)) _).mpr ?_
  have hqc := isQuasicoherentOnSite_directImageRingEquivalence_functor B S hS _
    (relativelyRepresentable_chartSquareMap B S hS f hrep V) _ hG
  have h := isIso_directImageAlgebraPullbackAdjunction_unit_app_chart B S hS V hV _
    (isAffineHom_chartSquareMap B S hS f hf hrep V) _ hqc
  exact h

/-- The restriction to an affine chart of the unit of the site adjunction is invertible at a
quasi-coherent module. -/
theorem isIso_chartSquareRestriction_map_siteAdjunction_unit (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (G : SheafOfModules.{u} (siteDirectImageRing B S hS f hrep)) (hG : G.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    IsIso ((SheafOfModules.pushforward.{u} (ChangeOfSitesSquare.ringMapV
      (SmallEtale.topology B S hS X.1) (SmallEtale.topology B S hS Y.1)
      (SmallEtale.topology B S hS (chartSpace B S hS X V).1)
      (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hrep V)).1)
      (chartSquareIso B S hS f hrep V) (structureRingSheaf B S hS Y))).map
        ((siteAdjunction B S hS f hrep).unit.app G)) := by
  have hGr : ((chartSquareRestriction B S hS f hrep V).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_pushforward_of_isIso _ _ _
      (isQuasicoherentOnSite_postcompRestriction B S hS _ _ _ _ hG)
  exact isIso_chartSquareRestriction_map_unit B S hS f hrep V (siteAdjunction B S hS f hrep)
    (siteAdjunction B S hS (chartSquareMap B S hS f hrep V)
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)) G
    (isIso_siteAdjunction_unit_app_chart B S hS f hf hrep V hV
      ((chartSquareRestriction B S hS f hrep V).obj G) hGr)

/-- The unit of the site adjunction is invertible at a quasi-coherent module, for an affine
morphism. -/
theorem isIso_siteAdjunction_unit_app (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (G : SheafOfModules.{u} (siteDirectImageRing B S hS f hrep)) (hG : G.IsQuasicoherentOnSite) :
    IsIso ((siteAdjunction B S hS f hrep).unit.app G) :=
  isIso_of_isIso_pushforward_postcomp B S hS _ _
    (fun V : {U : SmallEtale B S hS X.1 // IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj U))} => V.1)
    (SmallEtale.coversTop_affineCharts B S hS X.1)
    (fun V => ChangeOfSitesSquare.ringMapV (SmallEtale.topology B S hS X.1)
      (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS (chartSpace B S hS X V.1).1)
      (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hrep V.1)).1)
      (chartSquareIso B S hS f hrep V.1) (structureRingSheaf B S hS Y))
    (fun V => isIso_chartSquareRestriction_map_siteAdjunction_unit B S hS f hf hrep G hG V.1 V.2)

/-- **The unit of Stacks 03D4 is invertible at a quasi-coherent module**, for an affine
morphism. -/
theorem isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G) := by
  obtain hrep := relativelyRepresentable_hom_of_isAffineHom B S hS f hf
  have key := (Adjunction.isIso_transportRight_unit_app_iff
    (directImageAlgebraPullbackAdjunction B S hS f) (directImageRingEquivalence B S hS f hrep)
    (moduleDirectImageIsoSiteDirectImage B S hS f hrep) _).mp
    (isIso_siteAdjunction_unit_app B S hS f hf hrep _
      (isQuasicoherentOnSite_directImageRingEquivalence_inverse B S hS f hrep G hG))
  exact (NatTrans.isIso_app_iff_of_iso _
    ((directImageRingEquivalence B S hS f hrep).counitIso.app G)).1 key

/-- The counit of the site adjunction of the base change to an affine chart is invertible at a
quasi-coherent module. -/
theorem isIso_siteAdjunction_counit_app_chart (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom) (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V)))
    (M : SheafOfModules.{u} (structureRingSheaf B S hS
      (chartSpace B S hS Y (chartSquareTop B S hS f hrep V))))
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((siteAdjunction B S hS (chartSquareMap B S hS f hrep V)
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)).counit.app M) := by
  refine (Adjunction.isIso_transportRight_counit_app_iff
    (directImageAlgebraPullbackAdjunction B S hS (chartSquareMap B S hS f hrep V))
    (directImageRingEquivalence B S hS _ (relativelyRepresentable_chartSquareMap B S hS f hrep V))
    (moduleDirectImageIsoSiteDirectImage B S hS _
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)) _).mpr ?_
  have h := isIso_directImageAlgebraPullbackAdjunction_counit_app_chart B S hS V hV _
    (isAffineHom_chartSquareMap B S hS f hf hrep V) M hM
  exact h

/-- The restriction to the base change of an affine chart of the counit of the site adjunction is
invertible at a quasi-coherent module. -/
theorem isIso_restriction_map_siteAdjunction_counit (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS Y)) (hM : M.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj V))) :
    IsIso ((SheafOfModules.pushforward.{u}
      (F := smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hrep V))
        (isEtale_chartToSpace B S hS Y _))
      (𝟙 (((smallEtalePostcomp B S hS (chartToSpace B S hS Y (chartSquareTop B S hS f hrep V))
        (isEtale_chartToSpace B S hS Y _)).sheafPushforwardContinuous RingCat.{u}
          (SmallEtale.topology B S hS (chartSpace B S hS Y (chartSquareTop B S hS f hrep V)).1)
          (SmallEtale.topology B S hS Y.1)).obj (structureRingSheaf B S hS Y)))).map
        ((siteAdjunction B S hS f hrep).counit.app M)) := by
  have hMr := isQuasicoherentOnSite_etaleModulePullback B S hS _
    (isEtale_chartToSpace B S hS Y (chartSquareTop B S hS f hrep V)) M hM
  exact isIso_etaleModulePullback_map_counit B S hS f hrep V (siteAdjunction B S hS f hrep)
    (siteAdjunction B S hS (chartSquareMap B S hS f hrep V)
      (relativelyRepresentable_chartSquareMap B S hS f hrep V)) M
    (isIso_siteAdjunction_counit_app_chart B S hS f hf hrep V hV _ hMr)

/-- The counit of the site adjunction is invertible at a quasi-coherent module, for an affine
morphism. -/
theorem isIso_siteAdjunction_counit_app (hf : IsAffineHom B S hS f.hom)
    (hrep : yoneda.relativelyRepresentable f.hom)
    (M : SheafOfModules.{u} (structureRingSheaf B S hS Y)) (hM : M.IsQuasicoherentOnSite) :
    IsIso ((siteAdjunction B S hS f hrep).counit.app M) :=
  isIso_of_isIso_pushforward_postcomp B S hS _ _
    (fun V : {V : SmallEtale B S hS X.1 // IsAffine (chartScheme V)} =>
      (smallBaseChange B S hS f hrep).obj V.1)
    (coversTop_smallBaseChange_affineCharts B S hS f hrep) (fun _ => 𝟙 _)
    (fun V => isIso_restriction_map_siteAdjunction_counit B S hS f hf hrep M hM V.1 V.2)

/-- **The counit of Stacks 03D4 is invertible at a quasi-coherent module**, for an affine
morphism. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom
    (hf : IsAffineHom B S hS f.hom) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (hM : M.IsQuasicoherentOnSite) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M) := by
  obtain hrep := relativelyRepresentable_hom_of_isAffineHom B S hS f hf
  exact (Adjunction.isIso_transportRight_counit_app_iff _
    (directImageRingEquivalence B S hS f hrep)
    (moduleDirectImageIsoSiteDirectImage B S hS f hrep) M).mp
    (isIso_siteAdjunction_counit_app B S hS f hf hrep M hM)

/-- **Stacks 08AI, first assertion.**  Let `f : Y ⟶ X` be an affine morphism of algebraic spaces
over `S` and `𝒜 = f_*𝒪_Y`.  The functor `ℱ ↦ f_*ℱ` from quasi-coherent `𝒪_Y`-modules to
quasi-coherent `𝒜`-modules is an equivalence of categories.

The functor is `AlgebraicGeometry.Space.affineQuasicoherentDirectImage`, which is the direct image
of Stacks 03D1 on the nose (`AlgebraicGeometry.Space.affineQuasicoherentDirectImage_comp_ι`); its
quasi-inverse is `𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢`.  The second assertion of the tag is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff`. -/
@[stacks 08AI "the functor F ↦ f_*F from quasi-coherent 𝒪_Y-modules to quasi-coherent \
f_*𝒪_Y-modules is an equivalence of categories, for an affine morphism"]
theorem isEquivalence_affineQuasicoherentDirectImage (hf : IsAffineHom B S hS f.hom) :
    (affineQuasicoherentDirectImage B S hS f hf).IsEquivalence :=
  isEquivalence_quasicoherentDirectImage B S hS f
    (fun G hG => isQuasicoherentOnSite_directImageAlgebraPullback B S hS f hf G hG)
    (directImagePreservesQuasicoherence B S hS f hf)
    (fun G hG =>
      isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom B S hS f hf G hG)
    (fun M hM => isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom B S hS f hf M
      hM)

/-- The equivalence of Stacks 08AI, `QCoh(𝒪_Y) ≌ QCoh(f_*𝒪_Y)`, whose functor is `ℱ ↦ f_*ℱ`. -/
def affineQuasicoherentDirectImageEquivalence (hf : IsAffineHom B S hS f.hom) :
    QuasicoherentSheaves.{u, u} B S hS Y.1 Y.2 ≌
      (SheafOfModules.isQuasicoherentOnSite
        (affineDirectImageAlgebra B S hS f)).FullSubcategory :=
  haveI := isEquivalence_affineQuasicoherentDirectImage B S hS f hf
  (affineQuasicoherentDirectImage B S hS f hf).asEquivalence

/-- The statement `AlgebraicGeometry.Space.AffineDirectImageEquivalence` holds for every affine
morphism. -/
theorem affineDirectImageEquivalence_of_isAffineHom (hf : IsAffineHom B S hS f.hom) :
    AffineDirectImageEquivalence B S hS f :=
  ⟨directImagePreservesQuasicoherence B S hS f hf,
    isEquivalence_affineQuasicoherentDirectImage B S hS f hf⟩

end Main

/-- The statement `AlgebraicGeometry.Space.AffinePushforwardEquivalence` holds. -/
theorem affinePushforwardEquivalence : AffinePushforwardEquivalence B S hS :=
  fun f hf => affineDirectImageEquivalence_of_isAffineHom B S hS f hf


end AlgebraicGeometry.Space
