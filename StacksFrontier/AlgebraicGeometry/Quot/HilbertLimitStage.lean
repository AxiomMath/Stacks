module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Limits.ClosedSubobjectDescent
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitDescentHom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.BaseChangeChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceChartProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.AffineDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# Closed subspaces of the base changes of an algebraic space over a limit of affine schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
separated and of finite presentation, and let `T = lim T_j` be a cofiltered limit of affine
schemes over `Y`, all in the site. Write `X_T`, `X_{T_j}` for the base changes. This file proves
the two finite-stage statements behind the local finite presentation of the Hilbert functor
(Stacks 0D01, 0DM7):

* a closed subspace of `X_T` which is of finite presentation and flat over `T` is the inverse
  image of a closed subspace of some `X_{T_j}` of finite presentation and flat over `T_j`;
* two closed subspaces of some `X_{T_i}` of finite presentation over `T_i` with the same inverse
  image in `X_T` already have the same inverse image in some `X_{T_j}`.

Nothing is assumed of the size of the index category. The limit is never formed among algebraic
spaces: an affine étale chart `U` of `X_{T_{i₀}}` is base changed to the stages and to `T`, the
charts `T_j ×_{T_{i₀}} U` form the base changed system of `AlgebraicGeometry.pullbackDiagram`
whose limit is `T ×_{T_{i₀}} U`, and closed subspaces correspond to closed subschemes of the
charts invariant under their relations (Stacks 07TW). The descent then happens among closed
subschemes of affine schemes, by Stacks 01ZM and 01ZP, flatness by Stacks 04AI, and invariance
by descending an equality of closed subschemes of the relations.

## Main results

* `AlgebraicGeometry.Space.exists_affine_fibreProductChart`: the affine étale chart of a base
  change to an affine scheme, with an affine presentation of its relation.
* `AlgebraicGeometry.Space.exists_closedSubspace_stage_of_hilbertFamily`: the existence
  statement.
* `AlgebraicGeometry.Space.exists_preimage_eq_of_preimage_eq_limit`: the uniqueness statement.

## References

* [Stacks Project, Tag 0D01](https://stacks.math.columbia.edu/tag/0D01)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 01ZP](https://stacks.math.columbia.edu/tag/01ZP)
* [Stacks Project, Tag 04AI](https://stacks.math.columbia.edu/tag/04AI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks in presheaf categories on the big fppf site (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_HilbertLimitStage
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks in presheaf categories on the big fppf site. -/
local instance hasPullbacks_presheaf_HilbertLimitStage
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- A property of morphisms of algebraic spaces stable under base change passes from `f` to the
projection of the base change of `X` to a scheme over `Y`. -/
theorem prop_pullback_snd_schemeBaseChange
    (P : ∀ ⦃F G : AlgebraicSpaces B S hS⦄, (F ⟶ G) → Prop)
    [MorphismProperty.IsStableUnderBaseChange P]
    (hf : P f) (T : SchemesOverPresheaf B S hS Y) :
    P (ObjectProperty.homMk (pullback.snd f.hom T.hom) :
      schemeBaseChangeSpace f T ⟶ schemeOverSpace T) := by
  have hpb : IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom T.hom) : schemeBaseChangeSpace f T ⟶ X)
      (ObjectProperty.homMk (pullback.snd f.hom T.hom) :
        schemeBaseChangeSpace f T ⟶ schemeOverSpace T) f
      (ObjectProperty.homMk T.hom : schemeOverSpace T ⟶ Y) :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (IsPullback.of_hasPullback f.hom T.hom)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hf

/-- The projection of a base change of a morphism of finite presentation is of finite
presentation. -/
theorem isFinitePresentation_pullback_snd_schemeBaseChange
    (hfp : IsFinitePresentation B S hS f.hom) (T : SchemesOverPresheaf B S hS Y) :
    IsFinitePresentation B S hS (pullback.snd f.hom T.hom) :=
  prop_pullback_snd_schemeBaseChange f
    (fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsFinitePresentation B S hS k.hom) hfp T

/-- The projection of a base change of a separated morphism is separated. -/
theorem isSeparated_pullback_snd_schemeBaseChange
    (hsep : IsSeparated B S hS f.hom) (T : SchemesOverPresheaf B S hS Y) :
    IsSeparated B S hS (pullback.snd f.hom T.hom) := by
  have : (closedImmersionPresheafProperty B S hS).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _
  exact (MorphismProperty.IsStableUnderBaseChange.diagonal
    (P := closedImmersionPresheafProperty B S hS)).of_isPullback
      (IsPullback.of_hasPullback f.hom T.hom) hsep

/-- **An affine étale chart of a base change to an affine scheme.** For `f` separated and of
finite presentation and `T₀` an affine scheme over `Y`, the base change `X_{T₀}` has a surjective
étale chart `φ : U ⟶ X_{T₀}` by an affine scheme `U`, whose structure morphism `u : U ⟶ T₀` is of
finite presentation, and whose relation `U ×_{X_{T₀}} U` is presented by an affine scheme. -/
theorem exists_affine_fibreProductChart (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (T₀ : SchemesOverPresheaf B S hS Y)
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀.left)) :
    ∃ (U : BigFppfOver B S hS) (φ : yoneda.obj U ⟶ schemeBaseChange f T₀) (u : U ⟶ T₀.left)
      (_ : yoneda.map u = φ ≫ pullback.snd f.hom T₀.hom) (R : BigFppfOver B S hS)
      (rt rs : R ⟶ U),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ ∧
      IsPullback (yoneda.map rt) (yoneda.map rs) φ φ ∧
      FinitePresentation ((BigFppfOver.toScheme B S hS).map u) := by
  have hsfp := isFinitePresentation_pullback_snd_schemeBaseChange f hfp T₀
  have hP := isAlgebraicSpace_schemeBaseChange f T₀
  have hqc : IsQuasiCompactSpace B S hS (schemeBaseChange f T₀) :=
    isQuasiCompactSpace_of_isFinitePresentation B S hS _ (isAlgebraicSpace_yoneda B S hS _)
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS T₀.left hT₀) hsfp
  obtain ⟨U, φ, hU, hs, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hP).mp hqc
  have he := presheaf_etale_of_isEtale B S hS het
  let u : U ⟶ T₀.left := Yoneda.fullyFaithful.preimage (φ ≫ pullback.snd f.hom T₀.hom)
  have hu : yoneda.map u = φ ≫ pullback.snd f.hom T₀.hom := Yoneda.fullyFaithful.map_preimage _
  have := hU
  have := hT₀
  have huaff : IsAffineHom B S hS (yoneda.map u) :=
    isAffineHom_of_presheaf
      ((presheaf_yoneda_map_iff B S hS
          (P := @_root_.AlgebraicGeometry.IsAffineHom.{u}) inferInstance u).mpr
        (_root_.AlgebraicGeometry.isAffineHom_of_isAffine _))
  have hφaff : IsAffineHom B S hS φ :=
    isAffineHom_of_isAffineHom_comp_of_isSeparated B S hS φ _ (by rw [← hu]; exact huaff)
      (isSeparated_pullback_snd_schemeBaseChange f hsep T₀)
  obtain ⟨W, p, q, hpq⟩ := hφaff ⟨U, hU⟩ φ
  have hp : yoneda.map (Yoneda.fullyFaithful.preimage p) = p :=
    Yoneda.fullyFaithful.map_preimage _
  refine ⟨U, φ, u, hu, (BigAffineFppf.inclusion B S hS).obj W, Yoneda.fullyFaithful.preimage p,
    q, hU, W.property, hs, he, by rw [hp]; exact hpq, ?_⟩
  have := isMultiplicative_presheaf_etale B S hS
  have hlfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map u) :=
    hsfp.1 U T₀.left φ (𝟙 _) u he (MorphismProperty.id_mem _ _) (by rw [Category.comp_id, hu])
  exact ⟨hlfp, inferInstance, inferInstance⟩

section Limit

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
    (Dy : J ⥤ SchemesOverPresheaf B S hS Y) (cy : Cone Dy)
    (hc : IsLimit ((CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS).mapCone cy))
    (hD : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (Dy.obj j).left))

/-- Transport of a property of the second projection of a cartesian square to the second
projection of the chosen fibre product. -/
private theorem prop_pullback_snd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {W A C D : Scheme.{u}} {a : W ⟶ A} {b : W ⟶ C} {f₀ : A ⟶ D} {g : C ⟶ D}
    (h : IsPullback a b f₀ g) (hb : P b) : P (pullback.snd f₀ g) := by
  have e := h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f₀ g)
  rw [← e] at hb
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).1 hb

/-- Transport of a property of the second projection of the chosen fibre product to the second
projection of a cartesian square. -/
private theorem prop_snd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {W A C D : Scheme.{u}} {a : W ⟶ A} {b : W ⟶ C} {f₀ : A ⟶ D} {g : C ⟶ D}
    (h : IsPullback a b f₀ g) (hb : P (pullback.snd f₀ g)) : P b := by
  have e := h.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f₀ g)
  rw [← e]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).2 hb

include hc hD in
/-- **Closed subspaces of the base change to the limit descend.** For `f` separated and of
finite presentation and `T = lim T_j` a cofiltered limit of affine schemes over `Y`, the closed
subspace of `X_T` of a family of the Hilbert functor over `T` is the inverse image of a closed
subspace of `X_{T_j}`, of finite presentation and flat over `T_j`, for some stage `j`. -/
theorem exists_closedSubspace_stage_of_hilbertFamily (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (z : HilbertFamily f cy.pt) :
    ∃ (j : J) (W : Subfunctor (schemeBaseChange f (Dy.obj j))), IsClosedSubspace B S hS W ∧
      IsFinitePresentation B S hS (W.ι ≫ pullback.snd f.hom (Dy.obj j).hom) ∧
      IsFlat B S hS (W.ι ≫ pullback.snd f.hom (Dy.obj j).hom) ∧
      W.preimage (schemeBaseChangeMap f (cy.π.app j)) = z.Z := by
  classical
  let G := CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS
  let E := Dy ⋙ G
  let cS := G.mapCone cy
  let F := BigFppfOver.toScheme B S hS
  have hLFPri : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hFlatri : MorphismProperty.RespectsIso (@Flat.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨U, φ, u, hu, R, rt, rs, hU, hR, hs, he, hRφ, hufp⟩ :=
    exists_affine_fibreProductChart f hfp hsep (Dy.obj i₀) (hD i₀)
  have hEaff : ∀ j, IsAffine (E.obj j) := hD
  have := hU
  have := hR
  have := hufp.1
  have := hufp.2.1
  have := hufp.2.2
  let gT := cy.π.app i₀
  let φT := fibreProductChart B S hS f φ u hu gT
  have hsT := fibreProductChart_surjective B S hS f u hu gT hs
  have heT := fibreProductChart_etale B S hS f u hu gT he
  obtain ⟨CT, hCTci, hCTinv, hzCT⟩ := exists_preimage_eq_subschemePoints B S hS hsT z.closed
  have := hCTci
  have hψT : yoneda.map (stageFst B S hS gT.left u) = φT ≫ pullback.snd f.hom cy.pt.hom :=
    (fibreProductChart_snd B S hS f φ u hu gT).symm
  have hCTlfp : LocallyOfFinitePresentation
      (CT.arrow ≫ pullback.fst (F.map gT.left) (F.map u)) :=
    prop_arrow_comp_of_holdsOnEveryEtaleChart B S hS _ _ hψT inferInstance hzCT
      (@LocallyOfFinitePresentation) heT z.finitePresentation.1
  have hCTflat : Flat (CT.arrow ≫ pullback.fst (F.map gT.left) (F.map u)) :=
    prop_arrow_comp_of_holdsOnEveryEtaleChart B S hS _ _ hψT inferInstance hzCT
      (@Flat) heT z.flat
  have : LocallyOfFiniteType (F.map u) := inferInstance
  have hfst : ∀ {Z : Scheme.{u}} (t : Z ⟶ F.obj (Dy.obj i₀).left),
      FinitePresentation (pullback.fst t (F.map u)) := fun t =>
    have h := (IsPullback.of_hasPullback t (F.map u)).flip
    ⟨MorphismProperty.of_isPullback h hufp.1, MorphismProperty.of_isPullback h hufp.2.1,
      MorphismProperty.of_isPullback h hufp.2.2⟩
  have hfstLFT : ∀ {Z : Scheme.{u}} (t : Z ⟶ F.obj (Dy.obj i₀).left),
      LocallyOfFiniteType (pullback.fst t (F.map u)) := fun t =>
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback t (F.map u)).flip
      (inferInstance : LocallyOfFiniteType (F.map u))
  have hCTfp : FinitePresentation CT.arrow :=
    ⟨@locallyOfFinitePresentation_of_comp _ _ _ CT.arrow
      (pullback.fst (F.map gT.left) (F.map u)) hCTlfp (hfstLFT _), inferInstance, inferInstance⟩
  let N := pullbackDiagram E i₀ (F.map u)
  let cN := pullbackCone E cS i₀ (F.map u)
  have hN : IsLimit cN := isLimitPullbackCone E cS hc i₀ (F.map u)
  have hNaff : ∀ j : Over i₀, IsAffine (N.obj j) := fun j => by
    show IsAffine (pullback (E.map j.hom) (F.map u)); infer_instance
  let CT' : Subobject cN.pt := CT
  have : _root_.AlgebraicGeometry.IsClosedImmersion CT'.arrow := hCTci
  obtain ⟨k, Ck, hCkci, hCkfp, hCk⟩ := exists_pullback_subobject_eq_of_isLimit N cN hN CT' hCTfp
  have := hCkci
  have hfstfp : ∀ j : Over i₀, FinitePresentation (pullback.fst (E.map j.hom) (F.map u)) :=
    fun j => hfst (E.map j.hom)
  let X₀ : Over (E.obj k.left) := Over.mk (Ck.arrow ≫ pullback.fst (E.map k.hom) (F.map u))
  have hX₀fp : FinitePresentation X₀.hom := FinitePresentation.comp hCkfp (hfstfp k)
  have sq₀ := (Subobject.isPullback (cN.π.app k) Ck).paste_vert
    (isPullback_pullbackCone_π_app E cS i₀ (F.map u) k)
  have hflat₀ : Flat (((Subobject.pullback (cN.π.app k)).obj Ck).arrow ≫
      pullback.fst (cS.π.app i₀) (F.map u)) := by
    rw [hCk]; exact hCTflat
  have hflatsnd : Flat (pullback.snd X₀.hom (cS.π.app k.left)) :=
    prop_pullback_snd_of_isPullback (@Flat) sq₀ hflat₀
  have : IsAffine (Ck : Scheme.{u}) := isAffine_of_isAffineHom Ck.arrow
  have : CompactSpace (Over.mk (𝟙 (E.obj k.left))).left :=
    inferInstanceAs (CompactSpace (E.obj k.left))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (E.obj k.left))).left :=
    inferInstanceAs (QuasiSeparatedSpace (E.obj k.left))
  have : CompactSpace X₀.left := inferInstanceAs (CompactSpace (Ck : Scheme.{u}))
  have : QuasiSeparatedSpace X₀.left := inferInstanceAs (QuasiSeparatedSpace (Ck : Scheme.{u}))
  let t₀ : X₀ ⟶ Over.mk (𝟙 (E.obj k.left)) := Over.homMk X₀.hom (Category.comp_id _)
  have : LocallyOfFinitePresentation t₀.left := hX₀fp.1
  have : Flat ((Over.pullback (cS.π.app k.left)).map t₀).left :=
    (flat_overPullback_terminal_iff _ X₀).2 hflatsnd
  obtain ⟨m, g, hm⟩ := exists_flat_baseChange_of_limitBaseChange E cS k.left X₀
    (Over.mk (𝟙 (E.obj k.left))) t₀ hc
  have hflatg : Flat (pullback.snd X₀.hom (E.map g)) :=
    (flat_overPullback_terminal_iff (E.map g) X₀).1 hm
  let k' : Over i₀ := Over.mk (g ≫ k.hom)
  let a : k' ⟶ k := Over.homMk g rfl
  let Ck' := (Subobject.pullback (N.map a)).obj Ck
  have sqa := (Subobject.isPullback (N.map a) Ck).paste_vert
    (isPullback_pullbackDiagram_map E i₀ (F.map u) a)
  have hCk'flat : Flat (Ck'.arrow ≫ pullback.fst (E.map k'.hom) (F.map u)) :=
    prop_snd_of_isPullback (@Flat) sqa hflatg
  have hpba := Subobject.isPullback (N.map a) Ck
  have hCk'ci : _root_.AlgebraicGeometry.IsClosedImmersion Ck'.arrow :=
    MorphismProperty.of_isPullback hpba hCkci
  have hCk'fp : FinitePresentation Ck'.arrow :=
    ⟨MorphismProperty.of_isPullback hpba hCkfp.1, MorphismProperty.of_isPullback hpba hCkfp.2.1,
      MorphismProperty.of_isPullback hpba hCkfp.2.2⟩
  have hCk'T : (Subobject.pullback (cN.π.app k')).obj Ck' = CT := by
    rw [← Subobject.pullback_comp, cN.w a, hCk]
  have hrt : rt ≫ u = rs ≫ u := relation_comp_eq B S hS f φ u hu rt rs hRφ
  let M := pullbackDiagram E i₀ (F.map (rs ≫ u))
  let cM := pullbackCone E cS i₀ (F.map (rs ≫ u))
  have hM : IsLimit cM := isLimitPullbackCone E cS hc i₀ (F.map (rs ≫ u))
  have hMaff : ∀ j : Over i₀, IsAffine (M.obj j) := fun j => by
    show IsAffine (pullback (E.map j.hom) (F.map (rs ≫ u))); infer_instance
  let τ : ∀ {T' : SchemesOverPresheaf B S hS Y} (g' : T' ⟶ Dy.obj i₀),
      stageObj B S hS g'.left (rs ≫ u) ⟶ stageObj B S hS g'.left u :=
    fun g' => stageMapRight B S hS g'.left u rt hrt
  let σ : ∀ {T' : SchemesOverPresheaf B S hS Y} (g' : T' ⟶ Dy.obj i₀),
      stageObj B S hS g'.left (rs ≫ u) ⟶ stageObj B S hS g'.left u :=
    fun g' => stageMapRight B S hS g'.left u rs rfl
  have hτ : ∀ {T' T'' : SchemesOverPresheaf B S hS Y} (g' : T' ⟶ Dy.obj i₀)
      (g'' : T'' ⟶ Dy.obj i₀) (h : T'' ⟶ T') (hh : h.left ≫ g'.left = g''.left),
      F.map (stageMap B S hS g'.left (rs ≫ u) h.left hh) ≫ F.map (τ g') =
        F.map (τ g'') ≫ F.map (stageMap B S hS g'.left u h.left hh) := by
    intro T' T'' g' g'' h hh
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (stageMap_comp_stageMapRight B S hS h.left hh rt hrt)
  have hσ : ∀ {T' T'' : SchemesOverPresheaf B S hS Y} (g' : T' ⟶ Dy.obj i₀)
      (g'' : T'' ⟶ Dy.obj i₀) (h : T'' ⟶ T') (hh : h.left ≫ g'.left = g''.left),
      F.map (stageMap B S hS g'.left (rs ≫ u) h.left hh) ≫ F.map (σ g') =
        F.map (σ g'') ≫ F.map (stageMap B S hS g'.left u h.left hh) := by
    intro T' T'' g' g'' h hh
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map (stageMap_comp_stageMapRight B S hS h.left hh rs rfl)
  have hleft : ∀ j : J, (cy.π.app j).left ≫ (Dy.map (𝟙 _)).left = (cy.π.app j).left := by
    intro j; rw [Dy.map_id]; rfl
  have hconek : ∀ j : Over i₀, (cy.π.app j.left).left ≫ (Dy.map j.hom).left = gT.left :=
    fun j => congrArg CommaMorphism.left (cy.w j.hom)
  have htrans : ∀ {j j' : Over i₀} (b : j' ⟶ j),
      (Dy.map b.left).left ≫ (Dy.map j.hom).left = (Dy.map j'.hom).left := by
    intro j j' b
    rw [← CostructuredArrow.comp_left, ← Dy.map_comp, Over.w b]
  let A₁ := (Subobject.pullback (F.map (τ (Dy.map k'.hom)))).obj Ck'
  let A₂ := (Subobject.pullback (F.map (σ (Dy.map k'.hom)))).obj Ck'
  have hA : ∀ (t : stageObj B S hS (Dy.map k'.hom).left (rs ≫ u) ⟶
      stageObj B S hS (Dy.map k'.hom).left u),
      FinitePresentation ((Subobject.pullback (F.map t)).obj Ck').arrow := fun t =>
    have h := Subobject.isPullback (F.map t) Ck'
    ⟨MorphismProperty.of_isPullback h hCk'fp.1, MorphismProperty.of_isPullback h hCk'fp.2.1,
      MorphismProperty.of_isPullback h hCk'fp.2.2⟩
  have hA₁ : (Subobject.pullback (cM.π.app k')).obj A₁ =
      (Subobject.pullback (F.map (τ gT))).obj CT :=
    ((Subobject.pullback_comp (cM.π.app k') (F.map (τ (Dy.map k'.hom))) Ck').symm.trans
      (congrArg (fun t => (Subobject.pullback t).obj Ck')
        (hτ (Dy.map k'.hom) gT (cy.π.app k'.left) (hconek k')))).trans
      ((Subobject.pullback_comp (F.map (τ gT)) (cN.π.app k') Ck').trans
        (congrArg (fun x => (Subobject.pullback (F.map (τ gT))).obj x) hCk'T))
  have hA₂ : (Subobject.pullback (cM.π.app k')).obj A₂ =
      (Subobject.pullback (F.map (σ gT))).obj CT :=
    ((Subobject.pullback_comp (cM.π.app k') (F.map (σ (Dy.map k'.hom))) Ck').symm.trans
      (congrArg (fun t => (Subobject.pullback t).obj Ck')
        (hσ (Dy.map k'.hom) gT (cy.π.app k'.left) (hconek k')))).trans
      ((Subobject.pullback_comp (F.map (σ gT)) (cN.π.app k') Ck').trans
        (congrArg (fun x => (Subobject.pullback (F.map (σ gT))).obj x) hCk'T))
  have hinvT := (isInvariantSubscheme_iff_of_isPullback B S hS hsT (τ gT) (σ gT)
    (isPullback_stageRelation B S hS f φ u hu gT rt rs hRφ) CT).1 hCTinv
  obtain ⟨l, b, hb⟩ := exists_pullback_subobject_eq_of_isLimit_of_eq M cM hM k' A₁ A₂
    (hA _) (hA _) (by rw [hA₁, hA₂, hinvT])
  let Cl := (Subobject.pullback (N.map b)).obj Ck'
  let gl := Dy.map l.hom
  let φl := fibreProductChart B S hS f φ u hu gl
  have hsl := fibreProductChart_surjective B S hS f u hu gl hs
  have hel := fibreProductChart_etale B S hS f u hu gl he
  have hClinv : IsInvariantSubscheme B S hS hsl Cl := by
    refine (isInvariantSubscheme_iff_of_isPullback B S hS hsl (τ gl) (σ gl)
      (isPullback_stageRelation B S hS f φ u hu gl rt rs hRφ) Cl).2 ?_
    refine ((Subobject.pullback_comp (F.map (τ gl)) (N.map b) Ck').symm.trans ?_).trans
      (Subobject.pullback_comp (F.map (σ gl)) (N.map b) Ck')
    refine (congrArg (fun t => (Subobject.pullback t).obj Ck')
      (hτ (Dy.map k'.hom) gl (Dy.map b.left) (htrans b)).symm).trans ?_
    refine ((Subobject.pullback_comp (M.map b) (F.map (τ (Dy.map k'.hom))) Ck').trans hb).trans ?_
    refine (Subobject.pullback_comp (M.map b) (F.map (σ (Dy.map k'.hom))) Ck').symm.trans ?_
    exact congrArg (fun t => (Subobject.pullback t).obj Ck')
      (hσ (Dy.map k'.hom) gl (Dy.map b.left) (htrans b))
  have hpbb := Subobject.isPullback (N.map b) Ck'
  have hClci : _root_.AlgebraicGeometry.IsClosedImmersion Cl.arrow :=
    MorphismProperty.of_isPullback hpbb hCk'ci
  have hClfp : FinitePresentation Cl.arrow :=
    ⟨MorphismProperty.of_isPullback hpbb hCk'fp.1, MorphismProperty.of_isPullback hpbb hCk'fp.2.1,
      MorphismProperty.of_isPullback hpbb hCk'fp.2.2⟩
  have hClfp' : FinitePresentation (Cl.arrow ≫ pullback.fst (E.map l.hom) (F.map u)) :=
    FinitePresentation.comp hClfp (hfstfp l)
  have hClflat : Flat (Cl.arrow ≫ pullback.fst (E.map l.hom) (F.map u)) :=
    MorphismProperty.of_isPullback (hpbb.paste_vert
      (isPullback_pullbackDiagram_map E i₀ (F.map u) b)) hCk'flat
  have hP := isAlgebraicSpace_schemeBaseChange f (Dy.obj l.left)
  have hWl := isClosedSubspace_invariantSubspace B S hS hsl hel hP Cl hClci hClinv
  have hWlC := preimage_invariantSubspace B S hS hsl Cl hClinv
  have hψl : yoneda.map (stageFst B S hS gl.left u) =
      φl ≫ pullback.snd f.hom (Dy.obj l.left).hom := (fibreProductChart_snd B S hS f φ u hu gl).symm
  have hsnd := isFinitePresentation_pullback_snd_schemeBaseChange f hfp (Dy.obj l.left)
  have hYl := isAlgebraicSpace_yoneda B S hS (Dy.obj l.left).left
  let Cl' : Subobject (F.obj (stageObj B S hS gl.left u)) := Cl
  have hClim : _root_.AlgebraicGeometry.IsImmersion Cl'.arrow := by
    have : _root_.AlgebraicGeometry.IsClosedImmersion Cl'.arrow := hClci
    infer_instance
  refine ⟨l.left, invariantSubspace B S hS φl Cl, hWl, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact holdsOnEveryEtaleChart_of_prop_arrow_comp B S hS _ _ hψl hClim hWlC
      (@LocallyOfFinitePresentation) LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget
      hWl.1 hsl hel hClfp'.1
  · exact isQuasiCompact_comp B S hS hP hYl _ _ (isQuasiCompact_of_isClosedImmersion' B S hS hWl.2)
      hsnd.2.1
  · exact isQuasiSeparated_comp B S hS hWl.1 hP _ _
      (isQuasiSeparated_of_isClosedImmersion B S hS hWl.2) hsnd.2.2
  · exact holdsOnEveryEtaleChart_of_prop_arrow_comp B S hS _ _ hψl hClim hWlC
      (@Flat) Flat.isEtaleLocalOnSourceAndTarget hWl.1 hsl hel hClflat
  · have hm := stageMap_fibreProductChart B S hS f φ u hu gl (cy.π.app l.left) (cy.w l.hom)
    have h₁ := preimage_preimage_eq_subschemePoints_pullback B S hS
      (schemeBaseChangeMap f (cy.π.app l.left)) _ hm hWlC
    have h₂ : (Subobject.pullback (cN.π.app l)).obj Cl = CT' :=
      ((Subobject.pullback_comp (cN.π.app l) (N.map b) Ck').symm.trans
        (congrArg (fun t => (Subobject.pullback t).obj Ck') (cN.w b))).trans hCk'T
    refine eq_of_preimage_eq_of_isClosedSubspace B S hS hsT heT
      (isAlgebraicSpace_schemeBaseChange f cy.pt)
      (isClosedSubspace_preimage B S hS _ _ hP (isAlgebraicSpace_schemeBaseChange f cy.pt) hWl)
      z.closed ?_
    exact h₁.trans ((congrArg (subschemePoints B S hS) h₂).trans hzCT.symm)

include hc hD in
/-- **Closed subspaces with the same base change to the limit agree at a finite stage.** For `f`
separated and of finite presentation and `T = lim T_j` a cofiltered limit of affine schemes over
`Y`, two closed subspaces of `X_{T_i}` locally of finite presentation over `T_i` whose inverse
images in `X_T` agree already have the same inverse image in `X_{T_j}` for some `j ⟶ i`. -/
theorem exists_preimage_eq_of_preimage_eq_limit (hfp : IsFinitePresentation B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (i : J) {W W' : Subfunctor (schemeBaseChange f (Dy.obj i))}
    (hW : IsClosedSubspace B S hS W) (hW' : IsClosedSubspace B S hS W')
    (hWfp : IsLocallyOfFinitePresentation B S hS (W.ι ≫ pullback.snd f.hom (Dy.obj i).hom))
    (hW'fp : IsLocallyOfFinitePresentation B S hS (W'.ι ≫ pullback.snd f.hom (Dy.obj i).hom))
    (h : W.preimage (schemeBaseChangeMap f (cy.π.app i)) =
      W'.preimage (schemeBaseChangeMap f (cy.π.app i))) :
    ∃ (j : J) (e : j ⟶ i), W.preimage (schemeBaseChangeMap f (Dy.map e)) =
      W'.preimage (schemeBaseChangeMap f (Dy.map e)) := by
  classical
  let G := CostructuredArrow.proj yoneda Y.obj ⋙ BigFppfOver.toScheme B S hS
  let E := Dy ⋙ G
  let cS := G.mapCone cy
  let F := BigFppfOver.toScheme B S hS
  have hLFPri : MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  obtain ⟨U, φ, u, hu, R, rt, rs, hU, hR, hs, he, hRφ, hufp⟩ :=
    exists_affine_fibreProductChart f hfp hsep (Dy.obj i) (hD i)
  have hEaff : ∀ j, IsAffine (E.obj j) := hD
  have := hU
  have := hufp.1
  have := hufp.2.1
  have := hufp.2.2
  have : LocallyOfFiniteType (F.map u) := inferInstance
  have hfpC : ∀ {V : Subfunctor (schemeBaseChange f (Dy.obj i))}, IsClosedSubspace B S hS V →
      IsLocallyOfFinitePresentation B S hS (V.ι ≫ pullback.snd f.hom (Dy.obj i).hom) →
      ∃ C : Subobject (F.obj U), _root_.AlgebraicGeometry.IsClosedImmersion C.arrow ∧
        FinitePresentation C.arrow ∧ V.preimage φ = subschemePoints B S hS C := by
    intro V hV hVfp
    obtain ⟨C, hCci, -, hVC⟩ := exists_preimage_eq_subschemePoints B S hS hs hV
    have := hCci
    have hlfp : LocallyOfFinitePresentation (C.arrow ≫ F.map u) :=
      prop_arrow_comp_of_holdsOnEveryEtaleChart B S hS _ _ hu inferInstance hVC
        (@LocallyOfFinitePresentation) he hVfp
    exact ⟨C, hCci, ⟨locallyOfFinitePresentation_of_comp C.arrow (F.map u), inferInstance,
      inferInstance⟩, hVC⟩
  obtain ⟨C, hCci, hCfp, hWC⟩ := hfpC hW hWfp
  obtain ⟨C', hC'ci, hC'fp, hW'C⟩ := hfpC hW' hW'fp
  have hbc : ∀ {T' : SchemesOverPresheaf B S hS Y} (g' : T' ⟶ Dy.obj i)
      {V : Subfunctor (schemeBaseChange f (Dy.obj i))} {D : Subobject (F.obj U)},
      V.preimage φ = subschemePoints B S hS D →
      (V.preimage (schemeBaseChangeMap f g')).preimage (fibreProductChart B S hS f φ u hu g') =
        subschemePoints B S hS
          ((Subobject.pullback (F.map (stageSnd B S hS g'.left u))).obj D) :=
    fun g' _ _ hVD => preimage_preimage_eq_subschemePoints_pullback B S hS _ _
      (fibreProductChart_comp_schemeBaseChangeMap B S hS f φ u hu g').symm hVD
  have himm : ∀ {Z : Scheme.{u}} (t : Z ⟶ F.obj U) {D : Subobject (F.obj U)},
      _root_.AlgebraicGeometry.IsClosedImmersion D.arrow →
      _root_.AlgebraicGeometry.IsClosedImmersion ((Subobject.pullback t).obj D).arrow :=
    fun t D hD => MorphismProperty.of_isPullback (Subobject.isPullback t D) hD
  have hfpb : ∀ {Z : Scheme.{u}} (t : Z ⟶ F.obj U) {D : Subobject (F.obj U)},
      FinitePresentation D.arrow → FinitePresentation ((Subobject.pullback t).obj D).arrow :=
    fun t D hD =>
      have hp := Subobject.isPullback t D
      ⟨MorphismProperty.of_isPullback hp hD.1, MorphismProperty.of_isPullback hp hD.2.1,
        MorphismProperty.of_isPullback hp hD.2.2⟩
  let gT := cy.π.app i
  have hCT : (Subobject.pullback (F.map (stageSnd B S hS gT.left u))).obj C =
      (Subobject.pullback (F.map (stageSnd B S hS gT.left u))).obj C' := by
    have h₁ := hbc gT hWC
    have h₂ := hbc gT hW'C
    rw [h] at h₁
    have : _root_.AlgebraicGeometry.IsClosedImmersion C.arrow := hCci
    have : _root_.AlgebraicGeometry.IsClosedImmersion C'.arrow := hC'ci
    have := himm (F.map (stageSnd B S hS gT.left u)) hCci
    have := himm (F.map (stageSnd B S hS gT.left u)) hC'ci
    exact subschemePoints_injective B S hS inferInstance inferInstance (h₁.symm.trans h₂)
  let N := pullbackDiagram E i (F.map u)
  let cN := pullbackCone E cS i (F.map u)
  have hN : IsLimit cN := isLimitPullbackCone E cS hc i (F.map u)
  have hNaff : ∀ j : Over i, IsAffine (N.obj j) := fun j => by
    show IsAffine (pullback (E.map j.hom) (F.map u)); infer_instance
  let j₀ : Over i := Over.mk (𝟙 i)
  let Cj₀ : Subobject (N.obj j₀) :=
    (Subobject.pullback (F.map (stageSnd B S hS (Dy.map j₀.hom).left u))).obj C
  let C'j₀ : Subobject (N.obj j₀) :=
    (Subobject.pullback (F.map (stageSnd B S hS (Dy.map j₀.hom).left u))).obj C'
  have hconek : ∀ j : Over i, (cy.π.app j.left).left ≫ (Dy.map j.hom).left = gT.left :=
    fun j => congrArg CommaMorphism.left (cy.w j.hom)
  have htrans : ∀ {j j' : Over i} (b : j' ⟶ j),
      (Dy.map b.left).left ≫ (Dy.map j.hom).left = (Dy.map j'.hom).left := by
    intro j j' b
    rw [← CostructuredArrow.comp_left, ← Dy.map_comp, Over.w b]
  have hlim : ∀ D : Subobject (F.obj U),
      (Subobject.pullback (cN.π.app j₀)).obj
        ((Subobject.pullback (F.map (stageSnd B S hS (Dy.map j₀.hom).left u))).obj D) =
      (Subobject.pullback (F.map (stageSnd B S hS gT.left u))).obj D := fun D =>
    (Subobject.pullback_comp (cN.π.app j₀) _ D).symm.trans
      (congrArg (fun t => (Subobject.pullback t).obj D)
        ((F.map_comp _ _).symm.trans (congrArg F.map
          (stageMap_snd B S hS (Dy.map j₀.hom).left u (cy.π.app j₀.left).left (hconek j₀)))))
  obtain ⟨l, b, hb⟩ := exists_pullback_subobject_eq_of_isLimit_of_eq N cN hN j₀ Cj₀ C'j₀
    (hfpb _ hCfp) (hfpb _ hC'fp) ((hlim C).trans (hCT.trans (hlim C').symm))
  have hstage : ∀ D : Subobject (F.obj U),
      (Subobject.pullback (N.map b)).obj
        ((Subobject.pullback (F.map (stageSnd B S hS (Dy.map j₀.hom).left u))).obj D) =
      (Subobject.pullback (F.map (stageSnd B S hS (Dy.map l.hom).left u))).obj D := fun D =>
    (Subobject.pullback_comp (N.map b) _ D).symm.trans
      (congrArg (fun t => (Subobject.pullback t).obj D)
        ((F.map_comp _ _).symm.trans (congrArg F.map
          (stageMap_snd B S hS (Dy.map j₀.hom).left u (Dy.map b.left).left (htrans b)))))
  refine ⟨l.left, l.hom, ?_⟩
  let gl := Dy.map l.hom
  have hP := isAlgebraicSpace_schemeBaseChange f (Dy.obj i)
  have hPl := isAlgebraicSpace_schemeBaseChange f (Dy.obj l.left)
  refine eq_of_preimage_eq_of_isClosedSubspace B S hS
    (fibreProductChart_surjective B S hS f u hu gl hs)
    (fibreProductChart_etale B S hS f u hu gl he) hPl
    (isClosedSubspace_preimage B S hS _ _ hP hPl hW)
    (isClosedSubspace_preimage B S hS _ _ hP hPl hW') ?_
  rw [hbc gl hWC, hbc gl hW'C, ← hstage C, ← hstage C']
  exact congrArg (subschemePoints B S hS) hb

end Limit

end AlgebraicGeometry.Space

end
