module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleToposSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RingedToposThickeningAdditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurjThickeningAdditions
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientSections
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoiRingEquivalence

/-!
# The structure sheaf of the thickened quotient on the dense charts

Let `E` be a square-zero extension of the small étale structure sheaf of an algebraic space `X`
(the data of Stacks 05ZT), `X = U/R` an étale presentation whose chart thickenings lie in the
site, `i : X ⟶ X' = U'/R'` the thickened quotient and `G : W ↦ W'` the functor from the charts
of `X` over `U` to the small étale site of `X'`. On these charts the structure sheaf of `X'` and
the direct image `i_*𝒜` agree: `𝒪_{X'}(W') = Γ(W', ⊤) = 𝒜(W) = (i_*𝒜)(W')`, naturally in `W`.

The charts `W'` are cover-dense in the small étale site of `X'` and `W ↦ W'` is fully faithful
(base change of étale charts along the thickening `X ⟶ X'` is full, Stacks 05ZH, and `W` is
`X ×_{X'} W'`), so the isomorphism extends to `𝒪_{X'} ≅ i_*𝒜`; its adjoint is the isomorphism
`i⁻¹𝒪_{X'} ≅ 𝒜` of Stacks 05ZT, compatible with the maps to `𝒪_X`.

## Main definitions

* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartStructureIso`:
  `G^op ⋙ 𝒪_{X'} ≅ G^op ⋙ i_*𝒜`.
* `AlgebraicGeometry.Space.SquareZeroExtension.structureIsoPushforward`: `𝒪_{X'} ≅ i_*𝒜`.
* `AlgebraicGeometry.Space.SquareZeroExtension.quotientSheafIso`: `i⁻¹𝒪_{X'} ≅ 𝒜`.

## Main results

* `AlgebraicGeometry.Space.SquareZeroExtension.chartRealizedSchemeΓIso_naturality`
* `AlgebraicGeometry.Space.SquareZeroExtension.thickenedChartRingEquiv_naturality`
* `AlgebraicGeometry.Space.SquareZeroExtension.isCoverDense_thickenedChartFunctor`
* `AlgebraicGeometry.Space.SquareZeroExtension.full_thickenedChartFunctor`
* `AlgebraicGeometry.Space.SquareZeroExtension.inverseImageHom_ext`: maps out of `i⁻¹𝒪_{X'}` are
  determined by their chart components on the charts `W ⟶ W'`.
* `AlgebraicGeometry.Space.SquareZeroExtension.quotientSheafIso_hom_comp_π`

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.SquareZeroExtension

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- Restricting to the chart cut out by the whole of `V` after `g : V ⟶ U` is restricting along
`g` the chart cut out by the whole of `U`. -/
theorem chartOpensRestrict_top_comp_chartOpensTopHom {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    chartOpensRestrict B S hS g ⊤ ≫ chartOpensTopHom B S hS X U = chartOpensTopHom B S hS X V ≫ g :=
  hom_ext_of_toScheme_map_eq B S hS (morphismRestrict_ι (chartSchemeMap g) ⊤)

/-- **`𝒜(W) ≅ Γ(W', ⊤)` is natural in the chart.** -/
theorem chartRealizedSchemeΓIso_naturality {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    E.A.obj.map g.op ≫ (E.chartRealizedSchemeΓIso V).hom =
      (E.chartRealizedSchemeΓIso U).hom ≫ (E.chartRealizedSchemeMap g).appTop := by
  show E.A.obj.map g.op ≫ E.A.obj.map (chartOpensTopHom B S hS X V).op =
    E.A.obj.map (chartOpensTopHom B S hS X U).op ≫ E.A.obj.map (chartOpensRestrict B S hS g ⊤).op
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
    chartOpensRestrict_top_comp_chartOpensTopHom]
  rfl

/-- The inverse `Γ(W', ⊤) ≅ 𝒜(W)` is natural in the chart. -/
theorem chartRealizedSchemeΓIso_inv_naturality {U V : SmallEtale B S hS X.1} (g : V ⟶ U) :
    (E.chartRealizedSchemeMap g).appTop ≫ (E.chartRealizedSchemeΓIso V).inv =
      (E.chartRealizedSchemeΓIso U).inv ≫ E.A.obj.map g.op := by
  rw [Iso.comp_inv_eq, Category.assoc, chartRealizedSchemeΓIso_naturality, Iso.inv_hom_id_assoc]

variable (P : Presentation B S hS X.obj X.property)
  (hU : B.Contains (E.chartRealizedScheme (presentationChart P)))
  (hR : B.Contains (E.chartRealizedScheme (presentationRelationChart P)))

/-- **`(i_*𝒜)(W') ≃+* 𝒜(W)` is natural in `W`.** -/
theorem thickenedChartRingEquiv_naturality
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) {W₁ W₂ : OverPresentation P}
    (g : W₁ ⟶ W₂)
    (x : (ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) A).obj.obj
        (op ((E.thickenedChartFunctor P hU hR).obj W₂))) :
    E.thickenedChartRingEquiv P hU hR A W₁
        ((ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) A).obj.map
          ((E.thickenedChartFunctor P hU hR).map g).op x) =
      A.obj.map g.hom.op (E.thickenedChartRingEquiv P hU hR A W₂ x) := by
  let Q := (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).obj
    (ringSheafOf B S hS A)
  have e : ∀ (W : OverPresentation P)
      (y : (ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) A).obj.obj
        (op ((E.thickenedChartFunctor P hU hR).obj W))),
      E.thickenedChartRingEquiv P hU hR A W y =
        (ranChartCone B S hS X Q.obj (chartBaseChange B S hS (E.thickeningImmersion P hU hR)
          ((E.thickenedChartFunctor P hU hR).obj W))).π.app
          (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) y :=
    fun W y ↦ chartProjection_app B S hS _ Q _ _ y
  rw [e, e]
  exact (ranFmap B S hS (E.thickeningImmersion P hU hR) Q _ (𝟙 _)).naturality
    (E.thickenedChartDiagram P hU hR W₂) (E.thickenedChartDiagram P hU hR W₁) g.hom
    ((E.thickenedChartFunctor P hU hR).map g)
    (E.chartInclusionOver_comp_chartRealizedSchemeOverMap g.hom _ _).symm x

/-- **`𝒪_{X'}(W') ≅ (i_*𝒜)(W')` on the charts `W'` attached to the charts `W` of `X` over `U`**,
naturally in `W`: `𝒪_{X'}(W') = Γ(W', ⊤) ≅ 𝒜(W) ≅ (i_*𝒜)(W')`. -/
noncomputable def thickenedChartStructureIso :
    (E.thickenedChartFunctor P hU hR).op ⋙
        (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O.obj ≅
      (E.thickenedChartFunctor P hU hR).op ⋙
        (ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) E.A).obj :=
  NatIso.ofComponents (fun W ↦ (E.chartRealizedSchemeΓIso W.unop.obj).symm ≪≫
      (E.thickenedChartRingEquiv P hU hR E.A W.unop).symm.toCommRingCatIso) (by
    intro W₂ W₁ g
    ext x
    apply (E.thickenedChartRingEquiv P hU hR E.A W₁.unop).injective
    change E.thickenedChartRingEquiv P hU hR E.A W₁.unop
        ((E.thickenedChartRingEquiv P hU hR E.A W₁.unop).symm
          ((E.chartRealizedSchemeΓIso W₁.unop.obj).inv
            ((E.chartRealizedSchemeMap g.unop.hom).appTop x))) =
      E.thickenedChartRingEquiv P hU hR E.A W₁.unop
        ((ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) E.A).obj.map
          ((E.thickenedChartFunctor P hU hR).map g.unop).op
          ((E.thickenedChartRingEquiv P hU hR E.A W₂.unop).symm
            ((E.chartRealizedSchemeΓIso W₂.unop.obj).inv x)))
    rw [RingEquiv.apply_symm_apply, thickenedChartRingEquiv_naturality,
      RingEquiv.apply_symm_apply]
    exact ConcreteCategory.congr_hom (E.chartRealizedSchemeΓIso_inv_naturality g.unop.hom) x)

/-! ### The charts `W'` are cover-dense in the small étale site of `X'` -/

/-- Base change of étale scheme charts along `i : X ⟶ X'`. -/
noncomputable abbrev quotientChartBaseChange :
    SmallEtale B S hS (E.thickeningQuotient hS P hU hR).1 ⥤ SmallEtale B S hS X.1 :=
  smallBaseChange B S hS (E.thickeningImmersion P hU hR)
    (E.isClosedImmersion_thickeningImmersion P hU hR).rep

/-- **Base change of étale charts along `X ⟶ X'` is full**: it is spaces-étale base change on
charts (Stacks 03G2), which is fully faithful along a thickening (Stacks 05ZH). -/
theorem full_quotientChartBaseChange : (E.quotientChartBaseChange P hU hR).Full := by
  let i := E.thickeningImmersion P hU hR
  have : (spacesBaseChange B S hS i).functor.Full :=
    (fullyFaithfulSpacesBaseChangeOfIsThickeningHom B S hS i
      (E.isThickeningHom_thickeningImmersion P hU hR)).full
  have := comparisonFunctor_full B S hS (E.thickeningQuotient hS P hU hR)
  have := comparisonFunctor_faithful B S hS X
  have : (E.quotientChartBaseChange P hU hR ⋙ comparisonFunctor B S hS X).Full :=
    Functor.Full.of_iso (smallBaseChange_comparison B S hS i
      (E.isClosedImmersion_thickeningImmersion P hU hR).rep).symm
  exact Functor.Full.of_comp_faithful _ (comparisonFunctor B S hS X)

/-- Base change of étale charts along the surjective closed immersion `X ⟶ X'` is faithful. -/
theorem faithful_quotientChartBaseChange : (E.quotientChartBaseChange P hU hR).Faithful :=
  smallBaseChange_faithful_of_surjective B S hS (E.thickeningImmersion P hU hR)
    (E.isClosedImmersion_thickeningImmersion P hU hR)
    (E.isThickeningHom_thickeningImmersion P hU hR).surjective

/-- **`W ≅ X ×_{X'} W'`** on schemes: the chart `W` and the chosen fibre product are two
pullbacks of the same cospan (`isPullback_thickenedChartDiagram`). -/
noncomputable def thickenedChartBaseChangeSchemeIso (W : OverPresentation P) :
    W.obj.obj.left ≅ (E.isClosedImmersion_thickeningImmersion P hU hR).rep.pullback
      ((E.thickenedChartFunctor P hU hR).obj W).1.hom :=
  (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).preimageIso
    ((E.isPullback_thickenedChartDiagram P hU hR W).isoIsPullback _ _
      ((E.isClosedImmersion_thickeningImmersion P hU hR).rep.isPullback
        ((E.thickenedChartFunctor P hU hR).obj W).1.hom))

/-- The image under the Yoneda embedding of `W ⟶ X ×_{X'} W'` is the comparison isomorphism of
the two pullbacks. -/
theorem yoneda_map_thickenedChartBaseChangeSchemeIso_hom (W : OverPresentation P) :
    yoneda.map (E.thickenedChartBaseChangeSchemeIso P hU hR W).hom =
      ((E.isPullback_thickenedChartDiagram P hU hR W).isoIsPullback _ _
        ((E.isClosedImmersion_thickeningImmersion P hU hR).rep.isPullback
          ((E.thickenedChartFunctor P hU hR).obj W).1.hom)).hom :=
  (Yoneda.fullyFaithful (C := BigFppfOver B S hS)).map_preimage _

/-- The isomorphism `W ≅ X ×_{X'} W'` followed by the first projection is the structure map
`W ⟶ X`. -/
theorem thickenedChartBaseChangeSchemeIso_hom_fst (W : OverPresentation P) :
    yoneda.map (E.thickenedChartBaseChangeSchemeIso P hU hR W).hom ≫
        (E.isClosedImmersion_thickeningImmersion P hU hR).rep.fst
          ((E.thickenedChartFunctor P hU hR).obj W).1.hom =
      W.obj.obj.hom :=
  (congrArg (· ≫ (E.isClosedImmersion_thickeningImmersion P hU hR).rep.fst
      ((E.thickenedChartFunctor P hU hR).obj W).1.hom)
    (E.yoneda_map_thickenedChartBaseChangeSchemeIso_hom P hU hR W)).trans
    (IsPullback.isoIsPullback_hom_fst _ _ _ _)

/-- The isomorphism `W ≅ X ×_{X'} W'` followed by the second projection is the map `W ⟶ W'`. -/
theorem thickenedChartBaseChangeSchemeIso_hom_snd (W : OverPresentation P) :
    (E.thickenedChartBaseChangeSchemeIso P hU hR W).hom ≫
        (E.isClosedImmersion_thickeningImmersion P hU hR).rep.snd
          ((E.thickenedChartFunctor P hU hR).obj W).1.hom =
      (E.thickenedChartDiagram P hU hR W).g :=
  yoneda.map_injective ((yoneda.map_comp _ _).trans
    ((congrArg (· ≫ yoneda.map ((E.isClosedImmersion_thickeningImmersion P hU hR).rep.snd
        ((E.thickenedChartFunctor P hU hR).obj W).1.hom))
      (E.yoneda_map_thickenedChartBaseChangeSchemeIso_hom P hU hR W)).trans
      (IsPullback.isoIsPullback_hom_snd _ _ _ _)))

/-- **`W ≅ X ×_{X'} W'`** as charts of `X`. -/
noncomputable def thickenedChartBaseChangeIso (W : OverPresentation P) :
    W.obj ≅ (E.quotientChartBaseChange P hU hR).obj ((E.thickenedChartFunctor P hU hR).obj W) :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk (E.thickenedChartBaseChangeSchemeIso P hU hR W)
    (E.thickenedChartBaseChangeSchemeIso_hom_fst P hU hR W))

/-- The isomorphism of charts `W ≅ X ×_{X'} W'` followed by the second projection is the map
`W ⟶ W'`. -/
theorem thickenedChartBaseChangeIso_hom_snd (W : OverPresentation P) :
    (E.thickenedChartBaseChangeIso P hU hR W).hom.hom.left ≫
        (E.isClosedImmersion_thickeningImmersion P hU hR).rep.snd
          ((E.thickenedChartFunctor P hU hR).obj W).1.hom =
      (E.thickenedChartDiagram P hU hR W).g :=
  E.thickenedChartBaseChangeSchemeIso_hom_snd P hU hR W

/-- `W ≅ X ×_{X'} W'` is natural in `W`. -/
theorem thickenedChartBaseChangeIso_naturality {W₁ W₂ : OverPresentation P} (g : W₁ ⟶ W₂) :
    (E.thickenedChartBaseChangeIso P hU hR W₁).hom ≫
        (E.quotientChartBaseChange P hU hR).map ((E.thickenedChartFunctor P hU hR).map g) =
      g.hom ≫ (E.thickenedChartBaseChangeIso P hU hR W₂).hom := by
  let i := E.thickeningImmersion P hU hR
  let hf := (E.isClosedImmersion_thickeningImmersion P hU hR).rep
  refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _
    (Functor.relativelyRepresentable.hom_ext (F := yoneda) hf ?_ ?_))
  · exact (CostructuredArrow.w ((E.thickenedChartBaseChangeIso P hU hR W₁).hom ≫
        (E.quotientChartBaseChange P hU hR).map
          ((E.thickenedChartFunctor P hU hR).map g)).hom).trans
      (CostructuredArrow.w (g.hom ≫ (E.thickenedChartBaseChangeIso P hU hR W₂).hom).hom).symm
  · have h1 : (E.thickenedChartDiagram P hU hR W₁).g ≫
        ((E.thickenedChartFunctor P hU hR).map g).hom.left =
          g.hom.hom.left ≫ (E.thickenedChartDiagram P hU hR W₂).g :=
      E.chartInclusionOver_comp_chartRealizedSchemeOverMap g.hom _ _
    have h2 := smallBaseChange_map_snd B S hS i hf ((E.thickenedChartFunctor P hU hR).map g)
    have h3 := E.thickenedChartBaseChangeIso_hom_snd P hU hR W₁
    have h4 := E.thickenedChartBaseChangeIso_hom_snd P hU hR W₂
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans
      (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3)).trans
        (h1.trans ((congrArg (_ ≫ ·) h4.symm).trans (Category.assoc _ _ _).symm))))

/-- **`W ↦ W'` is full**: a morphism `W₁' ⟶ W₂'` of charts of `X'` is determined by its base
change along `X ⟶ X'`, which is a morphism `W₁ ⟶ W₂`. -/
theorem full_thickenedChartFunctor : (E.thickenedChartFunctor P hU hR).Full := by
  have := E.full_quotientChartBaseChange P hU hR
  have := E.faithful_quotientChartBaseChange P hU hR
  refine ⟨fun {W₁ W₂} h ↦ ⟨ObjectProperty.homMk ((E.thickenedChartBaseChangeIso P hU hR W₁).hom ≫
    (E.quotientChartBaseChange P hU hR).map h ≫
      (E.thickenedChartBaseChangeIso P hU hR W₂).inv), ?_⟩⟩
  apply (E.quotientChartBaseChange P hU hR).map_injective
  rw [← cancel_epi (E.thickenedChartBaseChangeIso P hU hR W₁).hom,
    thickenedChartBaseChangeIso_naturality]
  show ((E.thickenedChartBaseChangeIso P hU hR W₁).hom ≫
    (E.quotientChartBaseChange P hU hR).map h ≫
      (E.thickenedChartBaseChangeIso P hU hR W₂).inv) ≫
        (E.thickenedChartBaseChangeIso P hU hR W₂).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The charts `W'` are cover-dense in the small étale site of `X'`.** A sieve on a chart `Z`
of `X'` is covering when its base change along `X ⟶ X'` is (the base change of étale charts
along the surjective closed immersion `X ⟶ X'` is a dense subsite), and the base change of the
sieve of maps factoring through some `W'` contains every map from a chart `W` of `X` over `U`,
`W` being `X ×_{X'} W'`, by fullness of base change (Stacks 05ZH). -/
instance isCoverDense_thickenedChartFunctor :
    (E.thickenedChartFunctor P hU hR).IsCoverDense
      (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) where
  is_cover Z := by
    have := E.full_quotientChartBaseChange P hU hR
    have := smallBaseChange_isDenseSubsite_of_surjective B S hS (E.thickeningImmersion P hU hR)
      (E.isClosedImmersion_thickeningImmersion P hU hR)
      (E.isThickeningHom_thickeningImmersion P hU hR).surjective
    rw [← Functor.functorPushforward_mem_iff
      (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1)
      (SmallEtale.topology B S hS X.1) (G := E.quotientChartBaseChange P hU hR)]
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_
      ((overPresentationChart P).ι.is_cover_of_isCoverDense (SmallEtale.topology B S hS X.1)
        ((E.quotientChartBaseChange P hU hR).obj Z))
    rintro V v ⟨⟨W, l, m, hlm⟩⟩
    refine ⟨(E.thickenedChartFunctor P hU hR).obj W,
      (E.quotientChartBaseChange P hU hR).preimage
        ((E.thickenedChartBaseChangeIso P hU hR W).inv ≫ m),
      l ≫ (E.thickenedChartBaseChangeIso P hU hR W).hom,
      ⟨⟨W, 𝟙 _, _, Category.id_comp _⟩⟩, ?_⟩
    rw [Functor.map_preimage, Category.assoc, Iso.hom_inv_id_assoc]
    exact hlm.symm

/-- The functor `W ↦ W'` is locally full for the small étale topology of `X'`. -/
instance isLocallyFull_thickenedChartFunctor :
    (E.thickenedChartFunctor P hU hR).IsLocallyFull
      (SmallEtale.topology B S hS (E.thickeningQuotient hS P hU hR).1) :=
  have := E.full_thickenedChartFunctor P hU hR
  inferInstance

/-! ### The structure sheaf of `X'` and the extension -/

/-- `𝒪_{X'} ≅ i_*𝒜`, with the direct image in its right Kan extension form: the isomorphism on
the cover-dense charts `W'` extends uniquely. -/
noncomputable def structureIsoRingDirectImageRan :
    (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O ≅
      ringDirectImageRan B S hS (E.thickeningImmersion P hU hR) E.A :=
  Functor.IsCoverDense.sheafIso (E.thickenedChartStructureIso P hU hR)

/-- Restricted to the charts `W'`, the isomorphism `𝒪_{X'} ≅ i_*𝒜` is the isomorphism
`thickenedChartStructureIso`. -/
theorem whiskerLeft_structureIsoRingDirectImageRan_hom :
    Functor.whiskerLeft (E.thickenedChartFunctor P hU hR).op
        (E.structureIsoRingDirectImageRan P hU hR).hom.hom =
      (E.thickenedChartStructureIso P hU hR).hom :=
  Functor.IsCoverDense.sheafHom_restrict_eq _

/-- **`𝒪_{X'} ≅ i_*𝒜`.** -/
noncomputable def structureIsoPushforward :
    (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O ≅
      (smallEtaleRingedToposHom B S hS
        (E.thickeningImmersion P hU hR)).toToposHom.pushforwardRing.obj E.A :=
  E.structureIsoRingDirectImageRan P hU hR ≪≫
    (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) E.A).symm

/-- The direct image along `X ⟶ X'` is an equivalence of small étale topoi (Stacks 05ZM). -/
theorem isEquivalence_pushforward_thickeningImmersion :
    (smallEtaleRingedToposHom B S hS
      (E.thickeningImmersion P hU hR)).toToposHom.pushforward.IsEquivalence :=
  isEquivalence_pushforward_smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)
    (E.isClosedImmersion_thickeningImmersion P hU hR)
    (E.isThickeningHom_thickeningImmersion P hU hR).surjective

/-- **The structure sheaf of the thickened quotient is the extension**: `i⁻¹𝒪_{X'} ≅ 𝒜`, the
adjoint of `𝒪_{X'} ≅ i_*𝒜`. -/
noncomputable def quotientSheafIso :
    (smallEtaleRingedToposHom B S hS
      (E.thickeningImmersion P hU hR)).toToposHom.inverseImageRing.obj
        (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O ≅ E.A :=
  have := E.isEquivalence_pushforward_thickeningImmersion P hU hR
  MorphismOfTopoi.ringAdjunctionIsoOfIso _ (E.structureIsoPushforward P hU hR)

/-- **Maps out of `i⁻¹𝒪_{X'}` are determined by their chart components on the charts `W ⟶ W'`.** -/
theorem inverseImageHom_ext {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    {φ₁ φ₂ : (smallEtaleRingedToposHom B S hS
      (E.thickeningImmersion P hU hR)).toToposHom.inverseImageRing.obj
        (smallEtaleRingedTopos B S hS (E.thickeningQuotient hS P hU hR)).O ⟶ A}
    (h : ∀ (W : OverPresentation P) x,
      inverseImageHomChartRingHom B S hS (E.thickeningImmersion P hU hR) A φ₁
          (E.thickenedChartDiagram P hU hR W).V
          (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) x =
        inverseImageHomChartRingHom B S hS (E.thickeningImmersion P hU hR) A φ₂
          (E.thickenedChartDiagram P hU hR W).V
          (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) x) :
    φ₁ = φ₂ := by
  let t := (smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)).toToposHom
  apply (t.ringAdjunction.homEquiv _ _).injective
  rw [← Iso.cancel_iso_hom_right _ _
    (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) A)]
  apply Sheaf.hom_ext
  refine (Functor.IsCoverDense.restrictHomEquivHom
    (G := E.thickenedChartFunctor P hU hR)).symm.injective ?_
  ext W x
  exact (E.bijective_ringChartProjection_thickenedChartDiagram P hU hR A W.unop).1 (h W.unop x)

/-- Restricting a global section of a scheme to an open `O` and then mapping back along
`op O ⟶ op ⊤` returns the section. -/
theorem _root_.AlgebraicGeometry.Scheme.presheaf_map_map_top {Z : Scheme.{u}} {O : Z.Opens}
    (a : op ⊤ ⟶ op O) (b : op O ⟶ op ⊤) (y : Γ(Z, ⊤)) :
    Z.presheaf.map b (Z.presheaf.map a y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, Subsingleton.elim (a ≫ b) (𝟙 _),
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]

/-- The map `Γ(W', ⊤) = 𝒜(W) ⟶ 𝒪_X(W)` is pullback along `W ⟶ W'`. -/
theorem chartInclusion_appTop_chartRealizedSchemeΓIso (W : SmallEtale B S hS X.1)
    (a : E.A.obj.obj (op W)) :
    (E.chartInclusion W).appTop ((E.chartRealizedSchemeΓIso W).hom a) = E.π.hom.app (op W) a := by
  have hn : E.π.hom.app (op ((chartOpens B S hS W).obj ⊤))
      (E.A.obj.map (chartOpensTopHom B S hS X W).op a) =
        (smallEtaleRingedTopos B S hS X).O.obj.map (chartOpensTopHom B S hS X W).op
          (E.π.hom.app (op W) a) :=
    ConcreteCategory.congr_hom (E.π.hom.naturality (chartOpensTopHom B S hS X W).op) a
  refine (congrArg (chartΓEquiv W (op ⊤)) hn).trans ?_
  show (chartScheme W).presheaf.map _ ((chartScheme W).presheaf.map _ _) = _
  exact Scheme.presheaf_map_map_top _ _ _

/-- The map `Γ(W', ⊤) ⟶ 𝒪_X(W)` sends `x` to the image under `π` of the section of `𝒜(W)`
corresponding to `x`. -/
theorem chartInclusion_appTop_eq (W : SmallEtale B S hS X.1)
    (x : Γ(E.chartRealizedScheme W, ⊤)) :
    (E.chartInclusion W).appTop x = E.π.hom.app (op W) ((E.chartRealizedSchemeΓIso W).inv x) := by
  have h := E.chartInclusion_appTop_chartRealizedSchemeΓIso W ((E.chartRealizedSchemeΓIso W).inv x)
  rwa [Iso.inv_hom_id_apply] at h

/-- **`i⁻¹𝒪_{X'} ≅ 𝒜` is compatible with the maps to `𝒪_X`** (`quotient_compatibility` of
Stacks 05ZT). -/
theorem quotientSheafIso_hom_comp_π :
    (E.quotientSheafIso P hU hR).hom ≫ E.π =
      (smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)).fSharpInverseImage := by
  refine E.inverseImageHom_ext P hU hR (fun W x ↦ ?_)
  rw [inverseImageHomChartRingHom_comp, inverseImageHomChartRingHom_fSharpInverseImage,
    chartPullback, chartBaseChangeMap_indexOfChartDiagram]
  have h1 : inverseImageHomChartRingHom B S hS (E.thickeningImmersion P hU hR) E.A
      (E.quotientSheafIso P hU hR).hom (E.thickenedChartDiagram P hU hR W).V
      (indexOfChartDiagram B S hS _ (E.thickenedChartDiagram P hU hR W)) x =
        (E.chartRealizedSchemeΓIso W.obj).inv x := by
    let t := (smallEtaleRingedToposHom B S hS (E.thickeningImmersion P hU hR)).toToposHom
    have he : t.ringAdjunction.homEquiv _ _ (E.quotientSheafIso P hU hR).hom ≫
        (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) E.A).hom =
          (E.structureIsoRingDirectImageRan P hU hR).hom := by
      show t.ringAdjunction.homEquiv _ _ ((t.ringAdjunction.homEquiv _ _).symm
        (E.structureIsoPushforward P hU hR).hom) ≫ _ = _
      rw [Equiv.apply_symm_apply]
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
        (Category.comp_id _))
    show ringDirectImageRanChartProjection B S hS _ E.A _ _
      ((t.ringAdjunction.homEquiv _ _ (E.quotientSheafIso P hU hR).hom ≫
        (pushforwardRingIsoRan B S hS (E.thickeningImmersion P hU hR) E.A).hom).hom.app _ x) = _
    rw [he]
    have hx := ConcreteCategory.congr_hom (congrArg (fun α ↦ α.app (op W))
      (E.whiskerLeft_structureIsoRingDirectImageRan_hom P hU hR)) x
    change (E.structureIsoRingDirectImageRan P hU hR).hom.hom.app _ x =
      (E.thickenedChartRingEquiv P hU hR E.A W).symm ((E.chartRealizedSchemeΓIso W.obj).inv x) at hx
    rw [hx]
    exact (E.thickenedChartRingEquiv P hU hR E.A W).apply_symm_apply _
  rw [h1]
  exact (E.chartInclusion_appTop_eq W.obj x).symm

end AlgebraicGeometry.Space.SquareZeroExtension

end
