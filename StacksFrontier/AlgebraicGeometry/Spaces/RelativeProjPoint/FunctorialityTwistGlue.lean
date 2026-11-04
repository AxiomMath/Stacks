module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwist

/-!
# Gluing a map `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` on `U(ψ)` from the charts

Let `ψ` be a map of graded algebras read over the scheme points of the base
(`AlgebraicGeometry.Space.RelativeProjHomPoints`), between the presentations of `P` and `Q`, let
`U(ψ) ⊆ Q` be its open subspace with `r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q`, and let
`U(ψ) = U(ψ)_U / U(ψ)_R` be the presentation of `presentationOfBase` over a presentation `X = U/R`.
Modules `𝒟₁` on `P` and `𝒟₂` on `Q` descended from quasi-coherent modules `M₁`, `M₂` on the schemes
of `U ×_X P`, `U ×_X Q` with scheme transitions `τ₁`, `τ₂` (chart identifications `c₁`, `c₂`
carrying the canonical descent data to the transitions attached to `τ₁`, `τ₂`) have inverse images
`r_ψ^*𝒟₁`, `ι^*𝒟₂` whose charts on `U(ψ)_U` are the scheme pullbacks of `M₁`, `M₂` along the
charts of `r_ψ` and `ι` (Lemma K). A morphism `θ_U` of these scheme pullbacks compatible with the
pullbacks of `τ₁` and `τ₂` to `U(ψ)_R` glues to a unique morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂`.

Everything is stated at variable families of points and a variable map `ψ`, so that the families of
points are never unfolded.

## Main definitions

* `AlgebraicGeometry.Space.Presentation.IsAtlasMapComp`: a morphism whose inverse image along the
  atlas, followed by a chart identification, is a given composite.
* `AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`: the chart identification of
  Lemma K.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.ChartTransitionsCompatible` and
  `…IsChartHom`: the compatibility of `θ_U` with the pulled-back transitions, and a morphism
  `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` which is `θ_U` on the chart.

## Main results

* `Space.Presentation.existsUnique_modulePullback_atlas_map_comp_eq_of_transitionCommutes`:
  gluing along an étale presentation from charts carrying the transitions.
* `AlgebraicGeometry.Space.RelativeProjPoints.transitionCommutes_atlasPullbackChartIso`: Lemma K.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.existsUnique_isChartHom`: the gluing on `U(ψ)`;
  `…existsUnique_isDescendedChartHom` for modules descended along the presentations of `P`, `Q`.

## Implementation notes

`CategoryTheory.yoneda` is locally irreducible: the atlas of a presentation has source
`schemeSpace U`, which unifies with `⟨yoneda.obj U, _⟩` by unfolding `schemeSpace`; unfolding
`yoneda` instead does not terminate in practice.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- `AlgebraicGeometry.Space.transitionCommutes_canonicalComparison_of_square`, with the chart
identification `φ'^*f^*D ≅ C'` written as one composite isomorphism. -/
theorem transitionCommutes_canonicalComparison_trans_of_square
    {X Y U U' R R' : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (φ : U ⟶ X) (φ' : U' ⟶ Y) (fU : U' ⟶ U) (t s : R ⟶ U) (t' s' : R' ⟶ U')
    (ρ : R' ⟶ R) (hsq : φ' ≫ f = fU ≫ φ) (ht : t' ≫ fU = ρ ≫ t) (hs : ρ ≫ s = s' ≫ fU)
    (hw : t ≫ φ = s ≫ φ) (hw' : t' ≫ φ' = s' ≫ φ') (D : Modules.{u, u} B S hS X.1 X.2)
    {C : Modules.{u, u} B S hS U.1 U.2} (c : (modulePullback B S hS φ).obj D ≅ C)
    (αX : (modulePullback B S hS t).obj ((modulePullback B S hS φ).obj D) ⟶
      (modulePullback B S hS s).obj ((modulePullback B S hS φ).obj D))
    (hα : (canonicalComparison (ρ ≫ t) (ρ ≫ s) φ φ
        (by rw [Category.assoc, Category.assoc, hw]) D).hom = modulePullbackReindex ρ αX)
    (β : (modulePullback B S hS t).obj C ⟶ (modulePullback B S hS s).obj C)
    (hcomm : TransitionCommutes B S hS αX β c.hom)
    {C' : Modules.{u, u} B S hS U'.1 U'.2} (ε : (modulePullback B S hS fU).obj C ≅ C')
    (β' : (modulePullback B S hS t').obj C' ⟶ (modulePullback B S hS s').obj C')
    (hC : TransitionCommutes B S hS ((canonicalComparison t' ρ fU t ht C).hom ≫
      (modulePullback B S hS ρ).map β ≫ (canonicalComparison ρ s' s fU hs C).hom) β' ε.hom) :
    TransitionCommutes B S hS
      (canonicalComparison t' s' φ' φ' hw' ((modulePullback B S hS f).obj D)).hom β'
      (canonicalComparison φ' fU f φ hsq D ≪≫ (modulePullback B S hS fU).mapIso c ≪≫ ε).hom :=
  transitionCommutes_canonicalComparison_of_square f φ φ' fU t s t' s' ρ hsq ht hs hw hw' D c αX
    hα β hcomm ε β' hC

/-- A morphism `χ : M ⟶ N` whose inverse image along the atlas of a presentation, followed by a
chart identification `e_N`, is `κ_M ≫ θ`. -/
def Presentation.IsAtlasMapComp {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    {C D : Modules.{u, u} B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U)}
    (eN : Iso.{u + 1} ((modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj N) D)
    (κM : (modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj M ⟶ C)
    (θ : C ⟶ D) (χ : M ⟶ N) : Prop :=
  (modulePullback B S hS (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩)
    P.atlas).map χ ≫ eN.hom = κM ≫ θ

/-- **Gluing a morphism along an étale presentation from charts carrying the transitions**, with
the chart of the presentation and the projections of the relation written as represented morphisms
and the chart identification of the target an isomorphism: the glued morphism `χ` satisfies
`φ^*χ ≫ e_N = κ_M ≫ θ`. -/
theorem Presentation.existsUnique_modulePullback_atlas_map_comp_eq_of_transitionCommutes
    {X : AlgebraicSpaces B S hS} (P : Presentation B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2}
    {C D : Modules.{u, u} B S hS (yoneda.obj P.U) (isAlgebraicSpace_yoneda B S hS P.U)}
    {βM : (modulePullback B S hS (representedSpaceMap B S hS P.target)).obj C ⟶
      (modulePullback B S hS (representedSpaceMap B S hS P.source)).obj C}
    {βN : (modulePullback B S hS (representedSpaceMap B S hS P.target)).obj D ⟶
      (modulePullback B S hS (representedSpaceMap B S hS P.source)).obj D}
    {κM : (modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj M ⟶ C}
    (eN : Iso.{u + 1} ((modulePullback B S hS
      (X := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas).obj N) D)
    (hM : TransitionCommutes B S hS
      (canonicalComparison (representedSpaceMap B S hS P.target)
        (representedSpaceMap B S hS P.source) P.atlas P.atlas P.relationTarget_comp_atlas M).hom
      βM κM)
    (hN : TransitionCommutes B S hS
      (canonicalComparison (representedSpaceMap B S hS P.target)
        (representedSpaceMap B S hS P.source) P.atlas P.atlas P.relationTarget_comp_atlas N).hom
      βN eN.hom)
    {θ : C ⟶ D} (hθ : TransitionCommutes B S hS βM βN θ) :
    ∃! χ : M ⟶ N, P.IsAtlasMapComp eN κM θ χ := by
  obtain ⟨χ, hχ, hu⟩ := existsUnique_modulePullback_map_eq_of_relation B S hS
    (U := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas
    ((isEtale_iff_presheaf_of_yoneda B S hS P.toSpace).2 P.etale)
    (relativelyRepresentable_of_representableSource B S hS
      (P := ⟨yoneda.obj P.U, isAlgebraicSpace_yoneda B S hS P.U⟩) P.atlas P.U (Iso.refl _))
    (isEtaleCovering_atlas B S hS X.2 P.surjective P.etale)
    (representedSpaceMap B S hS P.target) (representedSpaceMap B S hS P.source)
    P.isPullback P.relationTarget_comp_atlas (κM ≫ θ ≫ eN.inv)
    (hM.trans (hθ.trans hN.inv)).symm
  unfold Presentation.IsAtlasMapComp
  refine ⟨χ, ?_, fun χ' h => hu χ' ?_⟩
  · exact (Iso.eq_comp_inv eN).1 (hχ.trans (Category.assoc _ _ _).symm)
  · exact ((Iso.eq_comp_inv eN).2 h).trans (Category.assoc _ _ _)

namespace RelativeProjHomPoints

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)

/-! ### The squares of the charts of `r_ψ` and `ι` over the projections of the relations -/

/-- The target projection of `presentationOfBase` lies over the target projection of the
presentation of `P` along the charts of `r_ψ`. -/
theorem presentationOfBase_target_comp_chartMapHom_spaceTarget :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).target (hψ.chartMapHom Px.U Px.toSpace) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dP.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) (dP.spaceTarget Px hP) :=
  hψ.presentationOfBase_target_comp_chartMapHom Px hG

/-- The source projection of `presentationOfBase` lies over the source projection of the
presentation of `P` along the charts of `r_ψ`. -/
theorem chartMapHom_spaceSource_comp_presentationOfBase_source :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dP.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) (dP.spaceSource Px hP) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).source (hψ.chartMapHom Px.U Px.toSpace) :=
  hψ.chartMapHom_comp_presentationOfBase_source Px hG

/-- The target projection of `presentationOfBase` lies over the target projection of the
presentation of `Q` along the inclusions of the charts. -/
theorem presentationOfBase_target_comp_chartIncl_spaceTarget :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).target (hψ.chartIncl Px.U Px.toSpace) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dQ.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) (dQ.spaceTarget Px hQ) :=
  hψ.presentationOfBase_target_comp_chartIncl Px hG

/-- The source projection of `presentationOfBase` lies over the source projection of the
presentation of `Q` along the inclusions of the charts. -/
theorem chartIncl_spaceSource_comp_presentationOfBase_source :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dQ.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) (dQ.spaceSource Px hQ) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).source (hψ.chartIncl Px.U Px.toSpace) :=
  hψ.chartIncl_comp_presentationOfBase_source Px hG

end RelativeProjHomPoints

/-! ### Gluing along a presentation lying over the presentations of `P` and `Q` -/

namespace RelativeProjPoints

section ChartPullbackIso

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  {Y : AlgebraicSpaces B S hS} (f : Y ⟶ ⟨P, hP⟩) (P' : Presentation B S hS Y.1 Y.2)
  (fU : P'.U ⟶ d.fibre Px.U Px.toSpace) (fR : P'.R ⟶ d.fibre Px.R (relationPoint Px))
  (hsq : P'.atlas ≫ f = representedSpaceMap B S hS fU ≫
    presentationAtlas (d.spacePresentation Px hP))
  (ht : P'.target ≫ fU = fR ≫ d.spaceTarget Px hP)
  (hs : fR ≫ d.spaceSource Px hP = P'.source ≫ fU)
  (D : Modules.{u, u} B S hS P hP)
  (M : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (d.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ : quasicoherentPullbackObj B S hS (d.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (d.spaceSource Px hP) M)
  (c : (modulePullback B S hS (presentationAtlas (d.spacePresentation Px hP))).obj D ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
      M).obj)

/-- **The chart identification of Lemma K**: for `f : Y ⟶ P` and a presentation `Y = U'/R'`
whose atlas lies over the chart `P_U ⟶ P` along `fU`, `φ'^*f^*𝒟 ≅ fU^*φ^*𝒟 ≅ fU^*C ≅ (fU^*M)^a`. -/
def atlasPullbackChartIso :
    (modulePullback B S hS (X := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
        P'.atlas).obj ((modulePullback B S hS f).obj D) ≅
      ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.obj
        (quasicoherentPullbackObj B S hS fU M)).obj :=
  canonicalComparison (P := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
      P'.atlas (representedSpaceMap B S hS fU) f
      (presentationAtlas (d.spacePresentation Px hP)) hsq D ≪≫
    (modulePullback B S hS (representedSpaceMap B S hS fU)).mapIso c ≪≫
    modulePullbackRepresentedQuasicoherentIso B S hS fU M

include ht hs in
/-- **Lemma K, through `AlgebraicGeometry.Space.RelativeProjPoints.atlasPullbackChartIso`.** -/
theorem transitionCommutes_atlasPullbackChartIso
    (hcomm : TransitionCommutes B S hS
      (U := (presentationGroupoid (d.spacePresentation Px hP)).objects)
      (V := (presentationGroupoid (d.spacePresentation Px hP)).arrows)
      (a := (presentationGroupoid (d.spacePresentation Px hP)).target)
      (b := (presentationGroupoid (d.spacePresentation Px hP)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (d.spacePresentation Px hP))
        (presentationAtlas (d.spacePresentation Px hP)) (presentationAtlas_comm _) D)
      (presentationSchemeTransition (d.spacePresentation Px hP) M τ) c.hom) :
    TransitionCommutes B S hS
      (canonicalComparison (representedSpaceMap B S hS P'.target)
        (representedSpaceMap B S hS P'.source) P'.atlas P'.atlas
        P'.relationTarget_comp_atlas ((modulePullback B S hS f).obj D)).hom
      (representedSchemeTransition B S hS P'.target P'.source
        (quasicoherentPullbackObj B S hS fU M)
        (schemeTransitionPullback B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP)
          P'.target P'.source fU fR ht hs M τ))
      (atlasPullbackChartIso d Px hP f P' fU hsq D M c).hom :=
  transitionCommutes_canonicalComparison_trans_of_square
    (X := ⟨P, hP⟩) (Y := Y)
    (U := ⟨yoneda.obj (d.fibre Px.U Px.toSpace), isAlgebraicSpace_yoneda B S hS _⟩)
    (U' := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS P'.U⟩)
    (R := ⟨yoneda.obj (d.fibre Px.R (relationPoint Px)), isAlgebraicSpace_yoneda B S hS _⟩)
    (R' := ⟨yoneda.obj P'.R, isAlgebraicSpace_yoneda B S hS _⟩) f
    (presentationAtlas (d.spacePresentation Px hP)) P'.atlas (representedSpaceMap B S hS fU)
    (representedSpaceMap B S hS (d.spaceTarget Px hP))
    (representedSpaceMap B S hS (d.spaceSource Px hP))
    (representedSpaceMap B S hS P'.target) (representedSpaceMap B S hS P'.source)
    (representedSpaceMap B S hS fR) hsq (representedSpaceMap_comp_eq_of_comp_eq B S hS ht)
    (representedSpaceMap_comp_eq_of_comp_eq B S hS hs) (presentationAtlas_comm _)
    P'.relationTarget_comp_atlas D c _
    (canonicalComparison_hom_eq_reindex_spaceBaseDescent_represented d Px hP P' fR D) _
    (transitionCommutes_represented_of_presentationGroupoid d Px hP D M τ c hcomm)
    (modulePullbackRepresentedQuasicoherentIso B S hS fU M) _
    (transitionCommutes_representedSchemeTransition_pullback B S hS (d.spaceTarget Px hP)
      (d.spaceSource Px hP) P'.target P'.source fU fR ht hs M τ)

end ChartPullbackIso

section Glue

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} (dP : RelativeProjPoints B S hS πP) (dQ : RelativeProjPoints B S hS πQ)
  (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  {Y : AlgebraicSpaces B S hS} (P' : Presentation B S hS Y.1 Y.2)
  (f₁ : Y ⟶ ⟨P, hP⟩) (fU₁ : P'.U ⟶ dP.fibre Px.U Px.toSpace)
  (fR₁ : P'.R ⟶ dP.fibre Px.R (relationPoint Px))
  (hsq₁ : P'.atlas ≫ f₁ = representedSpaceMap B S hS fU₁ ≫
    presentationAtlas (dP.spacePresentation Px hP))
  (ht₁ : P'.target ≫ fU₁ = fR₁ ≫ dP.spaceTarget Px hP)
  (hs₁ : fR₁ ≫ dP.spaceSource Px hP = P'.source ≫ fU₁)
  (f₂ : Y ⟶ ⟨Q, hQ⟩) (fU₂ : P'.U ⟶ dQ.fibre Px.U Px.toSpace)
  (fR₂ : P'.R ⟶ dQ.fibre Px.R (relationPoint Px))
  (hsq₂ : P'.atlas ≫ f₂ = representedSpaceMap B S hS fU₂ ≫
    presentationAtlas (dQ.spacePresentation Px hQ))
  (ht₂ : P'.target ≫ fU₂ = fR₂ ≫ dQ.spaceTarget Px hQ)
  (hs₂ : fR₂ ≫ dQ.spaceSource Px hQ = P'.source ≫ fU₂)
  (D₁ : Modules.{u, u} B S hS P hP)
  (M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₁ : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁ ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁)
  (c₁ : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁ ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁).obj)
  (hc₁ : TransitionCommutes B S hS
      (U := (presentationGroupoid (dP.spacePresentation Px hP)).objects)
      (V := (presentationGroupoid (dP.spacePresentation Px hP)).arrows)
      (a := (presentationGroupoid (dP.spacePresentation Px hP)).target)
      (b := (presentationGroupoid (dP.spacePresentation Px hP)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (dP.spacePresentation Px hP))
        (presentationAtlas (dP.spacePresentation Px hP)) (presentationAtlas_comm _) D₁)
      (presentationSchemeTransition (dP.spacePresentation Px hP) M₁ τ₁) c₁.hom)
  (D₂ : Modules.{u, u} B S hS Q hQ)
  (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₂ : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂ ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂)
  (c₂ : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂ ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂).obj)
  (hc₂ : TransitionCommutes B S hS
      (U := (presentationGroupoid (dQ.spacePresentation Px hQ)).objects)
      (V := (presentationGroupoid (dQ.spacePresentation Px hQ)).arrows)
      (a := (presentationGroupoid (dQ.spacePresentation Px hQ)).target)
      (b := (presentationGroupoid (dQ.spacePresentation Px hQ)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (dQ.spacePresentation Px hQ))
        (presentationAtlas (dQ.spacePresentation Px hQ)) (presentationAtlas_comm _) D₂)
      (presentationSchemeTransition (dQ.spacePresentation Px hQ) M₂ τ₂) c₂.hom)
  (θU : quasicoherentPullbackObj B S hS fU₁ M₁ ⟶ quasicoherentPullbackObj B S hS fU₂ M₂)

/-- **A morphism of the chart pullbacks compatible with the pulled-back transitions**: `θ_U :
fU₁^*M₁ ⟶ fU₂^*M₂` on the scheme of `U'` carries the pullback of `τ₁` along the morphism of
relations to the pullback of `τ₂`. -/
def ChartTransitionsCompatible : Prop :=
  schemeTransitionPullback B S hS (dP.spaceTarget Px hP) (dP.spaceSource Px hP) P'.target
      P'.source fU₁ fR₁ ht₁ hs₁ M₁ τ₁ ≫ quasicoherentPullbackMap B S hS P'.source θU =
    quasicoherentPullbackMap B S hS P'.target θU ≫
      schemeTransitionPullback B S hS (dQ.spaceTarget Px hQ) (dQ.spaceSource Px hQ) P'.target
        P'.source fU₂ fR₂ ht₂ hs₂ M₂ τ₂

variable (hθU : ChartTransitionsCompatible dP dQ Px hP hQ P' fU₁ fR₁ ht₁ hs₁ fU₂ fR₂ ht₂ hs₂
  M₁ τ₁ M₂ τ₂ θU)

include hc₁ hc₂ hθU in
/-- **Gluing from the charts**: for `f₁ : Y ⟶ P`, `f₂ : Y ⟶ Q` and a presentation `Y = U'/R'`
lying over the presentations of `P` and `Q`, a morphism `θ_U` of the chart pullbacks compatible
with the pulled-back transitions is, through the chart identifications of Lemma K, the inverse
image along the atlas of a unique morphism `f₁^*𝒟₁ ⟶ f₂^*𝒟₂`. -/
theorem existsUnique_isAtlasMapComp_atlasPullbackChartIso :
    ∃! χ : (modulePullback B S hS f₁).obj D₁ ⟶ (modulePullback B S hS f₂).obj D₂,
      P'.IsAtlasMapComp (atlasPullbackChartIso dQ Px hQ f₂ P' fU₂ hsq₂ D₂ M₂ c₂)
        (atlasPullbackChartIso dP Px hP f₁ P' fU₁ hsq₁ D₁ M₁ c₁).hom
        ((representedQuasicoherentSchemeEquivalence B S hS P'.U).functor.map θU).hom χ :=
  P'.existsUnique_modulePullback_atlas_map_comp_eq_of_transitionCommutes
    (atlasPullbackChartIso dQ Px hQ f₂ P' fU₂ hsq₂ D₂ M₂ c₂)
    (transitionCommutes_atlasPullbackChartIso dP Px hP f₁ P' fU₁ fR₁ hsq₁ ht₁ hs₁ D₁ M₁ τ₁ c₁ hc₁)
    (transitionCommutes_atlasPullbackChartIso dQ Px hQ f₂ P' fU₂ fR₂ hsq₂ ht₂ hs₂ D₂ M₂ τ₂ c₂ hc₂)
    (representedSchemeTransition_naturality B S hS _ _ _ _ _ θU hθU)

end Glue

end RelativeProjPoints


namespace RelativeProjHomPoints

section Glue

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  (D₁ : Modules.{u, u} B S hS P hP)
  (M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₁ : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁ ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁)
  (c₁ : (modulePullback B S hS (presentationAtlas (dP.spacePresentation Px hP))).obj D₁ ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dP.fibre Px.U Px.toSpace)).functor.obj
      M₁).obj)
  (hc₁ : TransitionCommutes B S hS
      (U := (presentationGroupoid (dP.spacePresentation Px hP)).objects)
      (V := (presentationGroupoid (dP.spacePresentation Px hP)).arrows)
      (a := (presentationGroupoid (dP.spacePresentation Px hP)).target)
      (b := (presentationGroupoid (dP.spacePresentation Px hP)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (dP.spacePresentation Px hP))
        (presentationAtlas (dP.spacePresentation Px hP)) (presentationAtlas_comm _) D₁)
      (presentationSchemeTransition (dP.spacePresentation Px hP) M₁ τ₁) c₁.hom)
  (D₂ : Modules.{u, u} B S hS Q hQ)
  (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₂ : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂ ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂)
  (c₂ : (modulePullback B S hS (presentationAtlas (dQ.spacePresentation Px hQ))).obj D₂ ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dQ.fibre Px.U Px.toSpace)).functor.obj
      M₂).obj)
  (hc₂ : TransitionCommutes B S hS
      (U := (presentationGroupoid (dQ.spacePresentation Px hQ)).objects)
      (V := (presentationGroupoid (dQ.spacePresentation Px hQ)).arrows)
      (a := (presentationGroupoid (dQ.spacePresentation Px hQ)).target)
      (b := (presentationGroupoid (dQ.spacePresentation Px hQ)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (dQ.spacePresentation Px hQ))
        (presentationAtlas (dQ.spacePresentation Px hQ)) (presentationAtlas_comm _) D₂)
      (presentationSchemeTransition (dQ.spacePresentation Px hQ) M₂ τ₂) c₂.hom)
  (θU : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁ ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂)

/-- **The compatibility of a morphism of the chart pullbacks of `U(ψ)_U` with the pulled-back
transitions**, for the presentation `U(ψ) = U(ψ)_U / U(ψ)_R` of `presentationOfBase` and the charts
of `r_ψ` and of `ι`. -/
def ChartTransitionsCompatible : Prop :=
  RelativeProjPoints.ChartTransitionsCompatible dP dQ Px hP hQ
    (Y := ⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩) (hψ.presentationOfBase Px hG)
    (hψ.chartMapHom Px.U Px.toSpace)
    (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_target_comp_chartMapHom_spaceTarget Px hG hP)
    (hψ.chartMapHom_spaceSource_comp_presentationOfBase_source Px hG hP)
    (hψ.chartIncl Px.U Px.toSpace)
    (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_target_comp_chartIncl_spaceTarget Px hG hQ)
    (hψ.chartIncl_spaceSource_comp_presentationOfBase_source Px hG hQ) M₁ τ₁ M₂ τ₂ θU

/-- **A morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` which is `θ_U` on the chart `U(ψ)_U`**, through the chart
identifications of Lemma K for `r_ψ` and for `ι`. -/
def IsChartHom
    (χ : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj D₁ ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj D₂) :
    Prop :=
  Presentation.IsAtlasMapComp (X := ⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩)
    (hψ.presentationOfBase Px hG)
    (RelativeProjPoints.atlasPullbackChartIso dQ Px hQ
      (Y := ⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩)
      (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι) (hψ.presentationOfBase Px hG)
      (hψ.chartIncl Px.U Px.toSpace)
      (hψ.presentationOfBase_atlas_comp_relativeMapSubfunctor_ι Px hG hQ) D₂ M₂ c₂)
    (RelativeProjPoints.atlasPullbackChartIso dP Px hP
      (Y := ⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩)
      (ObjectProperty.homMk hψ.relativeMapSpaceHom) (hψ.presentationOfBase Px hG)
      (hψ.chartMapHom Px.U Px.toSpace)
      (hψ.presentationOfBase_atlas_comp_relativeMapSpaceHom Px hG hP) D₁ M₁ c₁).hom
    ((representedQuasicoherentSchemeEquivalence B S hS
      (hψ.presentationOfBase Px hG).U).functor.map θU).hom χ

include hc₁ hc₂ in
/-- **Gluing a morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` from the chart `U(ψ)_U`**: a morphism `θ_U` of the
chart pullbacks compatible with the pulled-back transitions is, through the chart identifications
of Lemma K for `r_ψ` and for `ι`, the inverse image along the atlas of a unique morphism. -/
theorem existsUnique_isChartHom
    (hθU : hψ.ChartTransitionsCompatible Px hG hP hQ M₁ τ₁ M₂ τ₂ θU) :
    ∃! χ, hψ.IsChartHom Px hG hP hQ D₁ M₁ c₁ D₂ M₂ c₂ θU χ :=
  RelativeProjPoints.existsUnique_isAtlasMapComp_atlasPullbackChartIso dP dQ Px hP hQ
    (Y := ⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩) (hψ.presentationOfBase Px hG)
    (ObjectProperty.homMk hψ.relativeMapSpaceHom) (hψ.chartMapHom Px.U Px.toSpace)
    (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_atlas_comp_relativeMapSpaceHom Px hG hP)
    (hψ.presentationOfBase_target_comp_chartMapHom_spaceTarget Px hG hP)
    (hψ.chartMapHom_spaceSource_comp_presentationOfBase_source Px hG hP)
    (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι) (hψ.chartIncl Px.U Px.toSpace)
    (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px))
    (hψ.presentationOfBase_atlas_comp_relativeMapSubfunctor_ι Px hG hQ)
    (hψ.presentationOfBase_target_comp_chartIncl_spaceTarget Px hG hQ)
    (hψ.chartIncl_spaceSource_comp_presentationOfBase_source Px hG hQ)
    D₁ M₁ τ₁ c₁ hc₁ D₂ M₂ τ₂ c₂ hc₂ θU hθU

end Glue

section Descended

variable {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)
  (hP : IsAlgebraicSpace B S hS P) (hQ : IsAlgebraicSpace B S hS Q)
  (M₁ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dP.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₁ : quasicoherentPullbackObj B S hS (dP.spaceTarget Px hP) M₁ ⟶
    quasicoherentPullbackObj B S hS (dP.spaceSource Px hP) M₁)
  (hτ₁ : PresentationSchemeCocycle (dP.spacePresentation Px hP) M₁ τ₁)
  (hu₁ : PresentationSchemeUnit (dP.spacePresentation Px hP) M₁ τ₁)
  (M₂ : (SheafOfModules.isQuasicoherent ((BigFppfOver.toScheme B S hS).obj
    (dQ.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory)
  (τ₂ : quasicoherentPullbackObj B S hS (dQ.spaceTarget Px hQ) M₂ ⟶
    quasicoherentPullbackObj B S hS (dQ.spaceSource Px hQ) M₂)
  (hτ₂ : PresentationSchemeCocycle (dQ.spacePresentation Px hQ) M₂ τ₂)
  (hu₂ : PresentationSchemeUnit (dQ.spacePresentation Px hQ) M₂ τ₂)
  (θU : quasicoherentPullbackObj B S hS (hψ.chartMapHom Px.U Px.toSpace) M₁ ⟶
    quasicoherentPullbackObj B S hS (hψ.chartIncl Px.U Px.toSpace) M₂)

/-- **A morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` of the inverse images of descended modules which is `θ_U` on
the chart `U(ψ)_U`**: `𝒟ᵢ` the modules descended from `(Mᵢ, τᵢ)` along the presentations of `P`
and `Q` (Stacks 03M3), with their chart identifications. -/
def IsDescendedChartHom
    (χ : (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩)).obj
          (presentationDescendedModule (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁).obj ⟶
        (modulePullback B S hS (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩)).obj
          (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂).obj) :
    Prop :=
  hψ.IsChartHom Px hG hP hQ
    (presentationDescendedModule (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁).obj M₁
    (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁)
    (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂).obj M₂
    (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂) θU χ

/-- **Gluing a morphism `r_ψ^*𝒟₁ ⟶ ι^*𝒟₂` of the inverse images of descended modules from the
chart `U(ψ)_U`**: a morphism `θ_U` of the chart pullbacks of `M₁` and `M₂` compatible with the
pulled-back transitions is the chart of a unique morphism. -/
theorem existsUnique_isDescendedChartHom
    (hθU : hψ.ChartTransitionsCompatible Px hG hP hQ M₁ τ₁ M₂ τ₂ θU) :
    ∃! χ, hψ.IsDescendedChartHom Px hG hP hQ M₁ τ₁ hτ₁ hu₁ M₂ τ₂ hτ₂ hu₂ θU χ :=
  hψ.existsUnique_isChartHom Px hG hP hQ
    (presentationDescendedModule (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁).obj M₁ τ₁
    (presentationDescendedModuleChartIso (dP.spacePresentation Px hP) M₁ τ₁ hτ₁ hu₁)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent
      (dP.spacePresentation Px hP) τ₁ hτ₁ hu₁)
    (presentationDescendedModule (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂).obj M₂ τ₂
    (presentationDescendedModuleChartIso (dQ.spacePresentation Px hQ) M₂ τ₂ hτ₂ hu₂)
    (presentationDescendedModuleChartIso_comm_spaceBaseDescent
      (dQ.spacePresentation Px hQ) τ₂ hτ₂ hu₂) θU hθU

end Descended

end RelativeProjHomPoints

end AlgebraicGeometry.Space

end
