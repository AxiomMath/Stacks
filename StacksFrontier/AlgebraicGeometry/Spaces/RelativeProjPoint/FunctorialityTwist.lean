module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.Functoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules

/-!
# The twists of `P` and `Q` on the charts of `U(ψ)`

Let `ψ : 𝒜₁ ⟶ 𝒜₂` be a map of quasi-coherent graded algebras on an algebraic space `X`, with
`P = Proj_X(𝒜₁)`, `Q = Proj_X(𝒜₂)`, `r_ψ : U(ψ) ⟶ P` and `ι : U(ψ) ⟶ Q` of Stacks 085F, and
`X = U/R` an étale presentation.  On the chart `U(ψ)_U` of the presentation of `U(ψ)` restricted
from `Q = Q_U/Q_R`, the inverse images `r_ψ^*𝒪_P(n)` and `ι^*𝒪_Q(n)` are the inverse images of the
twists `𝒪(n)` of Stacks 01NR along the charts of `r_ψ` and of `ι`, and these identifications carry
the canonical descent data of `r_ψ^*𝒪_P(n)` and `ι^*𝒪_Q(n)` to the pullbacks of the transitions of
the twists along the morphisms of relations.

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.chartTwistIso`: for `f : Y ⟶ P` and a presentation
  of `Y` whose atlas lies over the chart `P_U ⟶ P`, the identification of the inverse image of
  `f^*𝒪_P(n)` along the atlas with the module attached to the inverse image of the twist.

## Main results

* `RelativeProjSituation.twistModuleChartIso_comm_spaceBaseDescent`: the chart identification of
  `𝒪_P(n)` carries the canonical transition morphism of Stacks 03M3 to the transition of the
  twists.
* `RelativeProjSituation.relativeMapPresentation_atlas_comp_relativeMapSpaceMor`
  and `…_relativeMapSpaceι`: the charts of `r_ψ` and `ι` over the atlas of `U(ψ)`.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

/-! ### The atlas of the presentation of `U(ψ)` over the charts of `P` and `Q` -/

namespace AlgebraicGeometry.Space.RelativeProjHomPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X.obj}
  {πQ : Q ⟶ X.obj} {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ) (Px : Presentation B S hS X.obj X.property)
  (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)

/-- The atlas of `presentationOfBase` lies over `r_ψ` along the chart of `r_ψ`. -/
theorem presentationOfBase_atlas_comp_relativeMapSpaceHom (hP : IsAlgebraicSpace B S hS P) :
    (hψ.presentationOfBase Px hG).atlas ≫
        (ObjectProperty.homMk hψ.relativeMapSpaceHom :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨P, hP⟩) =
      representedSpaceMap B S hS (T' := (hψ.presentationOfBase Px hG).U)
          (T := dP.fibre Px.U Px.toSpace) (hψ.chartMapHom Px.U Px.toSpace) ≫
        presentationAtlas (dP.spacePresentation Px hP) :=
  ObjectProperty.hom_ext _ (hψ.yoneda_map_chartMapHom_fibreToSpace Px.U Px.toSpace).symm

/-- The atlas of `presentationOfBase` lies over the inclusion `U(ψ) ⟶ Q` along the inclusion of
the chart. -/
theorem presentationOfBase_atlas_comp_relativeMapSubfunctor_ι (hQ : IsAlgebraicSpace B S hS Q) :
    (hψ.presentationOfBase Px hG).atlas ≫
        (ObjectProperty.homMk hψ.relativeMapSubfunctor.ι :
          (⟨hψ.relativeMapSubfunctor.toFunctor, hG⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Q, hQ⟩) =
      representedSpaceMap B S hS (T' := (hψ.presentationOfBase Px hG).U)
          (T := dQ.fibre Px.U Px.toSpace) (hψ.chartIncl Px.U Px.toSpace) ≫
        presentationAtlas (dQ.spacePresentation Px hQ) :=
  ObjectProperty.hom_ext _ (hψ.chartToSubfunctor_ι Px.U Px.toSpace)

end AlgebraicGeometry.Space.RelativeProjHomPoints

/-! ### Lemma K at the presentation of a relative Proj, at a variable family of points -/

namespace AlgebraicGeometry.Space.RelativeProjPoints

open QuasiCoherentDescent

section ChartPullback

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
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
  (c : (modulePullback B S hS
      (X := ⟨yoneda.obj (d.fibre Px.U Px.toSpace), isAlgebraicSpace_yoneda B S hS _⟩)
      (presentationAtlas (d.spacePresentation Px hP))).obj D ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (d.fibre Px.U Px.toSpace)).functor.obj
      M).obj)

/-- A transition carried on the groupoid of the presentation of `P`, read along the projections of
the relation as represented morphisms. -/
theorem transitionCommutes_represented_of_presentationGroupoid (hcomm : TransitionCommutes B S hS
      (U := (presentationGroupoid (d.spacePresentation Px hP)).objects)
      (V := (presentationGroupoid (d.spacePresentation Px hP)).arrows)
      (a := (presentationGroupoid (d.spacePresentation Px hP)).target)
      (b := (presentationGroupoid (d.spacePresentation Px hP)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (d.spacePresentation Px hP))
        (presentationAtlas (d.spacePresentation Px hP)) (presentationAtlas_comm _) D)
      (presentationSchemeTransition (d.spacePresentation Px hP) M τ) c.hom) :
    TransitionCommutes B S hS
      (U := (presentationGroupoid (d.spacePresentation Px hP)).objects)
      (a := representedSpaceMap B S hS (d.spaceTarget Px hP))
      (b := representedSpaceMap B S hS (d.spaceSource Px hP))
      (spaceBaseDescent B S hS (presentationGroupoid (d.spacePresentation Px hP))
        (presentationAtlas (d.spacePresentation Px hP)) (presentationAtlas_comm _) D)
      (representedSchemeTransition B S hS (d.spaceTarget Px hP) (d.spaceSource Px hP) M τ) c.hom :=
  hcomm

/-- The canonical comparison along the two composites of a morphism into the relation of `P`, the
projections written as represented morphisms, is the reindexing of the canonical transition
morphism of Stacks 03M3. -/
theorem canonicalComparison_hom_eq_reindex_spaceBaseDescent_represented :
    (canonicalComparison
        (representedSpaceMap B S hS fR ≫ representedSpaceMap B S hS (d.spaceTarget Px hP))
        (representedSpaceMap B S hS fR ≫ representedSpaceMap B S hS (d.spaceSource Px hP))
        (presentationAtlas (d.spacePresentation Px hP))
        (presentationAtlas (d.spacePresentation Px hP))
        (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (presentationAtlas_comm _))).trans
          (Category.assoc _ _ _).symm) D).hom =
      modulePullbackReindex (representedSpaceMap B S hS fR)
        (spaceBaseDescent B S hS (presentationGroupoid (d.spacePresentation Px hP))
          (presentationAtlas (d.spacePresentation Px hP)) (presentationAtlas_comm _) D) :=
  canonicalComparison_hom_eq_reindex_spaceBaseDescent B S hS
      (presentationGroupoid (d.spacePresentation Px hP))
      (presentationAtlas (d.spacePresentation Px hP)) (presentationAtlas_comm _) D
      (representedSpaceMap B S hS fR) _

include hs ht in
/-- **Lemma K at the presentation `P = P_U/P_R` of a relative Proj.**  For `f : Y ⟶ P` and a
presentation `Y = U'/R'` lying over `P_U/P_R` along `fU`, `fR`, a chart identification `c` of `D`
carrying the canonical descent datum to the transition attached to `τ` gives the chart
identification `φ'^*f^*D ≅ fU^*φ^*D ≅ fU^*C ≅ (fU^*M)^a` carrying the canonical descent datum of
`f^*D` to the transition attached to the pullback of `τ`. -/
theorem transitionCommutes_chartPullback
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
      ((canonicalComparison (P := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS _⟩) P'.atlas
          (representedSpaceMap B S hS fU) f
          (presentationAtlas (d.spacePresentation Px hP)) hsq D).hom ≫
        (modulePullback B S hS (representedSpaceMap B S hS fU)).map c.hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS fU M).hom) := by
  have K := transitionCommutes_canonicalComparison_of_square
    (X := ⟨P, hP⟩) (Y := Y)
    (U := ⟨yoneda.obj (d.fibre Px.U Px.toSpace), isAlgebraicSpace_yoneda B S hS _⟩)
    (U' := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda B S hS _⟩)
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
  exact K

end ChartPullback

end AlgebraicGeometry.Space.RelativeProjPoints

namespace AlgebraicGeometry.Space.RelativeProjSituation

open QuasiCoherentDescent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
  {𝒜₁ 𝒜₂ : SheafOfModules.GradedAlgebra.{u, m, u, u + 1} (structureRingSheaf B S hS X)}
  (h₁c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₁.piece i).val.obj U)
    (b : (𝒜₁.piece j).val.obj U), HEq ((𝒜₁.mul i j).app U a b) ((𝒜₁.mul j i).app U b a))
  (h₁n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₁.piece n))
  (h₁q : ∀ n : ℤ, (𝒜₁.piece n).IsQuasicoherentOnSite)
  (h₁k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₁.piece n).val.obj U) B.cutoff)
  (h₂c : ∀ (i j : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ) (a : (𝒜₂.piece i).val.obj U)
    (b : (𝒜₂.piece j).val.obj U), HEq ((𝒜₂.mul i j).app U a b) ((𝒜₂.mul j i).app U b a))
  (h₂n : ∀ n : ℤ, n < 0 → Limits.IsZero (𝒜₂.piece n))
  (h₂q : ∀ n : ℤ, (𝒜₂.piece n).IsQuasicoherentOnSite)
  (h₂k : ∀ (n : ℤ) (U : (SmallEtale B S hS X.1)ᵒᵖ),
    HasCardinalLT ↥((𝒜₂.piece n).val.obj U) B.cutoff)
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom 𝒜₁ 𝒜₂)
  (Px : Presentation B S hS X.1 X.2)

local notation "𝔰₁" => RelativeProjSituation.mk B S hS X 𝒜₁ h₁c h₁n h₁q h₁k
local notation "𝔰₂" => RelativeProjSituation.mk B S hS X 𝒜₂ h₂c h₂n h₂q h₂k
local notation "𝔥" => homPoints h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ
local notation "𝒫₁" => RelativeProjPoints.spacePresentation (relativeProjPoints 𝔰₁) Px
  (isAlgebraicSpace_relativeProjFunctor 𝔰₁)
local notation "𝒫₂" => RelativeProjPoints.spacePresentation (relativeProjPoints 𝔰₂) Px
  (isAlgebraicSpace_relativeProjFunctor 𝔰₂)
local notation "𝒫" => relativeMapPresentation h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ Px

/-! ### The chart identification of an inverse image of a twist -/

section Chart

variable (s : RelativeProjSituation.{u, m})
  (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property) (n : ℤ)
  {Y : AlgebraicSpaces s.site s.base s.containsBase}
  (f : Y ⟶ ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩)
  (P' : Presentation s.site s.base s.containsBase Y.1 Y.2)
  (fU : P'.U ⟶ s.relativeProjPoints.fibre Px.U Px.toSpace)
  (fR : P'.R ⟶ s.relativeProjPoints.fibre Px.R (RelativeProjPoints.relationPoint Px))
  (hsq : P'.atlas ≫ f = representedSpaceMap s.site s.base s.containsBase fU ≫
    presentationAtlas (s.relativeProjPoints.spacePresentation Px
      s.isAlgebraicSpace_relativeProjFunctor))
  (ht : P'.target ≫ fU = fR ≫ s.relativeProjPoints.presentationTarget Px)
  (hs : fR ≫ s.relativeProjPoints.presentationSource Px = P'.source ≫ fU)

/-- The target projection of the presentation of `P`, spelled through the presentation. -/
theorem spaceTarget_eq_presentationTarget :
    s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor =
      s.relativeProjPoints.presentationTarget Px :=
  s.relativeProjPoints.presentation_target Px s.isAlgebraicSpace_relativeProjFunctor

/-- The source projection of the presentation of `P`, spelled through the presentation. -/
theorem spaceSource_eq_presentationSource :
    s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor =
      s.relativeProjPoints.presentationSource Px :=
  s.relativeProjPoints.presentation_source Px s.isAlgebraicSpace_relativeProjFunctor

include ht in
/-- The square of the target projections, spelled through the presentation of `P`. -/
theorem comp_spaceTarget_of_comp_eq :
    P'.target ≫ fU =
      fR ≫ s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor :=
  ht.trans (congrArg (fR ≫ ·) (spaceTarget_eq_presentationTarget s Px).symm)

include hs in
/-- The square of the source projections, spelled through the presentation of `P`. -/
theorem spaceSource_comp_eq_of_comp_eq :
    fR ≫ s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor =
      P'.source ≫ fU :=
  (congrArg (fR ≫ ·) (spaceSource_eq_presentationSource s Px)).trans hs

omit fU fR hsq ht hs in
/-- The chart identification of `𝒪_P(n)` carries the canonical transition morphism of Stacks 03M3
to the transition of the twists. -/
theorem twistModuleChartIso_comm_spaceBaseDescent :
    TransitionCommutes s.site s.base s.containsBase
      (U := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).objects)
      (V := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).arrows)
      (a := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).target)
      (b := (presentationGroupoid (s.relativeProjPoints.spacePresentation Px
        s.isAlgebraicSpace_relativeProjFunctor)).source)
      (spaceBaseDescent s.site s.base s.containsBase
        (presentationGroupoid
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
        (presentationAtlas
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor))
        (presentationAtlas_comm _) (s.twistModule Px n).obj)
      (presentationSchemeTransition
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n))
      (s.twistModuleChartIso Px n).hom := by
  have h := s.twistModuleChartIso_comm Px n
  rwa [presentationQuasicoherentEquivalence_functor_obj_alpha] at h

include ht hs in
/-- **The chart identification of `f^*𝒪_P(n)` carries its canonical descent datum to the pullback
of the transition of the twists along the morphism of relations.** -/
theorem transitionCommutes_chartTwistIso :
    TransitionCommutes s.site s.base s.containsBase
      (canonicalComparison (representedSpaceMap s.site s.base s.containsBase P'.target)
        (representedSpaceMap s.site s.base s.containsBase P'.source) P'.atlas P'.atlas
        P'.relationTarget_comp_atlas
        ((modulePullback s.site s.base s.containsBase f).obj (s.twistModule Px n).obj)).hom
      (representedSchemeTransition s.site s.base s.containsBase P'.target P'.source
        (quasicoherentPullbackObj s.site s.base s.containsBase fU
          (s.twistPieceQcoh Px.U Px.toSpace n))
        (schemeTransitionPullback s.site s.base s.containsBase
          (s.relativeProjPoints.spaceTarget Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.relativeProjPoints.spaceSource Px s.isAlgebraicSpace_relativeProjFunctor)
          P'.target P'.source fU fR (comp_spaceTarget_of_comp_eq s Px P' fU fR ht)
          (spaceSource_comp_eq_of_comp_eq s Px P' fU fR hs)
          (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)))
      ((canonicalComparison
          (P := ⟨yoneda.obj P'.U, isAlgebraicSpace_yoneda s.site s.base s.containsBase _⟩)
          P'.atlas (representedSpaceMap s.site s.base s.containsBase fU) f
          (presentationAtlas (s.relativeProjPoints.spacePresentation Px
            s.isAlgebraicSpace_relativeProjFunctor)) hsq (s.twistModule Px n).obj).hom ≫
        (modulePullback s.site s.base s.containsBase
          (representedSpaceMap s.site s.base s.containsBase fU)).map
            (s.twistModuleChartIso Px n).hom ≫
        (modulePullbackRepresentedQuasicoherentIso s.site s.base s.containsBase fU
          (s.twistPieceQcoh Px.U Px.toSpace n)).hom) :=
  RelativeProjPoints.transitionCommutes_chartPullback s.relativeProjPoints Px
    s.isAlgebraicSpace_relativeProjFunctor f P' fU fR hsq
    (comp_spaceTarget_of_comp_eq s Px P' fU fR ht)
    (spaceSource_comp_eq_of_comp_eq s Px P' fU fR hs) (s.twistModule Px n).obj
    (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n) (s.twistModuleChartIso Px n)
    (twistModuleChartIso_comm_spaceBaseDescent s Px n)

end Chart

/-! ### The squares of the charts of `r_ψ` and `ι` -/

/-- The chart of `r_ψ` over `U` lies over `r_ψ`. -/
theorem relativeMapPresentation_atlas_comp_relativeMapSpaceMor :
    (𝒫).atlas ≫ relativeMapSpaceMor h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ =
      representedSpaceMap B S hS ((𝔥).chartMapHom Px.U Px.toSpace) ≫ presentationAtlas 𝒫₁ :=
  ObjectProperty.hom_ext _ ((𝔥).yoneda_map_chartMapHom_fibreToSpace Px.U Px.toSpace).symm

/-- The chart of `ι` over `U` lies over `ι`. -/
theorem relativeMapPresentation_atlas_comp_relativeMapSpaceι :
    (𝒫).atlas ≫ relativeMapSpaceι h₁c h₁n h₁q h₁k h₂c h₂n h₂q h₂k ψ =
      representedSpaceMap B S hS ((𝔥).chartIncl Px.U Px.toSpace) ≫ presentationAtlas 𝒫₂ :=
  ObjectProperty.hom_ext _ ((𝔥).chartToSubfunctor_ι Px.U Px.toSpace)

end AlgebraicGeometry.Space.RelativeProjSituation

end
