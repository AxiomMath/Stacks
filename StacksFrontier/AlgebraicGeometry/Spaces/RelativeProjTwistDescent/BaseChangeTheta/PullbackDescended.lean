module

public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.FunctorialityTwist
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Modules
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PresentationPullbackDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta.ProjMap

/-!
# The inverse image of a descended module along a morphism of presentations

For compatible chart data on presentations of two algebraic spaces related by a morphism `h`, the
inverse image `h^*𝒯` of the descended module is the descended module of the pulled-back chart
data (`presentationPullbackDescendedIso`, Stacks 03M3), and the same along a morphism of relative
Projs (`RelativeProjPoints.pullbackAlongDescendedIso`).
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)

namespace AlgebraicGeometry.Space

/-! ### The inverse image of a descended module along a morphism of presentations -/

section PullbackDescendedIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X'' X : AlgebraicSpaces B S hS} (P'' : Presentation B S hS X''.obj X''.property)
  (P : Presentation B S hS X.obj X.property) (h : X'' ⟶ X) (yU : P''.U ⟶ P.U) (yR : P''.R ⟶ P.R)
  (hY : presentationAtlas P'' ≫ h = representedSpaceMap B S hS yU ≫ presentationAtlas P)
  (hta : P''.target ≫ yU = yR ≫ P.target) (hsb : yR ≫ P.source = P''.source ≫ yU)
  (T : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
  (hT : T.obj.IsQuasicoherentOnSite)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (κ : (modulePullback B S hS (presentationAtlas P)).obj T.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
    (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
    (b := (presentationGroupoid P).source)
    (spaceBaseDescent B S hS (presentationGroupoid P) (presentationAtlas P)
      (presentationAtlas_comm P) T.obj)
    (presentationSchemeTransition P M τ) κ.hom)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P''.U).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS P''.target M'' ⟶
    quasicoherentPullbackObj B S hS P''.source M'')
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (hΘ : schemePairTransition B S hS yU yR hta hsb M τ ≫
      quasicoherentPullbackMap B S hS P''.source Θ.hom =
    quasicoherentPullbackMap B S hS P''.target Θ.hom ≫ τ'')
  (hc'' : PresentationSchemeCocycle P'' M'' τ'') (hu'' : PresentationSchemeUnit P'' M'' τ'')


/-- `AlgebraicGeometry.Space.TransitionCommutes` for a morphism equal to one for which it holds. -/
theorem transitionCommutes_of_hom_eq {U V : AlgebraicSpaces B S hS} {a b : V ⟶ U}
    {F G : Modules.{u, u} B S hS U.1 U.2}
    {α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F}
    {β : (modulePullback B S hS a).obj G ⟶ (modulePullback B S hS b).obj G} {f g : F ⟶ G}
    (e : f = g) (hg : TransitionCommutes B S hS α β g) : TransitionCommutes B S hS α β f :=
  e ▸ hg

/-- The identification on the atlas, unfolded into its four steps as isomorphisms. -/
theorem presentationPullbackChartIso_hom_eq_trans_hom :
    (presentationPullbackChartIso P'' P h yU hY T κ Θ).hom =
      (pullbackSquareIso (presentationAtlas P'') (presentationAtlas P) h
          (representedSpaceMap B S hS yU) hY T.obj ≪≫
        (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y :=
            (presentationGroupoid P).objects)
          (representedSpaceMap B S hS yU)).mapIso κ ≪≫
          modulePullbackRepresentedQuasicoherentIso B S hS yU M ≪≫
            (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
                P''.U).functor.mapIso Θ)).hom :=
  rfl

/-- The four steps of the identification on the atlas, composed as morphisms. -/
theorem presentationPullbackChartIso_trans_hom_eq_comp :
    (pullbackSquareIso (presentationAtlas P'') (presentationAtlas P) h
        (representedSpaceMap B S hS yU) hY T.obj ≪≫
      (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y :=
          (presentationGroupoid P).objects)
        (representedSpaceMap B S hS yU)).mapIso κ ≪≫
        modulePullbackRepresentedQuasicoherentIso B S hS yU M ≪≫
          (ObjectProperty.ι _).mapIso ((representedQuasicoherentSchemeEquivalence B S hS
              P''.U).functor.mapIso Θ)).hom =
      pullbackSquareHom (presentationAtlas P'') (presentationAtlas P) h
          (representedSpaceMap B S hS yU) hY T.obj ≫
        (modulePullback B S hS (X := (presentationGroupoid P'').objects) (Y :=
            (presentationGroupoid P).objects)
          (representedSpaceMap B S hS yU)).map κ.hom ≫
          (modulePullbackRepresentedQuasicoherentIso B S hS yU M).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS P''.U).functor.map Θ.hom).hom :=
  (Iso.trans_hom _ _).trans (congrArg (_ ≫ ·) ((Iso.trans_hom _ _).trans
    (congrArg (_ ≫ ·) (Iso.trans_hom _ _))))

include hκ hΘ in
/-- **The identification on the atlas, as an isomorphism, carries the canonical transition of
`c''^*(h^*𝒯)` to `τ''^a`.** -/
theorem transitionCommutes_presentationPullbackChartIso :
    TransitionCommutes B S hS (U := (presentationGroupoid P'').objects)
      (V := (presentationGroupoid P'').arrows) (a := (presentationGroupoid P'').target)
      (b := (presentationGroupoid P'').source)
      (spaceBaseDescent B S hS (presentationGroupoid P'') (presentationAtlas P'')
        (presentationAtlas_comm P'') ((modulePullback B S hS h).obj T.obj))
      (presentationSchemeTransition P'' M'' τ'')
      (presentationPullbackChartIso P'' P h yU hY T κ Θ).hom :=
  transitionCommutes_of_hom_eq
    ((presentationPullbackChartIso_hom_eq_trans_hom P'' P h yU hY T κ Θ).trans
      (presentationPullbackChartIso_trans_hom_eq_comp P'' P h yU hY T κ Θ))
    (transitionCommutes_presentationPullbackChartHom P'' P h yU yR hY hta hsb T τ κ hκ τ'' Θ hΘ)

include hκ hΘ in
/-- **The inverse image of a descended module along a morphism of presentations** (Stacks 03M3):
for chart data `(M, τ)` of `𝒯` on a presentation of `X`, compatible chart data `(M'', τ'')` on a
presentation of `X''` and an identification `Θ : yU^*M ≅ M''` carrying the pulled-back
transition to `τ''`, the inverse image `h^*𝒯` is the descended module `D(M'')`. -/
def presentationPullbackDescendedIso :
    (⟨(modulePullback B S hS h).obj T.obj,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS h _ hT⟩ :
        QuasicoherentSheaves.{u, u} B S hS X''.obj X''.property) ≅
      presentationDescendedModule P'' M'' τ'' hc'' hu'' :=
  presentationDescendedIso P'' τ'' hc'' hu''
    ⟨(modulePullback B S hS h).obj T.obj,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS h _ hT⟩
    (presentationPullbackChartIso P'' P h yU hY T κ Θ)
    (transitionCommutes_presentationPullbackChartIso P'' P h yU yR hY hta hsb T τ κ hκ τ'' Θ hΘ)

include hκ hΘ in
/-- **The inverse image along the atlas of `h^*𝒯 ≅ D(M'')` is the identification on the atlas**,
through the chart identification of `D(M'')`. -/
theorem presentationPullbackDescendedIso_spec :
    (modulePullback B S hS (presentationAtlas P'')).map
        (presentationPullbackDescendedIso P'' P h yU yR hY hta hsb T hT τ κ hκ τ'' Θ hΘ hc''
          hu'').hom.hom ≫
      (presentationDescendedModuleChartIso P'' M'' τ'' hc'' hu'').hom =
    (presentationPullbackChartIso P'' P h yU hY T κ Θ).hom :=
  presentationDescendedIso_spec P'' τ'' hc'' hu'' _ _ _

end PullbackDescendedIso

/-! ### The inverse image of a descended module along a morphism of relative Projs -/

namespace RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section PullbackAlong

variable {XA XA' : AlgebraicSpaces B S hS} {PA PA' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {πA : PA ⟶ XA.obj} {πA' : PA' ⟶ XA'.obj} {dA : RelativeProjPoints B S hS πA}
  {dA' : RelativeProjPoints B S hS πA'} {hA : PA' ⟶ PA}
  (Px : Presentation B S hS XA.obj XA.property)
  (Px' : Presentation B S hS XA'.obj XA'.property) (hP : IsAlgebraicSpace B S hS PA)
  (hP' : IsAlgebraicSpace B S hS PA') {ℓ : Px'.U ⟶ Px.U} {ℓR : Px'.R ⟶ Px.R}
  (hℓt : ℓR ≫ Px.target = Px'.target ≫ ℓ) (hℓs : ℓR ≫ Px.source = Px'.source ≫ ℓ)
  (yU : dA'.fibre Px'.U Px'.toSpace ⟶ dA.fibre Px.U Px.toSpace)
  (hyU : dA'.LiesOverAlong dA hA yU ℓ)
  (yR : dA'.fibre Px'.R (relationPoint Px') ⟶ dA.fibre Px.R (relationPoint Px))
  (hyR : dA'.LiesOverAlong dA hA yR ℓR)

include hℓt hyU hyR in
/-- Given compatible lifts `yU` and `yR` of `ℓ` and `ℓR` along `hA`, the target maps of the
space presentations of `dA'` and `dA` commute with `yU` and `yR`. -/
theorem spacePresentation_target_comp_of_liesOverAlong :
    dA'.spaceTarget Px' hP' ≫ yU = yR ≫ dA.spaceTarget Px hP :=
  (LiesOverAlong.comp_eq_comp hyR (dA.liesOver_spaceTarget Px hP)
    (dA'.liesOver_spaceTarget Px' hP') hyU hℓt).symm

include hℓs hyU hyR in
/-- Given compatible lifts `yU` and `yR` of `ℓ` and `ℓR` along `hA`, the source maps of the
space presentations of `dA'` and `dA` commute with `yU` and `yR`. -/
theorem comp_spacePresentation_source_of_liesOverAlong :
    yR ≫ dA.spaceSource Px hP = dA'.spaceSource Px' hP' ≫ yU :=
  LiesOverAlong.comp_eq_comp hyR (dA.liesOver_spaceSource Px hP)
    (dA'.liesOver_spaceSource Px' hP') hyU hℓs

include hyU in
/-- The atlas of the space presentation of `dA'` followed by `hA` equals the map induced by `yU`
followed by the atlas of the space presentation of `dA`. -/
theorem presentationAtlas_comp_homMk_of_liesOverAlong :
    presentationAtlas (dA'.spacePresentation Px' hP') ≫
        (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩) =
      representedSpaceMap B S hS yU ≫ presentationAtlas (dA.spacePresentation Px hP) :=
  ObjectProperty.hom_ext _ hyU.2.symm

variable (T : QuasicoherentSheaves.{u, u} B S hS PA hP)
  (hT : T.obj.IsQuasicoherentOnSite)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS (dA.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (dA.spaceSource Px hP) M)
  (κ : (modulePullback B S hS (presentationAtlas (dA.spacePresentation Px hP))).obj T.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dA.fibre Px.U Px.toSpace)).functor.obj
      M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
    (V := (presentationGroupoid (dA.spacePresentation Px hP)).arrows)
    (a := (presentationGroupoid (dA.spacePresentation Px hP)).target)
    (b := (presentationGroupoid (dA.spacePresentation Px hP)).source)
    (spaceBaseDescent B S hS (presentationGroupoid (dA.spacePresentation Px hP))
      (presentationAtlas (dA.spacePresentation Px hP))
      (presentationAtlas_comm (dA.spacePresentation Px hP)) T.obj)
    (presentationSchemeTransition (dA.spacePresentation Px hP) M τ) κ.hom)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA'.fibre Px'.U Px'.toSpace)).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS (dA'.spaceTarget Px' hP') M'' ⟶
    quasicoherentPullbackObj B S hS (dA'.spaceSource Px' hP') M'')
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')

/-- **The identification `Θ : y^*M ≅ M''` carries the pulled-back transition of `M` to the
transition `τ''` of `M''`**, for a morphism `y : U' ×_{X'} P' ⟶ U ×_X P` lying over `ℓ` and `h`
and the morphism of the relation schemes lying over `ℓR` and `h`. -/
structure PullbackTransitionCompatible : Prop where
  /-- The square of transitions commutes. -/
  eq : schemePairTransition B S hS yU yR
        (spacePresentation_target_comp_of_liesOverAlong Px Px' hP hP' hℓt yU hyU yR hyR)
        (comp_spacePresentation_source_of_liesOverAlong Px Px' hP hP' hℓs yU hyU yR hyR) M τ ≫
        quasicoherentPullbackMap B S hS (dA'.spaceSource Px' hP') Θ.hom =
      quasicoherentPullbackMap B S hS (dA'.spaceTarget Px' hP') Θ.hom ≫ τ''

variable (hΘ : PullbackTransitionCompatible Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ τ'' Θ)
  (hc'' : PresentationSchemeCocycle (dA'.spacePresentation Px' hP') M'' τ'')
  (hu'' : PresentationSchemeUnit (dA'.spacePresentation Px' hP') M'' τ'')

include hκ hΘ in
/-- **The inverse image of a descended module along a morphism of relative Projs lying over
compatible presentations** (Stacks 03M3): for chart data `(M, τ)` of `𝒯` on `U ×_X P`, chart data
`(M'', τ'')` on `U' ×_{X'} P'` and an identification `Θ : y^*M ≅ M''` along a morphism
`y : U' ×_{X'} P' ⟶ U ×_X P` lying over `ℓ` and `h`, carrying the pulled-back transition to
`τ''`, the inverse image `h^*𝒯` is the descended module `D(M'')`. -/
def pullbackAlongDescendedIso :
    (⟨(modulePullback B S hS
        (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)).obj T.obj,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hT⟩ :
        QuasicoherentSheaves.{u, u} B S hS PA' hP') ≅
      presentationDescendedModule (dA'.spacePresentation Px' hP') M'' τ'' hc'' hu'' :=
  presentationPullbackDescendedIso (dA'.spacePresentation Px' hP') (dA.spacePresentation Px hP)
    (ObjectProperty.homMk hA) yU yR
    (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
    (spacePresentation_target_comp_of_liesOverAlong Px Px' hP hP' hℓt yU hyU yR hyR)
    (comp_spacePresentation_source_of_liesOverAlong Px Px' hP hP' hℓs yU hyU yR hyR)
    T hT τ κ hκ τ'' Θ hΘ.eq hc'' hu''

include hκ hΘ in
/-- The inverse image along the atlas of `pullbackAlongDescendedIso` is the identification on the
atlas. -/
theorem pullbackAlongDescendedIso_spec :
    (modulePullback B S hS (presentationAtlas (dA'.spacePresentation Px' hP'))).map
        (pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR T hT τ κ hκ τ'' Θ hΘ hc''
          hu'').hom.hom ≫
      (presentationDescendedModuleChartIso (dA'.spacePresentation Px' hP') M'' τ'' hc'' hu'').hom =
    (presentationPullbackChartIso (dA'.spacePresentation Px' hP') (dA.spacePresentation Px hP)
      (ObjectProperty.homMk hA) yU
      (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
      T κ Θ).hom :=
  presentationPullbackDescendedIso_spec (dA'.spacePresentation Px' hP')
    (dA.spacePresentation Px hP) (ObjectProperty.homMk hA) yU yR _ _ _
    T hT τ κ hκ τ'' Θ hΘ.eq hc'' hu''

include hκ hΘ in
/-- `pullbackAlongDescendedIso_spec` for an isomorphism equal to `pullbackAlongDescendedIso`. -/
theorem pullbackAlongDescendedIso_spec_of_eq
    (e : (⟨(modulePullback B S hS
        (ObjectProperty.homMk hA : (⟨PA', hP'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨PA, hP⟩)).obj T.obj,
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ hT⟩ :
        QuasicoherentSheaves.{u, u} B S hS PA' hP') ≅
      presentationDescendedModule (dA'.spacePresentation Px' hP') M'' τ'' hc'' hu'')
    (he : e = pullbackAlongDescendedIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR T hT τ κ hκ τ'' Θ hΘ
      hc'' hu'') :
    (modulePullback B S hS (presentationAtlas (dA'.spacePresentation Px' hP'))).map e.hom.hom ≫
      (presentationDescendedModuleChartIso (dA'.spacePresentation Px' hP') M'' τ'' hc'' hu'').hom =
    (presentationPullbackChartIso (dA'.spacePresentation Px' hP') (dA.spacePresentation Px hP)
      (ObjectProperty.homMk hA) yU
      (presentationAtlas_comp_homMk_of_liesOverAlong Px Px' hP hP' yU hyU)
      T κ Θ).hom := by
  subst he
  exact pullbackAlongDescendedIso_spec Px Px' hP hP' hℓt hℓs yU hyU yR hyR T hT τ κ hκ τ'' Θ hΘ
    hc'' hu''


end PullbackAlong

end RelativeProjPoints

end AlgebraicGeometry.Space

end
