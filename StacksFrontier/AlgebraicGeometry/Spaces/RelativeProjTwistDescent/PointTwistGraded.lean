module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PullbackChartMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraMul
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.TwistAlgebraUnit

/-!
# The base change identification of `𝒪_P(n)` to a scheme point, and its compatibility with the
multiplications

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`𝒪_P(n)` the twists of Stacks 084D.  For every scheme point `f : T ⟶ X`, the inverse image of
`𝒪_P(n)` along `T ×_X P ⟶ P` is the twist `𝒪(n)` of Stacks 01NR on `T ×_X P = Proj_T(f^*𝒜)`
(`…RelativeProjSituation.exists_fibreToSpace_twistModule_iso`).  This file makes that
identification a definition, `…RelativeProjSituation.fibreToSpaceTwistModuleIso`, characterized by
its description on the étale cover `T_U ×_T P' ⟶ T ×_X P`, and proves the scheme-level and
chart-level inputs of its compatibility with the multiplications and units of the graded
algebras of Stacks 084D and Stacks 01NR: the comparisons of twists of Tag 01O3 along morphisms of
base changes are multiplicative and unital, and so are their readings on the attached modules.

## Main definitions

* `AlgebraicGeometry.Space.modulePullbackIsoOfOfIsoYoneda`: the isomorphism `h^*𝒯 ≅ N^a` on a
  representable algebraic space descended from identifications on a presentation (Stacks 03M3).
* `AlgebraicGeometry.Space.RelativeProjPoints.pullbackTransitionCompatibleIso`: the same along a
  morphism from a representable base change of relative Projs.
* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso`: **the base change
  identification `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of Stacks 084D in degree `n`**.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso_spec` and
  `…eq_fibreToSpaceTwistModuleIso`: the description of the identification on the étale cover, and
  its uniqueness.
* `AlgebraicGeometry.Space.RelativeProjSituation.baseChangeTwistPieceComparison_mul` and
  `…baseChangeTwistPieceComparison_unit`: the comparisons of twists along a morphism of base
  changes (Tag 01O3) carry the multiplication and the unit to the multiplication and the unit.
* `…RelativeProjSituation.modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison`: the
  same for the attached multiplications on represented algebraic spaces, through Stacks 03DX (2).

## Implementation notes

The definitions are explicit constructions at free variables, instantiated once; their
descriptions on the atlas are proved by unfolding the definition and applying the lemma with all
arguments left to unification.  Proofs passed to the concrete definition are named theorems
whose arguments are the section variables, so that no auxiliary lemma is abstracted from the
body.  The twist is passed as the descended module it is by definition.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory MonoidalCategory AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp

namespace AlgebraicGeometry.Space

/-- An equation `f ≫ g ≫ h = p ≫ q` transported along equations of its five morphisms, so that
an instance compares two spellings morphism by morphism. -/
private theorem comp_comp_eq_comp_of_eqs {C : Type*} [Category C] {X₁ X₂ X₃ X₄ Y₁ : C}
    {f f' : X₁ ⟶ X₂} {g g' : X₂ ⟶ X₃} {h h' : X₃ ⟶ X₄} {p p' : X₁ ⟶ Y₁} {q q' : Y₁ ⟶ X₄}
    (hf : f' = f) (hg : g' = g) (hh : h' = h) (hp : p' = p) (hq : q' = q)
    (H : f ≫ g ≫ h = p ≫ q) : f' ≫ g' ≫ h' = p' ≫ q' := by
  subst hf hg hh hp hq
  exact H

/-- The image under an uncurried bifunctor of a pair of morphisms depends only on the two
morphisms. -/
private theorem uncurry_map_pair_congr {C D : Type*} [Category C] [Category D] (F : C ⥤ C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} {a a' : X₁ ⟶ Y₁} {b b' : X₂ ⟶ Y₂} (ha : a = a') (hb : b = b') :
    (Functor.uncurry.obj F).map ((a, b) : (X₁, X₂) ⟶ (Y₁, Y₂)) =
      (Functor.uncurry.obj F).map ((a', b') : (X₁, X₂) ⟶ (Y₁, Y₂)) := by
  subst ha hb
  rfl

/-! ### The identification of a descended module along a representable algebraic space -/

section OfIsoYonedaIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P0 : Presentation B S hS F hF) {W : BigFppfOver B S hS} (e : F ≅ yoneda.obj W)
  (c : P0.U ⟶ W) (hc : yoneda.map c = P0.toSpace ≫ e.hom)

variable (N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P0.U).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS P0.target M'' ⟶
    quasicoherentPullbackObj B S hS P0.source M'')
  (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
  (hΘB : canonicalSchemeTransition B S hS P0.target P0.source c
      (P0.target_comp_eq_source_comp_of_iso e c hc) N ≫
      quasicoherentPullbackMap B S hS P0.source ΘB.hom =
    quasicoherentPullbackMap B S hS P0.target ΘB.hom ≫ τ'')

variable {XA : AlgebraicSpaces B S hS} (Pb : Presentation B S hS XA.obj XA.property)
  (hA : representedAlgebraicSpace B S hS W ⟶ XA) (yU : P0.U ⟶ Pb.U) (yR : P0.R ⟶ Pb.R)
  (hY : presentationAtlas (P0.ofIsoYoneda e c hc) ≫ hA =
    representedSpaceMap B S hS yU ≫ presentationAtlas Pb)
  (hta : P0.target ≫ yU = yR ≫ Pb.target) (hsb : yR ≫ Pb.source = P0.source ≫ yU)
  (Tm : QuasicoherentSheaves.{u, u} B S hS XA.obj XA.property)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj Pb.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS Pb.target M ⟶ quasicoherentPullbackObj B S hS Pb.source M)
  (κ : (modulePullback B S hS (presentationAtlas Pb)).obj Tm.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS Pb.U).functor.obj M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid Pb).objects)
    (V := (presentationGroupoid Pb).arrows) (a := (presentationGroupoid Pb).target)
    (b := (presentationGroupoid Pb).source)
    (spaceBaseDescent B S hS (presentationGroupoid Pb) (presentationAtlas Pb)
      (presentationAtlas_comm Pb) Tm.obj)
    (presentationSchemeTransition Pb M τ) κ.hom)
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (hΘ : schemePairTransition B S hS yU yR hta hsb M τ ≫
      quasicoherentPullbackMap B S hS P0.source Θ.hom =
    quasicoherentPullbackMap B S hS P0.target Θ.hom ≫ τ'')


/-- **The inverse image of a descended module on a representable algebraic space** (Stacks 03M3),
as an isomorphism `h^*𝒯 ≅ N^a`: the isomorphism of
`AlgebraicGeometry.Space.exists_modulePullback_iso_of_ofIsoYoneda`, descended from the two
identifications on the presentation of `W`. -/
def modulePullbackIsoOfOfIsoYoneda :
    (modulePullback B S hS hA).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj :=
  (ObjectProperty.ι _).mapIso
      (presentationIsoOfChartIsos (P0.ofIsoYoneda e c hc) τ''
        ⟨(modulePullback B S hS hA).obj Tm.obj,
          isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ Tm.property⟩
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N)
        (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ)
        (transitionCommutes_presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU yR hY
          hta hsb Tm τ κ hκ τ'' Θ hΘ)
        (ofIsoYonedaChartIso P0 e c hc N ΘB)
        (transitionCommutes_ofIsoYonedaChartIso P0 e c hc N τ'' ΘB hΘB))

/-- The inverse image along the atlas of
`AlgebraicGeometry.Space.modulePullbackIsoOfOfIsoYoneda`, followed by the identification of `N^a`,
is the identification of `h^*𝒯` there. -/
theorem modulePullbackIsoOfOfIsoYoneda_spec :
    (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map
        (modulePullbackIsoOfOfIsoYoneda P0 e c hc N τ'' ΘB hΘB Pb hA yU yR hY hta hsb Tm τ κ hκ
          Θ hΘ).hom ≫
        (ofIsoYonedaChartIso P0 e c hc N ΘB).hom =
      (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom := by
  unfold modulePullbackIsoOfOfIsoYoneda
  exact modulePullback_map_presentationIsoOfChartIsos_hom _ _ _ _ _ _ _ _

end OfIsoYonedaIso


/-! ### The identification of a descended module along a representable base change -/

namespace RelativeProjPoints

section PullbackAlongYonedaIso

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {XA XA' : AlgebraicSpaces B S hS} {PA PA' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
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
  (Tm : QuasicoherentSheaves.{u, u} B S hS PA hP)
  {M : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA.fibre Px.U Px.toSpace)).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS (dA.spaceTarget Px hP) M ⟶
    quasicoherentPullbackObj B S hS (dA.spaceSource Px hP) M)
  (κ : (modulePullback B S hS (presentationAtlas (dA.spacePresentation Px hP))).obj Tm.obj ≅
    ((representedQuasicoherentSchemeEquivalence B S hS (dA.fibre Px.U Px.toSpace)).functor.obj
      M).obj)
  (hκ : TransitionCommutes B S hS (U := (presentationGroupoid (dA.spacePresentation Px hP)).objects)
    (V := (presentationGroupoid (dA.spacePresentation Px hP)).arrows)
    (a := (presentationGroupoid (dA.spacePresentation Px hP)).target)
    (b := (presentationGroupoid (dA.spacePresentation Px hP)).source)
    (spaceBaseDescent B S hS (presentationGroupoid (dA.spacePresentation Px hP))
      (presentationAtlas (dA.spacePresentation Px hP))
      (presentationAtlas_comm (dA.spacePresentation Px hP)) Tm.obj)
    (presentationSchemeTransition (dA.spacePresentation Px hP) M τ) κ.hom)
  {M'' : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj (dA'.fibre Px'.U Px'.toSpace)).ringCatSheaf).FullSubcategory}
  (τ'' : quasicoherentPullbackObj B S hS (dA'.spaceTarget Px' hP') M'' ⟶
    quasicoherentPullbackObj B S hS (dA'.spaceSource Px' hP') M'')
  (Θ : quasicoherentPullbackObj B S hS yU M ≅ M'')
  (hΘ : PullbackTransitionCompatible Px Px' hP hP' hℓt hℓs yU hyU yR hyR τ τ'' Θ)
  {W : BigFppfOver B S hS} (e : PA' ≅ yoneda.obj W) (c : dA'.fibre Px'.U Px'.toSpace ⟶ W)
  (hc : yoneda.map c = (dA'.spacePresentation Px' hP').toSpace ≫ e.hom)
  (hW : representedAlgebraicSpace B S hS W ⟶ ⟨PA, hP⟩)
  (hY : presentationAtlas ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc) ≫ hW =
    representedSpaceMap B S hS yU ≫ presentationAtlas (dA.spacePresentation Px hP))
  (N : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj W).ringCatSheaf).FullSubcategory)
  (ΘB : quasicoherentPullbackObj B S hS c N ≅ M'')
  (hΘB : canonicalSchemeTransition B S hS (dA'.spaceTarget Px' hP') (dA'.spaceSource Px' hP') c
      (Presentation.target_comp_eq_source_comp_of_iso (dA'.spacePresentation Px' hP') e c hc) N ≫
      quasicoherentPullbackMap B S hS (dA'.spaceSource Px' hP') ΘB.hom =
    quasicoherentPullbackMap B S hS (dA'.spaceTarget Px' hP') ΘB.hom ≫ τ'')


/-- **The inverse image of a descended module along a morphism from a representable base change**
(Stacks 03M3), as an isomorphism `hW^*𝒯 ≅ N^a`: the isomorphism of
`…RelativeProjPoints.exists_modulePullback_iso_of_pullbackTransitionCompatible`,
whose inverse image along the atlas is the composite of the identifications. -/
def pullbackTransitionCompatibleIso :
    (modulePullback B S hS hW).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj :=
  modulePullbackIsoOfOfIsoYoneda (dA'.spacePresentation Px' hP') e c hc N τ'' ΘB hΘB
    (dA.spacePresentation Px hP) hW yU yR hY
    (spacePresentation_target_comp_of_liesOverAlong Px Px' hP hP' hℓt yU hyU yR hyR)
    (comp_spacePresentation_source_of_liesOverAlong Px Px' hP hP' hℓs yU hyU yR hyR)
    Tm τ κ hκ Θ hΘ.eq

/-- The inverse image along the atlas of
`AlgebraicGeometry.Space.RelativeProjPoints.pullbackTransitionCompatibleIso`, followed by the
identification of `N^a` there, is the composite of the identifications. -/
theorem pullbackTransitionCompatibleIso_spec :
    (modulePullback B S hS
        (presentationAtlas ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc))).map
        (pullbackTransitionCompatibleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ τ'' Θ hΘ
          e c hc hW hY N ΘB hΘB).hom ≫
        (ofIsoYonedaChartIso (dA'.spacePresentation Px' hP') e c hc N ΘB).hom =
      (presentationPullbackChartIso ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc)
        (dA.spacePresentation Px hP) hW yU hY Tm κ Θ).hom := by
  unfold pullbackTransitionCompatibleIso
  exact modulePullbackIsoOfOfIsoYoneda_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **The identification is determined by its inverse image along the atlas**: an isomorphism
`hW^*𝒯 ≅ N^a` with the description of
`AlgebraicGeometry.Space.RelativeProjPoints.pullbackTransitionCompatibleIso_spec` is
`AlgebraicGeometry.Space.RelativeProjPoints.pullbackTransitionCompatibleIso`. -/
theorem eq_pullbackTransitionCompatibleIso
    (e' : (modulePullback B S hS hW).obj Tm.obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
    (he' : (modulePullback B S hS
        (presentationAtlas ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc))).map e'.hom ≫
        (ofIsoYonedaChartIso (dA'.spacePresentation Px' hP') e c hc N ΘB).hom =
      (presentationPullbackChartIso ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc)
        (dA.spacePresentation Px hP) hW yU hY Tm κ Θ).hom) :
    e' = pullbackTransitionCompatibleIso Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ τ'' Θ hΘ e
      c hc hW hY N ΘB hΘB :=
  Iso.ext (@presentationAtlas_map_injective _ _ _ _
    ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc) _ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ Tm.property)
    ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).property _ _
    ((Iso.cancel_iso_hom_right _ _
        (ofIsoYonedaChartIso (dA'.spacePresentation Px' hP') e c hc N ΘB)).1
      (he'.trans (pullbackTransitionCompatibleIso_spec Px Px' hP hP' hℓt hℓs yU hyU yR hyR Tm τ κ hκ
        τ'' Θ hΘ e c hc hW hY N ΘB hΘB).symm)))

end PullbackAlongYonedaIso

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-! ### The comparisons of twists along a morphism of base changes are multiplicative -/

section BaseChange

variable {X' : AlgebraicSpaces s.site s.base s.containsBase} (g : X' ⟶ s.space)

/-- `AlgebraicGeometry.Space.pullbackIsoOfSquare_hom_mul` at the comparison of the twists along a
morphism of base changes. -/
private theorem baseChangeTwistPieceComparison_mul_aux
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (i j : ℤ) :
    type_of% (pullbackIsoOfSquare_hom_mul
      (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
      (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
      (s.toRelativeProj U u)
      ((s.pullback g).toRelativeProj V v :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            ((s.pullback g).relativeProjPoints.fibre V v) ⟶
          (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.map_comp_toRelativeProj_baseChange g y)
      (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
        ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
        (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
        (s.isIso_baseChangeAlgebraHom_app g k u v hv)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.toScheme_map_eq_of_liesOverAlong g hv hy)) i j) :=
  pullbackIsoOfSquare_hom_mul ..

/-- The underlying morphism of the comparison of the twists along a morphism of base changes is
the comparison along the square of `AlgebraicGeometry.Space.RelativeProjSituation.toRelativeProj`
of the degree-`n` piece of Tag 01O3's `θ`, as `AlgebraicGeometry.Space.pullbackIsoOfSquare`. -/
private theorem baseChangeTwistPieceComparison_hom_hom_eq
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (n : ℤ) :
    (s.baseChangeTwistPieceComparison g k hv y hy n).hom.hom =
      (pullbackIsoOfSquare (s.toRelativeProj U u)
        ((s.pullback g).toRelativeProj V v :
          (BigFppfOver.toScheme s.site s.base s.containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v) ⟶
            (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.map_comp_toRelativeProj_baseChange g y)
        (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
          (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
            (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
            (s.isIso_baseChangeAlgebraHom_app g k u v hv)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.toScheme_map_eq_of_liesOverAlong g hv hy)) n)).hom :=
  (s.baseChangeTwistPieceComparison_hom_hom g k hv y hy n).trans
    (pullbackSheafIsoOfSquare_hom _ _ _ _ _ _)

/-- The tensor product of two comparisons of the twists along a morphism of base changes, in the
uncurried spelling. -/
private theorem quasicoherentTensorHom_baseChangeTwistPieceComparison_hom
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (i j : ℤ) :
    (quasicoherentTensorHom s.site s.base s.containsBase
        ((s.pullback g).relativeProjPoints.fibre V v)
        (s.baseChangeTwistPieceComparison g k hv y hy i).hom
        (s.baseChangeTwistPieceComparison g k hv y hy j).hom).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((BigFppfOver.toScheme (s.pullback g).site (s.pullback g).base
                (s.pullback g).containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v)).toRingedSpace.presheaf,
            ((BigFppfOver.toScheme (s.pullback g).site (s.pullback g).base
                (s.pullback g).containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v)).toRingedSpace.IsSheaf⟩)).map
        (((s.baseChangeTwistPieceComparison g k hv y hy i).hom.hom,
          (s.baseChangeTwistPieceComparison g k hv y hy j).hom.hom) : (_, _) ⟶ (_, _)) :=
  sheafTensor_whisker_eq_uncurry_map _ _

/-- The tensor product of two comparisons of the twists along a morphism of base changes, in the
uncurried spelling of the comparisons along the squares. -/
private theorem quasicoherentTensorHom_baseChangeTwistPieceComparison_hom_eq
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (i j : ℤ) :
    (quasicoherentTensorHom s.site s.base s.containsBase
        ((s.pullback g).relativeProjPoints.fibre V v)
        (s.baseChangeTwistPieceComparison g k hv y hy i).hom
        (s.baseChangeTwistPieceComparison g k hv y hy j).hom).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((BigFppfOver.toScheme (s.pullback g).site (s.pullback g).base
                (s.pullback g).containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v)).toRingedSpace.presheaf,
            ((BigFppfOver.toScheme (s.pullback g).site (s.pullback g).base
                (s.pullback g).containsBase).obj
              ((s.pullback g).relativeProjPoints.fibre V v)).toRingedSpace.IsSheaf⟩)).map
        (((pullbackIsoOfSquare (s.toRelativeProj U u)
            ((s.pullback g).toRelativeProj V v :
              (BigFppfOver.toScheme s.site s.base s.containsBase).obj
                  ((s.pullback g).relativeProjPoints.fibre V v) ⟶
                (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.map_comp_toRelativeProj_baseChange g y)
            (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
              (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
              (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
                ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
                (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
                (s.isIso_baseChangeAlgebraHom_app g k u v hv)
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
                (s.toScheme_map_eq_of_liesOverAlong g hv hy)) i)).hom,
          (pullbackIsoOfSquare (s.toRelativeProj U u)
            ((s.pullback g).toRelativeProj V v :
              (BigFppfOver.toScheme s.site s.base s.containsBase).obj
                  ((s.pullback g).relativeProjPoints.fibre V v) ⟶
                (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
            (s.map_comp_toRelativeProj_baseChange g y)
            (gradedPieceIso (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
              (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
              (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
                ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
                (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
                (s.isIso_baseChangeAlgebraHom_app g k u v hv)
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
                (s.toScheme_map_eq_of_liesOverAlong g hv hy)) j)).hom) : (_, _) ⟶ (_, _)) :=
  (s.quasicoherentTensorHom_baseChangeTwistPieceComparison_hom g k hv y hy i j).trans
    (uncurry_map_pair_congr _ (s.baseChangeTwistPieceComparison_hom_hom_eq g k hv y hy i)
      (s.baseChangeTwistPieceComparison_hom_hom_eq g k hv y hy j))

/-- **The comparisons of the twists along a morphism of base changes are compatible with the
multiplications.**  Along a morphism `y : V ×_{X'} P' ⟶ U ×_X P` lying over `k : V ⟶ U` and
`P' ⟶ P`, the comparisons `y^*𝒪(n) ≅ 𝒪(n)` of Tag 01O3 carry the multiplication of the twists of
`U ×_X P`, pulled back along `y` and read through Stacks 01CD, to the multiplication of the twists
of `V ×_{X'} P'`. -/
theorem baseChangeTwistPieceComparison_mul {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (i j : ℤ) :
    (quasicoherentPullbackTensorIso s.site s.base s.containsBase y (s.twistPieceQcoh U u i)
        (s.twistPieceQcoh U u j)).inv ≫
      quasicoherentPullbackMap s.site s.base s.containsBase y (s.twistPieceMul U u i j) ≫
      (s.baseChangeTwistPieceComparison g k hv y hy (i + j)).hom =
    quasicoherentTensorHom s.site s.base s.containsBase
        ((s.pullback g).relativeProjPoints.fibre V v)
        (s.baseChangeTwistPieceComparison g k hv y hy i).hom
        (s.baseChangeTwistPieceComparison g k hv y hy j).hom ≫
      (s.pullback g).twistPieceMul V v i j := by
  refine ObjectProperty.hom_ext _ ?_
  refine comp_comp_eq_comp_of_eqs
    (C := SheafOfModules.{u} ((BigFppfOver.toScheme s.site s.base s.containsBase).obj
      ((s.pullback g).relativeProjPoints.fibre V v)).ringCatSheaf) ?_ ?_
    (s.baseChangeTwistPieceComparison_hom_hom_eq g k hv y hy (i + j))
    (s.quasicoherentTensorHom_baseChangeTwistPieceComparison_hom_eq g k hv y hy i j) ?_
    (s.baseChangeTwistPieceComparison_mul_aux g k hv y hy i j)
  · rfl
  · rfl
  · rfl

/-- **The comparison of the twists along a morphism of base changes carries the unit to the
unit.**  Along a morphism `y : V ×_{X'} P' ⟶ U ×_X P` lying over `k` and `P' ⟶ P`, the comparison
`y^*𝒪(0) ≅ 𝒪(0)` of Tag 01O3 carries the unit of the twists of `U ×_X P`, pulled back along `y`
and read through Stacks 03LU, to the unit of the twists of `V ×_{X'} P'`. -/
theorem baseChangeTwistPieceComparison_unit {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) :
    (quasicoherentPullbackUnitIso s.site s.base s.containsBase y).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase y (s.twistPieceUnit U u) ≫
        (s.baseChangeTwistPieceComparison g k hv y hy 0).hom =
      (s.pullback g).twistPieceUnit V v := by
  refine ObjectProperty.hom_ext _ ?_
  refine Eq.trans ?_ (pullbackIsoOfSquare_hom_one
    (X := (relativeProj (s.shrink.pointAlgebra U u)).scheme)
    (Y := (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
    (s.toRelativeProj U u)
    ((s.pullback g).toRelativeProj V v :
      (BigFppfOver.toScheme s.site s.base s.containsBase).obj
          ((s.pullback g).relativeProjPoints.fibre V v) ⟶
        (relativeProj ((s.pullback g).shrink.pointAlgebra V v)).scheme)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
    (s.map_comp_toRelativeProj_baseChange g y)
    (congrBaseChangeTwistIso (s.shrink.pointAlgebra U u)
      ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map k)
      (A₁ := (s.pullback g).shrink.pointAlgebra V v) (s.baseChangeAlgebraHom g k u v hv)
      (s.isIso_baseChangeAlgebraHom_app g k u v hv)
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
      (s.toScheme_map_eq_of_liesOverAlong g hv hy)))
  exact congrArg (fun t => (Scheme.Modules.pullbackUnitIso
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).inv ≫
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).map
      (s.twistPieceUnit U u).hom ≫ t)
    (s.baseChangeTwistPieceComparison_hom_hom_eq g k hv y hy 0)

/-- **The comparisons of twists along a morphism of base changes carry the attached
multiplication to the attached multiplication**: the inverse image along `y` of the multiplication
`𝒪(i)^a ⊗ 𝒪(j)^a ⟶ 𝒪(i + j)^a` of the attached twists of `U ×_X P`, followed by the
identification of the inverse image of an attached module and the comparison of twists, is
Stacks 03EL followed by the comparisons and the multiplication of the attached twists of
`V ×_{X'} P'`. -/
theorem modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison
    {U V : BigFppfOver s.site s.base s.containsBase}
    {u : yoneda.obj U ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} (k : V ⟶ U)
    (hv : yoneda.map k ≫ u = v ≫ g.hom)
    (y : (s.pullback g).relativeProjPoints.fibre V v ⟶ s.relativeProjPoints.fibre U u)
    (hy : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) y k) (i j : ℤ) :
    type_of% (modulePullback_map_representedTensorChartMul_comp s.site s.base s.containsBase y
      (s.twistPieceMul U u i j) ((s.pullback g).twistPieceMul V v i j)
      (s.baseChangeTwistPieceComparison g k hv y hy i).hom
      (s.baseChangeTwistPieceComparison g k hv y hy j).hom
      (s.baseChangeTwistPieceComparison g k hv y hy (i + j)).hom
      (representedC3TensorCompat s.site s.base s.containsBase _ _ _)
      (s.baseChangeTwistPieceComparison_mul g k hv y hy i j)) :=
  modulePullback_map_representedTensorChartMul_comp s.site s.base s.containsBase y _ _ _ _ _
    (representedC3TensorCompat s.site s.base s.containsBase _ _ _)
    (s.baseChangeTwistPieceComparison_mul g k hv y hy i j)

end BaseChange

/-! ### The base change to a scheme point, as graded algebras -/

section Point

attribute [local instance] modulesMonoidalCategory

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- The relative Proj of the base change to the scheme point `f` is an algebraic space. -/
theorem isAlgebraicSpace_pointRelativeProjFunctor :
    type_of% ((s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor) :=
  (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor

/-- The morphism `T_U ×_T P' ⟶ U ×_X P` lies over `T_U ⟶ U` and `P' ⟶ P`. -/
theorem liesOverAlong_pointChartBaseChangeMap :
    type_of% (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f)) :=
  s.liesOverAlong_chartBaseChangeMap ..

/-- The morphism `T_R ×_T P' ⟶ R ×_X P` lies over `T_R ⟶ R` and `P' ⟶ P`. -/
theorem liesOverAlong_pointRelationBaseChangeMap :
    type_of% (s.liesOverAlong_relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f)) :=
  s.liesOverAlong_relationBaseChangeMap ..

/-- The comparisons of twists along `T_U ×_T P' ⟶ U ×_X P` carry the transitions of the twists
of `P` to those of `P'`. -/
theorem pullbackTransitionCompatible_pointChartBaseChangeMap (n : ℤ) :
    type_of% (s.pullbackTransitionCompatible_chartBaseChangeMap (s.schemePointHom T f) Px
      (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (Px.alongPointRelationMap f) (Px.alongPointRelationMap_comp_target f)
        (Px.alongPointRelationMap_comp_source f) n) :=
  s.pullbackTransitionCompatible_chartBaseChangeMap ..


/-- The chart identification of the descended twist carries the canonical transition of its
inverse image along the atlas to the transition of the twists, with the twist spelled as the
descended module it is by definition. -/
theorem presentationDescendedModuleChartIso_comm_twistTransition (n : ℤ) :
    type_of% (presentationDescendedModuleChartIso_comm_spaceBaseDescent
      (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
      (M := s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
      (s.presentationSchemeCocycle_twistTransition Px n)
      (s.presentationSchemeUnit_twistTransition Px n)) :=
  presentationDescendedModuleChartIso_comm_spaceBaseDescent ..

/-- **The base change identification of Stacks 084D in degree `n`**: the isomorphism
`(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a` of
`AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso`, descended
from its description on the étale cover `T_U ×_T P' ⟶ T ×_X P` by the comparisons of twists of
Tag 01O3 (`…RelativeProjSituation.fibreToSpaceTwistModuleIso_spec`); it is the only isomorphism
with that description (`…RelativeProjSituation.eq_fibreToSpaceTwistModuleIso`).  The twist is
passed as the descended module it is by definition. -/
def fibreToSpaceTwistModuleIso (n : ℤ) :
    (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.twistModule Px n).obj ≅
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f n)).obj :=
  RelativeProjPoints.pullbackTransitionCompatibleIso
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_pointChartBaseChangeMap Px T f)
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
      (presentationDescendedModule
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.twistTransition Px n)
      (presentationDescendedModuleChartIso
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)

/-- `AlgebraicGeometry.Space.RelativeProjSituation.fibreToSpaceTwistModuleIso` is the
identification of Stacks 03M3 along the morphism of relative Projs `Proj_T(f^*𝒜) ⟶ P`. -/
theorem fibreToSpaceTwistModuleIso_eq (n : ℤ) :
    s.fibreToSpaceTwistModuleIso Px T f n =
      RelativeProjPoints.pullbackTransitionCompatibleIso
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_pointChartBaseChangeMap Px T f)
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
      (presentationDescendedModule
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.twistTransition Px n)
      (presentationDescendedModuleChartIso
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n) :=
  rfl

/-- **The description of the base change identification on the étale cover
`T_U ×_T P' ⟶ T ×_X P`**: its inverse image along the atlas, followed by the identification of the
twist of Stacks 01NR there, is the composite of the comparisons of twists of Tag 01O3 along
`T_U ×_T P' ⟶ U ×_X P` and along `T_U ×_T P' ⟶ T ×_X P` (stated for
`…RelativeProjSituation.fibreToSpaceTwistModuleIso` unfolded by
`…RelativeProjSituation.fibreToSpaceTwistModuleIso_eq`). -/
theorem fibreToSpaceTwistModuleIso_spec (n : ℤ) :
    type_of% (RelativeProjPoints.pullbackTransitionCompatibleIso_spec
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_pointChartBaseChangeMap Px T f)
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
      (presentationDescendedModule
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.twistTransition Px n)
      (presentationDescendedModuleChartIso
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)) :=
  RelativeProjPoints.pullbackTransitionCompatibleIso_spec ..

/-- **The base change identification is determined by its description on the étale cover**. -/
theorem eq_fibreToSpaceTwistModuleIso (n : ℤ) :
    type_of% (RelativeProjPoints.eq_pullbackTransitionCompatibleIso
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.isAlgebraicSpace_pointRelativeProjFunctor T f)
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_pointChartBaseChangeMap Px T f)
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_pointRelationBaseChangeMap Px T f)
      (presentationDescendedModule
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.twistTransition Px n)
      (presentationDescendedModuleChartIso
        (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
        (s.twistPieceQcoh Px.U Px.toSpace n) (s.twistTransition Px n)
        (s.presentationSchemeCocycle_twistTransition Px n)
        (s.presentationSchemeUnit_twistTransition Px n))
      (s.presentationDescendedModuleChartIso_comm_twistTransition Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_pointChartBaseChangeMap Px T f n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)) :=
  fun e' he' => RelativeProjPoints.eq_pullbackTransitionCompatibleIso (e' := e') (he' := he') ..

/-- The comparisons of twists along `T_U ×_T P' ⟶ U ×_X P` carry the multiplication of the
attached twists on `U ×_X P`, pulled back, to the multiplication of the attached twists on
`T_U ×_T P'`. -/
theorem modulePullback_map_twistPieceMul_chartTwistComparison (i j : ℤ) :
    type_of% (s.modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison
      (s.schemePointHom T f)
      (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i j) :=
  s.modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison (s.schemePointHom T f)
      (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) i j

/-- The comparisons of twists along `T_U ×_T P' ⟶ T ×_X P` carry the multiplication of the
attached twists of Stacks 01NR on `T ×_X P`, pulled back, to the multiplication of the attached
twists on `T_U ×_T P'`. -/
theorem modulePullback_map_twistPieceMul_pointChartTwistComparison (i j : ℤ) :
    type_of% (s.modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison
      (s.schemePointHom T f)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
      i j) :=
  s.modulePullback_map_twistPieceMul_baseChangeTwistPieceComparison (s.schemePointHom T f)
      (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
      i j

end Point



end RelativeProjSituation

end AlgebraicGeometry.Space

end
