module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.BaseChangeTheta
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointBaseChange

/-!
# The twists `𝒪_P(n)` restricted to a scheme point of the base

In Situation 0849 let `P = Proj_X(𝒜)` be the relative homogeneous spectrum of Stacks 084B and
`𝒪_P(n)` the twist of Stacks 084D (`AlgebraicGeometry.Space.RelativeProjSituation.twistModule`),
descended from a presentation `X = U/R`.  For **every** scheme point `f : T ⟶ X` (an object `T`
of the site), the inverse image of `𝒪_P(n)` along the base change
`T ×_X P = Proj_T(f^*𝒜) ⟶ P` is the twist `𝒪(n)` of Stacks 01NR on `Proj_T(f^*𝒜)`: this is the
base change clause of Stacks 084D, degree by degree.

The point `f` is a morphism of algebraic spaces `T ⟶ X`, so Stacks 085C applies to it: the
relative Proj `P' = Proj_T(f^*𝒜)` of the pulled-back algebra is `T ×_X P`
(`AlgebraicGeometry.Space.RelativeProjSituation.isPullback_relativeProjBaseChangeHom`), hence
isomorphic to the representable `T ×_X P` of Stacks 084B.  The presentation of `P'` over the
presentation `T = T_U/T_R` (`AlgebraicGeometry.Space.Presentation.alongPoint`) maps to the
presentation of `P` over `X = U/R`, and the comparison of twists of Tag 01O3 along the presenting
schemes carries the transition of the twists of `P` to that of `P'` (the chart compatibility of
`θ_n` of Stacks 085C).  Along the atlas `T_U ×_T P' ⟶ T ×_X P` the twist of Stacks 01NR on
`T ×_X P` is again identified with the twist on the presenting scheme by Tag 01O3, carrying its
canonical transition to the same transition; so the two identifications descend (Stacks 03M3).

## Main definitions

* `AlgebraicGeometry.Space.Presentation.ofIso`: a presentation transported along an isomorphism
  of algebraic spaces, with any atlas equal to the transported one.
* `AlgebraicGeometry.Space.RelativeProjSituation.schemePointHom`: a scheme point `f : T ⟶ X` as a
  morphism of algebraic spaces.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointBaseChangeIso`: the identification of
  `Proj_T(f^*𝒜)` (Stacks 085C) with the base change `T ×_X P` of Stacks 084B.
* `AlgebraicGeometry.Space.RelativeProjSituation.pointChartMap`: the morphism
  `T_U ×_T P' ⟶ T ×_X P` from the presenting scheme of `P'`, the atlas of the presentation of
  `T ×_X P` transported from `P'` (`AlgebraicGeometry.Space.Presentation.ofIsoYoneda`).

## Main results

* `AlgebraicGeometry.Space.exists_modulePullback_iso_of_ofIsoYoneda`: for a morphism `h` from a
  representable algebraic space `W` to an algebraic space with a presentation, chart data of a
  quasi-coherent module `𝒯` and of a quasi-coherent module `N` on the scheme `W`, identified on a
  presentation of `W` with a common module carrying both transitions to a common one, give
  `h^*𝒯 ≅ N^a` (Stacks 03M3).
* `…RelativeProjSituation.canonicalSchemeTransition_baseChangeTwistPieceComparison`:
  the comparison of twists along a morphism of base changes lying over `h` carries the canonical
  transition of the pulled-back twist to the transition of the twists of `P'`.
* `AlgebraicGeometry.Space.RelativeProjSituation.exists_fibreToSpace_twistModule_iso`: **the base
  change clause of Stacks 084D, degreewise**: `(T ×_X P ⟶ P)^*𝒪_P(n) ≅ 𝒪(n)^a`, by the
  isomorphism which on the étale cover `T_U ×_T P' ⟶ T ×_X P` is the composite of the comparisons
  of twists of Tag 01O3.

## Implementation notes

The descent step is proved once at free variables
(`AlgebraicGeometry.Space.exists_modulePullback_iso_of_ofIsoYoneda`, then
`…RelativeProjPoints.exists_modulePullback_iso_of_pullbackTransitionCompatible`,
whose compatibility hypothesis is the structure of Stacks 085C's `θ_n`) and instantiated once.
The final statement spells out the transported presentation of `T ×_X P` over the site of `X`
instead of naming it by an abbreviation: the nested proofs of an abbreviation's body are
abstracted into auxiliary lemmas, and comparing those with the proofs of the instance is out of
reach of the elaborator and of the kernel.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-! ### Transporting a presentation along an isomorphism -/

namespace Presentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P : Presentation B S hS F hF) (hG : IsAlgebraicSpace B S hS G) (e : F ≅ G)
  (a : yoneda.obj P.U ⟶ G) (ha : a = P.toSpace ≫ e.hom)

include ha in
/-- An atlas followed by an isomorphism is a base change of the atlas. -/
theorem isPullback_id_of_eq_comp_iso : IsPullback (𝟙 (yoneda.obj P.U)) a P.toSpace e.inv :=
  IsPullback.of_horiz_isIso ⟨by
    rw [ha, Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]⟩

include ha in
/-- The relation of a presentation is the kernel pair of the atlas followed by an isomorphism. -/
theorem isPullback_of_eq_comp_iso :
    IsPullback (yoneda.map P.target) (yoneda.map P.source) a a :=
  P.isPullback.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
    (by rw [ha]; simp) (by rw [ha]; simp)

/-- **A presentation transported along an isomorphism `e : F ≅ G` of algebraic spaces**: the same
presenting scheme and relation, with atlas any morphism equal to the atlas followed by `e`. -/
abbrev ofIso : Presentation B S hS G hG where
  U := P.U
  R := P.R
  target := P.target
  source := P.source
  isEtaleEquivalenceRelation := P.isEtaleEquivalenceRelation
  toSpace := a
  surjective := presheaf_of_isPullback B S hS (P.isPullback_id_of_eq_comp_iso e a ha) P.surjective
  etale := presheaf_of_isPullback B S hS (P.isPullback_id_of_eq_comp_iso e a ha) P.etale
  isPullback := P.isPullback_of_eq_comp_iso e a ha

end Presentation

/-! ### Isomorphisms on a representable algebraic space from identifications on a presentation -/

section OfIsoYoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
  (P0 : Presentation B S hS F hF) {W : BigFppfOver B S hS} (e : F ≅ yoneda.obj W)
  (c : P0.U ⟶ W) (hc : yoneda.map c = P0.toSpace ≫ e.hom)

/-- The presentation of the representable algebraic space `W` transported from `P0` along
`e : F ≅ W`, with the represented atlas `c`. -/
abbrev Presentation.ofIsoYoneda :
    Presentation B S hS (representedAlgebraicSpace B S hS W).obj
      (representedAlgebraicSpace B S hS W).property :=
  P0.ofIso (isAlgebraicSpace_yoneda B S hS W) e (yoneda.map c) hc

include hc in
/-- The represented atlas `c` equalizes the two projections of the relation. -/
theorem Presentation.target_comp_eq_source_comp_of_iso : P0.target ≫ c = P0.source ≫ c :=
  Yoneda.fullyFaithful.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hc, P0.isPullback.w_assoc])

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

/-- The identification of `N^a` on the atlas of the transported presentation:
`c^*(N^a) ≅ (c^*N)^a ≅ M''^a`. -/
abbrev ofIsoYonedaChartIso :
    (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).obj
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj ≅
      ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.obj M'').obj :=
  modulePullbackRepresentedQuasicoherentIso B S hS c N ≪≫
    (ObjectProperty.ι _).mapIso
      ((representedQuasicoherentSchemeEquivalence B S hS P0.U).functor.mapIso ΘB)

include hΘB in
/-- **The identification on the atlas of `N^a` carries its canonical transition to `τ''^a`.** -/
theorem transitionCommutes_ofIsoYonedaChartIso :
    TransitionCommutes B S hS (U := (presentationGroupoid (P0.ofIsoYoneda e c hc)).objects)
      (V := (presentationGroupoid (P0.ofIsoYoneda e c hc)).arrows)
      (a := (presentationGroupoid (P0.ofIsoYoneda e c hc)).target)
      (b := (presentationGroupoid (P0.ofIsoYoneda e c hc)).source)
      (spaceBaseDescent B S hS (presentationGroupoid (P0.ofIsoYoneda e c hc))
        (presentationAtlas (P0.ofIsoYoneda e c hc))
        (presentationAtlas_comm (P0.ofIsoYoneda e c hc))
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj)
      (presentationSchemeTransition (P0.ofIsoYoneda e c hc) M'' τ'')
      (ofIsoYonedaChartIso P0 e c hc N ΘB).hom := by
  have hts := P0.target_comp_eq_source_comp_of_iso e c hc
  have hcomp : @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
        (representedSpaceMap B S hS P0.target) (representedSpaceMap B S hS c) =
      @CategoryStruct.comp (AlgebraicSpaces B S hS) _ _ _ _
        (representedSpaceMap B S hS P0.source) (representedSpaceMap B S hS c) :=
    representedSpaceMap_comp_eq_of_comp_eq B S hS hts
  have h1 := transitionCommutes_representedQuasicoherent B S hS P0.target P0.source c hts N hcomp
  have h2 := representedSchemeTransition_naturality B S hS P0.target P0.source
    (quasicoherentPullbackObj B S hS c N)
    (canonicalSchemeTransition B S hS P0.target P0.source c hts N) τ'' ΘB.hom hΘB
  exact TransitionCommutes.trans h1 h2

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

include hΘB hκ hΘ in
/-- **The inverse image of a descended module on a representable algebraic space** (Stacks
03M3): for `h : W ⟶ X`, chart data `(M, τ, κ)` of a quasi-coherent `𝒪_X`-module `𝒯` on a
presentation of `X`, a quasi-coherent module `N` on the scheme `W`, and identifications
`Θ : yU^*M ≅ M''` and `ΘB : c^*N ≅ M''` on the presenting scheme of a presentation of `W` with
represented atlas `c`, carrying the pulled-back transition of `τ` and the canonical transition of
`c^*N` to a common transition `τ''`, there is an isomorphism `h^*𝒯 ≅ N^a` whose inverse image
along the atlas is the composite of the two identifications. -/
theorem exists_modulePullback_iso_of_ofIsoYoneda :
    ∃ e' : (modulePullback B S hS hA).obj Tm.obj ≅
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj,
      (modulePullback B S hS (presentationAtlas (P0.ofIsoYoneda e c hc))).map e'.hom ≫
          (ofIsoYonedaChartIso P0 e c hc N ΘB).hom =
        (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ).hom :=
  ⟨(ObjectProperty.ι _).mapIso
      (presentationIsoOfChartIsos (P0.ofIsoYoneda e c hc) τ''
        ⟨(modulePullback B S hS hA).obj Tm.obj,
          isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _ Tm.property⟩
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N)
        (presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU hY Tm κ Θ)
        (transitionCommutes_presentationPullbackChartIso (P0.ofIsoYoneda e c hc) Pb hA yU yR hY
          hta hsb Tm τ κ hκ τ'' Θ hΘ)
        (ofIsoYonedaChartIso P0 e c hc N ΘB)
        (transitionCommutes_ofIsoYonedaChartIso P0 e c hc N τ'' ΘB hΘB)),
    modulePullback_map_presentationIsoOfChartIsos_hom _ _ _ _ _ _ _ _⟩

end OfIsoYoneda

/-! ### Along a morphism of relative Projs to a representable base change -/

namespace RelativeProjPoints

section PullbackAlongYoneda

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

include hκ hΘ hΘB in
/-- **The inverse image of a descended module along a morphism from a representable base change**
(Stacks 03M3): for a morphism `h : P' ⟶ P` of relative Projs, a morphism `y` of the presenting
schemes `U' ×_{X'} P' ⟶ U ×_X P` lying over `h` with a compatible identification
`Θ : y^*M ≅ M''`, an isomorphism `P' ≅ W` with a representable algebraic space, and an
identification `ΘB : c^*N ≅ M''` along the represented atlas `c : U' ×_{X'} P' ⟶ W` carrying the
canonical transition to `τ''`, there is an isomorphism `hW^*𝒯 ≅ N^a` for any `hW : W ⟶ P`
compatible with the atlases, whose inverse image along the atlas is the composite of the
identifications. -/
theorem exists_modulePullback_iso_of_pullbackTransitionCompatible :
    ∃ e' : (modulePullback B S hS hW).obj Tm.obj ≅
        ((representedQuasicoherentSchemeEquivalence B S hS W).functor.obj N).obj,
      (modulePullback B S hS
          (presentationAtlas ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc))).map e'.hom ≫
          (ofIsoYonedaChartIso (dA'.spacePresentation Px' hP') e c hc N ΘB).hom =
        (presentationPullbackChartIso ((dA'.spacePresentation Px' hP').ofIsoYoneda e c hc)
          (dA.spacePresentation Px hP) hW yU hY Tm κ Θ).hom :=
  exists_modulePullback_iso_of_ofIsoYoneda (dA'.spacePresentation Px' hP') e c hc N τ'' ΘB hΘB
    (dA.spacePresentation Px hP) hW yU yR hY
    (spacePresentation_target_comp_of_liesOverAlong Px Px' hP hP' hℓt yU hyU yR hyR)
    (comp_spacePresentation_source_of_liesOverAlong Px Px' hP hP' hℓs yU hyU yR hyR)
    Tm τ κ hκ Θ hΘ.eq

end PullbackAlongYoneda

end RelativeProjPoints

namespace RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-! ### The comparison of twists along a morphism of base changes and canonical transitions -/

section CanonicalBaseChange

variable {X' : AlgebraicSpaces s.site s.base s.containsBase} (g : X' ⟶ s.space)

/-- **The comparison of twists along a morphism `q` of base changes lying over `h` carries the
canonical transition of the pulled-back twist to the transition of the twists of `P'`**, at
variable points: for projections `t', s' : R ×_{X'} P' ⇉ V ×_{X'} P'` lying over `kt, ks` with
`t' ≫ q = s' ≫ q` and `kt ≫ kq = ks ≫ kq`, and `q : V ×_{X'} P' ⟶ W ×_X P` lying over `kq` and
`h`. -/
theorem canonicalSchemeTransition_baseChangeTwistPieceComparison
    {W V R : BigFppfOver s.site s.base s.containsBase}
    {w : yoneda.obj W ⟶ s.space.1} {v : yoneda.obj V ⟶ X'.1} {r : yoneda.obj R ⟶ X'.1}
    (kq : V ⟶ W) (hv : yoneda.map kq ≫ w = v ≫ g.hom)
    (q : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase) (X := X'.obj)
        (s.pullback g).relativeProjPoints V v ⟶ s.relativeProjPoints.fibre W w)
    (hq : (s.pullback g).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom g) q kq)
    (kt ks : R ⟶ V) (hrt : yoneda.map kt ≫ v = r) (hrs : yoneda.map ks ≫ v = r)
    (t' s' : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := X'.obj) (s.pullback g).relativeProjPoints R r ⟶
      RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase) (X := X'.obj)
        (s.pullback g).relativeProjPoints V v)
    (ht' : (s.pullback g).relativeProjPoints.LiesOver t' kt)
    (hs' : (s.pullback g).relativeProjPoints.LiesOver s' ks)
    (hts : t' ≫ q = s' ≫ q) (hk : kt ≫ kq = ks ≫ kq) (n : ℤ)
    (τ'' : quasicoherentPullbackObj s.site s.base s.containsBase t'
        ((s.pullback g).twistPieceQcoh V v n) ⟶
      quasicoherentPullbackObj s.site s.base s.containsBase s'
        ((s.pullback g).twistPieceQcoh V v n))
    (hτ'' : τ'' = ((s.pullback g).twistPieceComparison kt hrt t' ht' n).hom ≫
        ((s.pullback g).twistPieceComparison ks hrs s' hs' n).inv) :
    canonicalSchemeTransition s.site s.base s.containsBase t' s' q hts (s.twistPieceQcoh W w n) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase s'
        (s.baseChangeTwistPieceComparison g kq hv q hq n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase t'
        (s.baseChangeTwistPieceComparison g kq hv q hq n).hom ≫ τ'' := by
  subst hτ''
  have hp : ∀ k : R ⟶ V, yoneda.map k ≫ v = r → yoneda.map (k ≫ kq) ≫ w = r ≫ g.hom :=
    fun k hr => by rw [Functor.map_comp, Category.assoc, hv, ← Category.assoc, hr]
  have key : ∀ (k : R ⟶ V) (hr : yoneda.map k ≫ v = r)
      (u : RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := X'.obj) (s.pullback g).relativeProjPoints R r ⟶
        RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := X'.obj) (s.pullback g).relativeProjPoints V v)
      (hu : (s.pullback g).relativeProjPoints.LiesOver u k),
      (s.baseChangeTwistPieceComparison g (k ≫ kq) (hp k hr) (u ≫ q)
        (hu.comp_liesOverAlong hq) n).hom =
      (quasicoherentPullbackCompIso s.site s.base s.containsBase u q
          (s.twistPieceQcoh W w n)).inv ≫
        quasicoherentPullbackMap s.site s.base s.containsBase u
          (s.baseChangeTwistPieceComparison g kq hv q hq n).hom ≫
          ((s.pullback g).twistPieceComparison k hr u hu n).hom :=
    fun k hr u hu => ObjectProperty.hom_ext _
      ((s.baseChangeTwistSheafIso_liesOver_comp g kq k hv hr (hp k hr) q u hq hu n).trans
        ((congrArg (· ≫ _) (rfl : (Scheme.Modules.pullbackCongr
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp u q)).hom.app
            ((Scheme.Modules.pullback (s.toRelativeProj W w)).obj
              ((Stacks.AlgebraicGeometry.Tag07ZGTwist.twistAlgebra
                (s.shrink.pointAlgebra W w)).piece n)) = 𝟙 _)).trans
          (Category.id_comp _)))
  exact canonicalTransition_of_comparisons
    (quasicoherentPullbackCompIso s.site s.base s.containsBase t' q (s.twistPieceQcoh W w n))
    (quasicoherentPullbackCompIso s.site s.base s.containsBase s' q (s.twistPieceQcoh W w n))
    (quasicoherentPullbackEqToHom s.site s.base s.containsBase hts (s.twistPieceQcoh W w n))
    (quasicoherentPullbackMap s.site s.base s.containsBase t'
      (s.baseChangeTwistPieceComparison g kq hv q hq n).hom)
    (quasicoherentPullbackMap s.site s.base s.containsBase s'
      (s.baseChangeTwistPieceComparison g kq hv q hq n).hom)
    ((s.pullback g).twistPieceComparison kt hrt t' ht' n)
    ((s.pullback g).twistPieceComparison ks hrs s' hs' n)
    (s.baseChangeTwistPieceComparison g (kt ≫ kq) (hp kt hrt) (t' ≫ q)
      (ht'.comp_liesOverAlong hq) n)
    (s.baseChangeTwistPieceComparison g (ks ≫ kq) (hp ks hrs) (s' ≫ q)
      (hs'.comp_liesOverAlong hq) n)
    (key kt hrt t' ht') (key ks hrs s' hs')
    (s.quasicoherentPullbackEqToHom_comp_baseChangeTwistPieceComparison_hom g
      (hv₁ := hp kt hrt) (hv₂ := hp ks hrs) (hy₁ := ht'.comp_liesOverAlong hq)
      (hy₂ := hs'.comp_liesOverAlong hq) hts hk n)

end CanonicalBaseChange

/-! ### The base change to a scheme point -/

section Point

variable (Px : Presentation s.site s.base s.containsBase s.space.obj s.space.property)
  (T : BigFppfOver s.site s.base s.containsBase) (f : yoneda.obj T ⟶ s.space.1)

/-- **A scheme point `f : T ⟶ X` as a morphism of algebraic spaces.** -/
abbrev schemePointHom : representedAlgebraicSpace s.site s.base s.containsBase T ⟶ s.space :=
  ObjectProperty.homMk f

/-- **`Proj_T(f^*𝒜) = T ×_X P`**: the relative Proj of the pulled-back algebra along the scheme
point `f` (Stacks 085C) is the base change of `P` along `f` of Stacks 084B. -/
abbrev pointBaseChangeIso :
    (s.pullback (s.schemePointHom T f)).relativeProjFunctor ≅
      yoneda.obj (s.relativeProjPoints.fibre T f) :=
  (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f)).isoIsPullback _ _
    (s.relativeProjPoints.isPullback T f)

/-- **The morphism `T_U ×_T P' ⟶ T ×_X P`** from the presenting scheme of `P' = Proj_T(f^*𝒜)`
over the presentation `T = T_U/T_R`, lying over the projection `T_U ⟶ T` and over
`P' ⟶ P`. -/
abbrev pointChartMap :
    RelativeProjPoints.fibre (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := (representedAlgebraicSpace s.site s.base s.containsBase T).obj)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints
        (Px.alongPoint f).U (Px.alongPoint f).toSpace ⟶ s.relativeProjPoints.fibre T f :=
  RelativeProjPoints.fibreMapAlong (B := s.site) (S := s.base) (hS := s.containsBase) _ _ _
    (s.relativeProjBaseChangeHom_comp_relativeProjπ (s.schemePointHom T f)) f
    (Px.alongPoint f).toSpace (Px.alongPointToPoint f) rfl

/-- The morphism `T_U ×_T P' ⟶ T ×_X P` lies over `T_U ⟶ T` and `P' ⟶ P`. -/
theorem liesOverAlong_pointChartMap :
    (s.pullback (s.schemePointHom T f)).relativeProjPoints.LiesOverAlong s.relativeProjPoints
      (s.relativeProjBaseChangeHom (s.schemePointHom T f)) (s.pointChartMap Px T f)
      (Px.alongPointToPoint f) :=
  RelativeProjPoints.liesOverAlong_fibreMapAlong _ _ _ _ _

/-- The morphism `T_U ×_T P' ⟶ T ×_X P` is the atlas of `P'` followed by `P' ≅ T ×_X P`. -/
theorem map_pointChartMap :
    yoneda.map (s.pointChartMap Px T f) =
      (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := representedAlgebraicSpace s.site s.base s.containsBase T)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor).toSpace ≫
        (s.pointBaseChangeIso T f).hom := by
  have hy := s.liesOverAlong_pointChartMap Px T f
  have h1 := IsPullback.isoIsPullback_hom_fst _ _
    (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f))
    (s.relativeProjPoints.isPullback T f)
  have h2 := IsPullback.isoIsPullback_hom_snd _ _
    (s.isPullback_relativeProjBaseChangeHom (s.schemePointHom T f))
    (s.relativeProjPoints.isPullback T f)
  refine (s.relativeProjPoints.isPullback T f).hom_ext ?_ ?_
  · exact hy.2.trans ((congrArg (_ ≫ ·) h1).symm.trans (Category.assoc _ _ _).symm)
  · exact (Functor.map_comp yoneda _ _).symm.trans ((congrArg yoneda.map hy.1).trans
      ((Functor.map_comp yoneda _ _).trans
        (((s.pullback (s.schemePointHom T f)).relativeProjPoints.isPullback
          (Px.alongPoint f).U (Px.alongPoint f).toSpace).w.symm.trans
          ((congrArg (_ ≫ ·) h2).symm.trans (Category.assoc _ _ _).symm))))

/-- The morphism `T_U ×_T P' ⟶ T ×_X P` equalizes the two projections of the relation. -/
theorem spaceTarget_comp_pointChartMap :
    RelativeProjPoints.spaceTarget (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := representedAlgebraicSpace s.site s.base s.containsBase T)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints
        (Px.alongPoint f) (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor ≫
        s.pointChartMap Px T f =
      RelativeProjPoints.spaceSource (B := s.site) (S := s.base) (hS := s.containsBase)
        (X := representedAlgebraicSpace s.site s.base s.containsBase T)
          (s.pullback (s.schemePointHom T f)).relativeProjPoints
        (Px.alongPoint f) (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor ≫
        s.pointChartMap Px T f :=
  Presentation.target_comp_eq_source_comp_of_iso
    (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
        (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
      (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)

/-- **The base change `T ×_X P ⟶ P` of Stacks 084B**, as a morphism of algebraic spaces. -/
abbrev fibreToSpaceHom :
    representedAlgebraicSpace s.site s.base s.containsBase (s.relativeProjPoints.fibre T f) ⟶
      ⟨s.relativeProjFunctor, s.isAlgebraicSpace_relativeProjFunctor⟩ :=
  ObjectProperty.homMk (s.relativeProjPoints.fibreToSpace T f)

/-- The atlas of `T ×_X P` and the atlas of `P` are compatible with the morphism of the
presenting schemes `T_U ×_T P' ⟶ U ×_X P`. -/
theorem presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom :
    presentationAtlas (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
      (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
        (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
      (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)) ≫
      s.fibreToSpaceHom T f =
      representedSpaceMap s.site s.base s.containsBase
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)) ≫
        presentationAtlas
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor) :=
  ObjectProperty.hom_ext _ ((s.liesOverAlong_pointChartMap Px T f).2.trans
    (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
      (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)).2.symm)

/-- **The comparison of twists of Tag 01O3 along `T_U ×_T P' ⟶ T ×_X P`**,
`(T_U ×_T P' ⟶ T ×_X P)^*𝒪(n) ≅ 𝒪(n)`. -/
abbrev pointChartTwistComparison (n : ℤ) :=
  s.baseChangeTwistPieceComparison (s.schemePointHom T f) (Px.alongPointToPoint f) rfl
    (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f) n

/-- The comparison of twists along `T_U ×_T P' ⟶ T ×_X P` carries the canonical transition of
the pulled-back twist of `T ×_X P` to the transition of the twists of `P'`. -/
theorem canonicalSchemeTransition_pointChartTwistComparison (n : ℤ) :
    canonicalSchemeTransition s.site s.base s.containsBase
        (RelativeProjPoints.spaceTarget (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := representedAlgebraicSpace s.site s.base s.containsBase T)
            (s.pullback (s.schemePointHom T f)).relativeProjPoints
          (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
        (RelativeProjPoints.spaceSource (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := representedAlgebraicSpace s.site s.base s.containsBase T)
            (s.pullback (s.schemePointHom T f)).relativeProjPoints
          (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
        (s.pointChartMap Px T f)
        (s.spaceTarget_comp_pointChartMap Px T f)
        (s.twistPieceQcoh T f n) ≫
      quasicoherentPullbackMap s.site s.base s.containsBase
        (RelativeProjPoints.spaceSource (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := representedAlgebraicSpace s.site s.base s.containsBase T)
            (s.pullback (s.schemePointHom T f)).relativeProjPoints
          (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
        (s.pointChartTwistComparison Px T f n).hom =
    quasicoherentPullbackMap s.site s.base s.containsBase
        (RelativeProjPoints.spaceTarget (B := s.site) (S := s.base) (hS := s.containsBase)
          (X := representedAlgebraicSpace s.site s.base s.containsBase T)
            (s.pullback (s.schemePointHom T f)).relativeProjPoints
          (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
        (s.pointChartTwistComparison Px T f n).hom ≫
      (s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n :=
  s.canonicalSchemeTransition_baseChangeTwistPieceComparison (s.schemePointHom T f)
    (X' := representedAlgebraicSpace s.site s.base s.containsBase T) (W := T)
    (V := (Px.alongPoint f).U) (R := (Px.alongPoint f).R) (w := f)
    (v := (Px.alongPoint f).toSpace) (r := RelativeProjPoints.relationPoint (Px.alongPoint f))
    (Px.alongPointToPoint f) rfl (s.pointChartMap Px T f) (s.liesOverAlong_pointChartMap Px T f)
    (Px.alongPoint f).target (Px.alongPoint f).source rfl
    ((s.pullback (s.schemePointHom T f)).map_source_comp_toSpace (Px.alongPoint f))
    (RelativeProjPoints.spaceTarget (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
        (s.pullback (s.schemePointHom T f)).relativeProjPoints
      (Px.alongPoint f) (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    (RelativeProjPoints.spaceSource (B := s.site) (S := s.base) (hS := s.containsBase)
      (X := representedAlgebraicSpace s.site s.base s.containsBase T)
        (s.pullback (s.schemePointHom T f)).relativeProjPoints
      (Px.alongPoint f) (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    ((s.pullback (s.schemePointHom T f)).relativeProjPoints.liesOver_spaceTarget (Px.alongPoint f)
      (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    ((s.pullback (s.schemePointHom T f)).relativeProjPoints.liesOver_spaceSource (Px.alongPoint f)
      (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
    (s.spaceTarget_comp_pointChartMap Px T f) (Px.alongPointTarget_comp_toPoint f) n
    ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n) rfl

/-- **The base change clause of Stacks 084D, degreewise**: for every scheme point `f : T ⟶ X`,
the inverse image of the twist `𝒪_P(n)` along the base change `T ×_X P = Proj_T(f^*𝒜) ⟶ P` is
the module `𝒪(n)^a` attached to the twist `𝒪(n)` of Stacks 01NR on `Proj_T(f^*𝒜)`, by an
isomorphism which on the étale cover `T_U ×_T P' ⟶ T ×_X P` (the presenting scheme of
`P' = Proj_T(f^*𝒜)` over `T_U = T ×_X U`) is the composite of the comparisons of twists of Tag 01O3
along `T_U ×_T P' ⟶ U ×_X P` and along `T_U ×_T P' ⟶ T ×_X P`. -/
theorem exists_fibreToSpace_twistModule_iso (n : ℤ) :
    ∃ e : (modulePullback s.site s.base s.containsBase (s.fibreToSpaceHom T f)).obj
        (s.twistModule Px n).obj ≅
        ((representedQuasicoherentSchemeEquivalence s.site s.base s.containsBase
          (s.relativeProjPoints.fibre T f)).functor.obj (s.twistPieceQcoh T f n)).obj,
      (modulePullback s.site s.base s.containsBase
          (presentationAtlas (Presentation.ofIsoYoneda (RelativeProjPoints.spacePresentation
            (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
              (s.map_pointChartMap Px T f)))).map e.hom ≫
          (ofIsoYonedaChartIso (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base)
            (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f)
            (s.map_pointChartMap Px T f) (s.twistPieceQcoh T f n)
            (s.pointChartTwistComparison Px T f n)).hom =
        (presentationPullbackChartIso (Presentation.ofIsoYoneda
          (RelativeProjPoints.spacePresentation (B := s.site) (S := s.base) (hS := s.containsBase)
            (X := representedAlgebraicSpace s.site s.base s.containsBase T)
              (s.pullback (s.schemePointHom T f)).relativeProjPoints (Px.alongPoint f)
            (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor)
            (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f))
          (s.relativeProjPoints.spacePresentation Px s.isAlgebraicSpace_relativeProjFunctor)
          (s.fibreToSpaceHom T f)
          (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f))
          (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
          (s.twistModule Px n) (s.twistModuleChartIso Px n)
          (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f)
            (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f) n)).hom := by
  have h :=
    RelativeProjPoints.exists_modulePullback_iso_of_pullbackTransitionCompatible
      (XA' := representedAlgebraicSpace s.site s.base s.containsBase T)
      (dA := s.relativeProjPoints) (dA' := (s.pullback (s.schemePointHom T f)).relativeProjPoints)
      (hA := s.relativeProjBaseChangeHom (s.schemePointHom T f)) Px (Px.alongPoint f)
      s.isAlgebraicSpace_relativeProjFunctor
        (s.pullback (s.schemePointHom T f)).isAlgebraicSpace_relativeProjFunctor
      (Px.alongPointRelationMap_comp_target f) (Px.alongPointRelationMap_comp_source f)
      (s.chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.liesOverAlong_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f))
      (s.relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.liesOverAlong_relationBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) (Px.alongPointRelationMap f)
        (Px.alongPointRelationMap_comp_target f))
      (s.twistModule Px n) (s.twistTransition Px n) (s.twistModuleChartIso Px n)
      (s.twistModuleChartIso_comm_spaceBaseDescent Px n)
      ((s.pullback (s.schemePointHom T f)).twistTransition (Px.alongPoint f) n)
      (s.chartTwistComparison (s.schemePointHom T f) Px (Px.alongPoint f) (Px.alongPointToAtlas f)
        (Px.map_alongPointToAtlas_comp_toSpace' f) n)
      (s.pullbackTransitionCompatible_chartBaseChangeMap (s.schemePointHom T f) Px (Px.alongPoint f)
        (Px.alongPointToAtlas f) (Px.map_alongPointToAtlas_comp_toSpace' f)
        (Px.alongPointRelationMap f) (Px.alongPointRelationMap_comp_target f)
        (Px.alongPointRelationMap_comp_source f) n)
      (s.pointBaseChangeIso T f) (s.pointChartMap Px T f) (s.map_pointChartMap Px T f)
      (s.fibreToSpaceHom T f) (s.presentationAtlas_ofIsoYoneda_comp_fibreToSpaceHom Px T f)
      (s.twistPieceQcoh T f n) (s.pointChartTwistComparison Px T f n)
      (s.canonicalSchemeTransition_pointChartTwistComparison Px T f n)
  obtain ⟨e, he⟩ := h
  exact ⟨e, he⟩

end Point

end RelativeProjSituation

end AlgebraicGeometry.Space

end
