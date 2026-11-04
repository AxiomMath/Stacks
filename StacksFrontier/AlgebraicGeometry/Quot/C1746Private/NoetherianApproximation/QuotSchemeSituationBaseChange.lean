/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotSchemeSituationRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Representability of `Quot^P` over an affine scheme along a cartesian square of schemes

Let `q' : U' ⟶ W'` be a morphism of schemes of the site with a morphism `i' : U' ⟶ ℙⁿ_{W'}`, `F'`
a quasi-coherent module on `h_{U'}`, and let

```
U ──g──▶ U'
│q       │q'
▼        ▼
W ──w──▶ W'
```

be a cartesian square of the site with `i : U ⟶ ℙⁿ_W` the base change of `i'` and `F ≅ g^* F'`.
If `Quot^{P, i'^*𝒪(1)}_{F'/U'/W'}` is represented by a scheme separated and of finite
presentation over `W'`, then `Quot^{P, i^*𝒪(1)}_{F/U/W}` is represented by a scheme separated and
of finite presentation over `W`. This is the base change step of the Noetherian approximation in
the proof of Stacks 0DPD: `W'` is a Noetherian stage of the affine scheme `W`.

The representing scheme over `W` is the fibre product `Z' ×_{W'} W` of the site; the subfunctor
`Quot^P ×_{W'} W` is identified with `Quot^P` of the base-changed situation
(`AlgebraicGeometry.Space.QuotSituation.baseChangeSubfunctor_hilbertPolynomialQuot`), and that
situation with `F/U/W` through the isomorphism `X' ×_{W'} W ≅ h_U` (Stacks 0DP4 for an
isomorphism), the identification `F ≅ g^* F'` (Stacks 0DP5 for an isomorphism) and the
identification of the two inverse images of `𝒪(1)`.

## Main results

* `Space.QuotSituation.isRepresentedSeparatedFinitePresentation_baseChangeSubfunctor` (in the
  namespace `AlgebraicGeometry`): representability over `W'` gives representability of the base
  change over `W`.
* `AlgebraicGeometry.Space.QuotSituation.isRepresentedSeparatedFinitePresentation_of_isPullback`:
  the statement above.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
* [Stacks Project, Tag 0DP5](https://stacks.math.columbia.edu/tag/0DP5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- A property of morphisms of schemes stable under base change passes from the right side to the
left side of a cartesian square of the site. -/
theorem toScheme_map_of_isPullback {P : MorphismProperty Scheme.{u}}
    (hP : P.IsStableUnderBaseChange) {Z Z' W W' : BigFppfOver B integerBase ℤS} {a : Z ⟶ Z'}
    {r : Z ⟶ W} {r' : Z' ⟶ W'} {w : W ⟶ W'} (sq : IsPullback a r r' w)
    (h : P ((𝒯).map r')) : P ((𝒯).map r) :=
  (presheaf_yoneda_map_iff B integerBase ℤS hP r).1
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback (sq.map yoneda)
      ((presheaf_yoneda_map_iff B integerBase ℤS hP r').2 h))

/-- **Base change of a represented subfunctor.** If a subfunctor `Q` of the Quot presheaf of the
Quot situation `F'/U'/W'` is represented over `W'` by a scheme separated and of finite
presentation over `W'`, then for every morphism `w : W ⟶ W'` of the site the subfunctor
`Q ×_{W'} W` of the Quot presheaf of the base change to `W` is represented over `W`, by the
fibre product `Z' ×_{W'} W`. -/
theorem isRepresentedSeparatedFinitePresentation_baseChangeSubfunctor
    {U' W' W : BigFppfOver B integerBase ℤS} {q' : U' ⟶ W'}
    {hq' : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q').hom}
    {F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2}
    {hF' : F'.IsQuasicoherentOnSite} (w : W ⟶ W')
    {Q : Subfunctor (schemeQuotSituation q' hq' F' hF').quotSitePresheaf}
    (hQ : (schemeQuotSituation q' hq' F' hF').IsRepresentedSeparatedFinitePresentation W' (𝟙 _)
      Q) :
    ((schemeQuotSituation q' hq' F' hF').canonicalBaseChanged
        (schemeSpaceMap w)).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q' hq' F' hF').baseChangeSubfunctor (schemeSpaceMap w) Q) := by
  let D' := schemeQuotSituation q' hq' F' hF'
  obtain ⟨Z', r', e', he', hsep, hlfp, hqc⟩ := hQ
  have sq : IsPullback (pullback.fst r' w) (pullback.snd r' w) r' w :=
    IsPullback.of_hasPullback r' w
  let Φ := (Functor.whiskeringRight (BigFppfOver B integerBase ℤS)ᵒᵖ (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1, u}
  have sq' := (sq.map yoneda).map Φ
  have sq'' : IsPullback (Φ.map (yoneda.map (pullback.fst r' w)) ≫ e'.hom)
      (Φ.map (yoneda.map (pullback.snd r' w))) (Q.ι ≫ D'.quotSitePresheafToBase)
      (Φ.map (yoneda.map w)) := by
    refine sq'.of_iso (Iso.refl _) e' (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp
    · refine (Category.comp_id _).trans (Eq.trans ?_ he'.symm)
      ext T x
      rfl
    · exact Category.comp_id _
  let e := sq''.isoIsPullback _ _ (D'.isPullback_baseChangeSubfunctor (schemeSpaceMap w) Q)
  refine ⟨pullback r' w, pullback.snd r' w, e, ?_,
    toScheme_map_of_isPullback (P := @_root_.AlgebraicGeometry.IsSeparated) inferInstance sq hsep,
    toScheme_map_of_isPullback (P := @LocallyOfFinitePresentation) inferInstance sq hlfp,
    toScheme_map_of_isPullback (P := @QuasiCompact) inferInstance sq hqc⟩
  have := IsPullback.isoIsPullback_hom_snd _ _ sq'' (D'.isPullback_baseChangeSubfunctor
    (schemeSpaceMap w) Q)
  refine this.trans ?_
  ext T x
  rfl

/-- The inverse image of `𝒪(1)` on `h_W × ℙⁿ_ℤ` along `h_{ℙⁿ_W} ≅ h_W × ℙⁿ_ℤ` is its inverse
image along the morphism `ℙⁿ_W ⟶ ℙⁿ_ℤ`: the composite of the identification with the first
projection is the morphism of algebraic spaces represented by `ℙⁿ_W ⟶ ℙⁿ_ℤ`. -/
theorem projectiveSiteProductIso_hom_productFst (n : ℕ) (W : BigFppfOver B integerBase ℤS) :
    (projectiveSiteProductIso n W).hom ≫ productFst n (schemeSpace W) =
      schemeSpaceMap (projectiveSiteMap B n (toSiteBase B W)) := by
  unfold projectiveSiteProductIso
  exact IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- **`i^*𝒪(1)` is the inverse image of `𝒪(1)` along `U ⟶ ℙⁿ_W ⟶ ℙⁿ_ℤ`.** -/
def projectiveTwistIso {U W : BigFppfOver B integerBase ℤS} {n : ℕ}
    (i : U ⟶ projectiveSite B n W) :
    projectiveTwist i ≅ (modulePullback B integerBase ℤS
      (schemeSpaceMap (i ≫ projectiveSiteMap B n (toSiteBase B W)))).obj (twistingModuleBase B n) :=
  ((modulePullbackCompIso B integerBase ℤS (schemeSpaceMap i ≫ (projectiveSiteProductIso n W).hom)
      (productFst n (schemeSpace W))).app (twistingModuleBase B n)) ≪≫
    eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj (twistingModuleBase B n))
      (by
        rw [Category.assoc, projectiveSiteProductIso_hom_productFst]
        exact ObjectProperty.hom_ext _ (yoneda.map_comp _ _).symm))

/-- The morphisms `ℙⁿ_{W} ⟶ ℙⁿ_{W'} ⟶ ℙⁿ_ℤ` and `ℙⁿ_W ⟶ ℙⁿ_ℤ` agree. -/
theorem projectiveSiteMap_comp_toSiteBase {n : ℕ} {W W' : BigFppfOver B integerBase ℤS}
    (w : W ⟶ W') :
    projectiveSiteMap B n w ≫ projectiveSiteMap B n (toSiteBase B W') =
      projectiveSiteMap B n (toSiteBase B W) := by
  rw [show toSiteBase B W = w ≫ toSiteBase B W' from (isTerminal_siteBase B).hom_ext _ _]
  apply (𝒯).map_injective
  rw [Functor.map_comp]
  exact (projectiveSpaceOverMap_comp n _ _).trans
    (congrArg (projectiveSpaceOverMap n) ((𝒯).map_comp _ _).symm)

/-- **Representability of `Quot^P` along a cartesian square of schemes of the site.** Let
`q' : U' ⟶ W'` be separated, `i' : U' ⟶ ℙⁿ_{W'}`, `F'` quasi-coherent on `h_{U'}`, and let `g`,
`q`, `q'`, `w` be a cartesian square of the site, with `i : U ⟶ ℙⁿ_W` satisfying
`g ≫ i' = i ≫ (ℙⁿ_W ⟶ ℙⁿ_{W'})` and `F ≅ g^* F'`. If `Quot^{P, i'^*𝒪(1)}_{F'/U'/W'}` is represented
by a scheme separated and of finite presentation over `W'`, then `Quot^{P, i^*𝒪(1)}_{F/U/W}` is
represented by a scheme separated and of finite presentation over `W`. -/
theorem isRepresentedSeparatedFinitePresentation_of_isPullback
    {W U W' U' : BigFppfOver B integerBase ℤS} {n : ℕ}
    {q : U ⟶ W} (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    {F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2}
    (hF : F.IsQuasicoherentOnSite) (i : U ⟶ projectiveSite B n W)
    {q' : U' ⟶ W'} (hq' : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q').hom)
    (hsep' : _root_.AlgebraicGeometry.IsSeparated ((𝒯).map q'))
    {F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2}
    (hF' : F'.IsQuasicoherentOnSite) (i' : U' ⟶ projectiveSite B n W')
    (w : W ⟶ W') (g : U ⟶ U') (hsq : IsPullback g q q' w)
    (hi : g ≫ i' = i ≫ projectiveSiteMap B n w)
    (e : F ≅ (modulePullback B integerBase ℤS (schemeSpaceMap g)).obj F') (P : ℤ → ℤ)
    (h : (schemeQuotSituation q' hq' F' hF').IsRepresentedSeparatedFinitePresentation W' (𝟙 _)
      ((schemeQuotSituation q' hq' F' hF').hilbertPolynomialQuot (projectiveTwist i') P)) :
    (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot (projectiveTwist i) P) := by
  let D' := schemeQuotSituation q' hq' F' hF'
  let D := schemeQuotSituation q hq F hF
  let ξ : schemeSpace W ⟶ D'.Y := schemeSpaceMap w
  let D'' := D'.canonicalBaseChanged ξ
  have h1 := isRepresentedSeparatedFinitePresentation_baseChangeSubfunctor w h
  rw [D'.baseChangeSubfunctor_hilbertPolynomialQuot] at h1
  have hsq' : IsPullback (schemeSpaceMap g) (schemeSpaceMap q) D'.f ξ :=
    CurveFamily.isPullback_schemeSpaceMap_of_isPullback hsq
  let ι : D''.X ≅ schemeSpace U :=
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS D'.f ξ).isoIsPullback _ _ hsq'
  have hι₁ : ι.hom ≫ schemeSpaceMap g = D'.baseChangedSourceProjection ξ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hι₂ : ι.hom ≫ schemeSpaceMap q = D''.f := IsPullback.isoIsPullback_hom_snd _ _ _ _
  have : IsIso ι.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso ι).hom)
  have hιci : IsClosedImmersion B integerBase ℤS ι.hom.hom :=
    isClosedImmersion_of_isIso B integerBase ℤS ι.hom.hom
  have hsepq' : IsSeparated B integerBase ℤS (schemeSpaceMap q').hom :=
    (isSeparated_yoneda_map_iff B integerBase ℤS q').2 hsep'
  have hsepW : IsSeparated B integerBase ℤS D''.f.hom :=
    isSeparated_of_isPullback B integerBase ℤS (IsPullback.of_hasPullback D'.f.hom ξ.hom) hsepq'
  have hsepU : IsSeparated B integerBase ℤS (schemeSpaceMap q).hom :=
    isSeparated_of_isPullback B integerBase ℤS (hsq.map yoneda) hsepq'
  let PS : QuotPushforwardSituation B integerBase ℤS :=
    { base := schemeSpace W
      X := D''.X
      Y := schemeSpace U
      π := ι.hom
      structureX := D''.f
      structureY := schemeSpaceMap q
      comp := hι₂
      F := D''.F
      quasicoherent := D''.quasicoherent
      affine := isAffineHom_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci
      quasiFinite := isQuasiFinite_of_isFinite B integerBase ℤS ι.hom.hom D''.X.2 (schemeSpace U).2
        (isFinite_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci)
      separatedX := hsepW
      separatedY := hsepU
      finitePresentationX := D''.finitePresentation
      finitePresentationY := hq }
  -- the two inverse images of `𝒪(1)` on `X' ×_{W'} W`
  have hmaps : ι.hom ≫ schemeSpaceMap (i ≫ projectiveSiteMap B n (toSiteBase B W)) =
      D'.baseChangedSourceProjection ξ ≫
        schemeSpaceMap (i' ≫ projectiveSiteMap B n (toSiteBase B W')) := by
    rw [← hι₁, Category.assoc]
    congr 1
    refine ObjectProperty.hom_ext _ ?_
    show yoneda.map (i ≫ _) = yoneda.map g ≫ yoneda.map (i' ≫ _)
    rw [← yoneda.map_comp, ← Category.assoc, hi, Category.assoc,
      projectiveSiteMap_comp_toSiteBase]
  let O := twistingModuleBase B n
  let c := schemeSpaceMap (i ≫ projectiveSiteMap B n (toSiteBase B W))
  let c' := schemeSpaceMap (i' ≫ projectiveSiteMap B n (toSiteBase B W'))
  let p₁ := D'.baseChangedSourceProjection ξ
  let eL₁ : (modulePullback B integerBase ℤS ι.hom).obj (projectiveTwist i) ≅
      (modulePullback B integerBase ℤS ι.hom).obj ((modulePullback B integerBase ℤS c).obj O) :=
    (modulePullback B integerBase ℤS ι.hom).mapIso (projectiveTwistIso i)
  let eL₂ :
      (modulePullback B integerBase ℤS ι.hom).obj ((modulePullback B integerBase ℤS c).obj O) ≅
        (modulePullback B integerBase ℤS (ι.hom ≫ c)).obj O :=
    (modulePullbackCompIso B integerBase ℤS ι.hom c).app O
  let eL₃ : (modulePullback B integerBase ℤS (ι.hom ≫ c)).obj O ≅
      (modulePullback B integerBase ℤS (p₁ ≫ c')).obj O :=
    eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj O) hmaps)
  let eL₄ : (modulePullback B integerBase ℤS (p₁ ≫ c')).obj O ≅
      (modulePullback B integerBase ℤS p₁).obj ((modulePullback B integerBase ℤS c').obj O) :=
    ((modulePullbackCompIso B integerBase ℤS p₁ c').app O).symm
  let eL₅ : (modulePullback B integerBase ℤS p₁).obj ((modulePullback B integerBase ℤS c').obj O) ≅
      (modulePullback B integerBase ℤS p₁).obj (projectiveTwist i') :=
    (modulePullback B integerBase ℤS p₁).mapIso (projectiveTwistIso i').symm
  let eL := eL₁ ≪≫ eL₂ ≪≫ eL₃ ≪≫ eL₄ ≪≫ eL₅
  -- the module: `F ≅ ι_* F''`
  let G := (modulePushforward B integerBase ℤS ι.hom).obj D''.F
  have hG : G.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePushforward_of_isIso B integerBase ℤS ι.symm D''.F
      D''.quasicoherent
  have hgι : ι.inv ≫ D'.baseChangedSourceProjection ξ = schemeSpaceMap g := by
    rw [← hι₁, Iso.inv_hom_id_assoc]
  let eG₁ : G ≅ (modulePullback B integerBase ℤS ι.inv).obj D''.F :=
    (modulePushforwardInvIsoModulePullback B integerBase ℤS ι.symm).app D''.F
  let eG₂ : (modulePullback B integerBase ℤS ι.inv).obj
        ((modulePullback B integerBase ℤS (D'.baseChangedSourceProjection ξ)).obj F') ≅
      (modulePullback B integerBase ℤS (ι.inv ≫ D'.baseChangedSourceProjection ξ)).obj F' :=
    (modulePullbackCompIso B integerBase ℤS ι.inv (D'.baseChangedSourceProjection ξ)).app F'
  let eG₃ : (modulePullback B integerBase ℤS (ι.inv ≫ D'.baseChangedSourceProjection ξ)).obj F' ≅
      (modulePullback B integerBase ℤS (schemeSpaceMap g)).obj F' :=
    eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj F') hgι)
  let eF : F ≅ G := e ≪≫ (eG₁ ≪≫ eG₂ ≪≫ eG₃).symm
  let φ : D.F ⟶ G := eF.hom
  have : IsIso φ := eF.isIso_hom
  let i₁ := PS.directImageHilbertPolynomialQuotIso hιci (projectiveTwist i) P
  let i₂ := D.hilbertPolynomialQuotWithModuleIso (hG := hG) φ (projectiveTwist i) P
  have h2 := IsRepresentedSeparatedFinitePresentation.of_eq
    (hilbertPolynomialQuot_congr (D := D'') _ (hL := isInvertible_modulePullback B integerBase ℤS
      (D'.baseChangedSourceProjection ξ) (projectiveTwist i'))
      (hL' := isInvertible_modulePullback B integerBase ℤS ι.hom (projectiveTwist i))
      eL.symm P) h1
  refine IsRepresentedSeparatedFinitePresentation.of_iso (D := D'') (D' := D)
    (Q' := D.hilbertPolynomialQuot (projectiveTwist i) P) (𝟙 _) (Category.comp_id _)
    (i₁ ≪≫ i₂) ?_ h2
  ext T x
  rfl

end AlgebraicGeometry.Space.QuotSituation

end
