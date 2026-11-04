/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotSchemeSituationRepresented
public import StacksFrontier.AlgebraicGeometry.Quot.C1746Private.QuotSeparatedFinitePresentationReduction
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType

/-!
# `Quot^P` over an affine base for a relatively ample invertible module (Stacks 0DPD)

Let `F/X/B` be a Quot situation with `f : X ⟶ B` separated and of finite presentation, `F` of
finite presentation, `L` an invertible `𝒪_X`-module ample on `X/B` (Stacks 0D31) and `P` a
numerical polynomial. Over an affine scheme `W` over `B` the base change `X_W` is the algebraic
space of a scheme `U` (a relatively ample `L` makes `f` representable), `L_U` is ample
(Stacks 01VK), and Stacks 01VS gives an immersion `i : U ⟶ ℙⁿ_W` over `W` with
`L_U^{⊗ d} ≅ i^*𝒪(1)`. Replacing `(L, P(t))` by `(L^{⊗ d}, P(dt))` (Stacks 0DP8) and transporting
along `X_W ≅ h_U` (Stacks 0DP4 for an isomorphism), `Quot^{P, L_W}_{F_W/X_W/W}` becomes
`Quot^{P(d·), i^*𝒪(1)}_{F_U/U/W}`. This file carries out that reduction, as in the proof of
Stacks 0DPC with an immersion in place of a closed immersion; the representability of the
latter by a scheme separated and of finite presentation over `W` is its hypothesis `hA`.

## Main results

* `Space.QuotSituation.exists_immersion_projectiveSite_of_isRelativelyAmple`:
  Stacks 01VS for a relatively ample affine base change.
* `Space.QuotSituation.isRepresentedSeparatedFinitePresentation_canonicalBaseChanged`:
  the reduction.

## References

* [Stacks Project, Tag 0DPD](https://stacks.math.columbia.edu/tag/0DPD)
* [Stacks Project, Tag 01VS](https://stacks.math.columbia.edu/tag/01VS)
* [Stacks Project, Tag 0DP8](https://stacks.math.columbia.edu/tag/0DP8)
* [Stacks Project, Tag 0DP4](https://stacks.math.columbia.edu/tag/0DP4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space.QuotSituation

open ProjectiveQuot ProjectiveQuotOverSpace Stacks.AmpleProjectiveImmersion

variable {B : BigFppfSite.{u}}

local notation "ℤS" => B.contains_integerBase

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The base change of a morphism of finite presentation along `h_W ⟶ Y` is again of finite
presentation, when it is a morphism of representables. -/
private theorem isFinitePresentation_yoneda_map_of_isPullback
    {X Y : AlgebraicSpaces B integerBase ℤS} {f : X ⟶ Y}
    (hf : IsFinitePresentation B integerBase ℤS f.hom) {W U : BigFppfOver B integerBase ℤS}
    {ξ : yoneda.obj W ⟶ Y.1} {p : yoneda.obj U ⟶ X.1} {q : U ⟶ W}
    (hsq : IsPullback p (yoneda.map q) f.hom ξ) :
    IsFinitePresentation B integerBase ℤS (yoneda.map q) :=
  (isFinitePresentation_isStableUnderBaseChange B integerBase ℤS).of_isPullback
    (isPullback_homMk B integerBase ℤS X.2 (isAlgebraicSpace_yoneda B integerBase ℤS W)
      Y.2 (isAlgebraicSpace_yoneda B integerBase ℤS U) hsq) hf

/-- **Stacks 01VS for a relatively ample affine base change.** For `f : X ⟶ Y` of finite
presentation, `L` ample on `X/Y` and a cartesian square exhibiting `X ×_Y W` as a scheme `U` over
an affine scheme `W`, the reading `L_U` of `L` on `U` is invertible and some power `L_U^{⊗ d}`,
`d ≥ 1`, is the inverse image of `𝒪(1)` along an immersion `U ⟶ ℙⁿ_W` over `W`. -/
theorem exists_immersion_projectiveSite_of_isRelativelyAmple
    {X Y : AlgebraicSpaces B integerBase ℤS} {f : X ⟶ Y}
    (hf : IsFinitePresentation B integerBase ℤS f.hom)
    {L : Modules.{u, u} B integerBase ℤS X.1 X.2} (hL : IsRelativelyAmple B integerBase ℤS f L)
    (W U : BigFppfOver B integerBase ℤS) (hW : IsAffine ((𝒯).obj W))
    (ξ : yoneda.obj W ⟶ Y.1) (p : yoneda.obj U ⟶ X.1) (q : U ⟶ W)
    (hsq : IsPullback p (yoneda.map q) f.hom ξ) :
    ∃ _ : Stacks.Ample.IsInvertibleModule ((𝒯).obj U) (baseChangeModule B integerBase ℤS L U p),
      ∃ (n : ℕ) (d : ℕ) (_ : 1 ≤ d) (i : U ⟶ projectiveSite B n W),
        _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) ∧
        i ≫ projectiveSiteStructure B n W = q ∧
        Nonempty (Stacks.Ample.tensorPowModule ((𝒯).obj U)
            (baseChangeModule B integerBase ℤS L U p) (d : ℤ) ≅
          (Scheme.Modules.pullback ((𝒯).map i)).obj
            (projectiveSpaceTwistingSheaf n ((𝒯).obj W))) := by
  obtain ⟨hinv, hamp⟩ := isAmple_baseChangeModule_of_isRelativelyAmple hL W U hW ξ p q hsq
  have hq := isFinitePresentation_yoneda_map_of_isPullback hf hsq
  have : LocallyOfFiniteType ((𝒯).map q) :=
    (isLocallyOfFiniteType_yoneda_map_iff B integerBase ℤS q).1
      (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B integerBase ℤS hq.1)
  obtain ⟨d₀, hd₀, h⟩ := Stacks.StalkwiseGeneration.exists_immersion_projectiveSpaceOver_of_isAmple
    ((𝒯).map q) _ hamp
  obtain ⟨n, i, hi, hover, ⟨e⟩⟩ := h d₀ le_rfl
  refine ⟨hinv, n, d₀, hd₀, CurveFamily.homOfScheme i, hi, ?_, ⟨e⟩⟩
  exact (𝒯).map_injective (by rw [Functor.map_comp]; exact hover)

/-- **Stacks 0DP4 transports representability back along a closed immersion.** If
`Quot^{P, M}_{π_*F/Y/B}` is represented over `W`, so is `Quot^{P, π^*M}_{F/X/B}`. -/
private theorem isRepresented_sourceSituation
    (PS : QuotPushforwardSituation B integerBase ℤS)
    (hπ : IsClosedImmersion B integerBase ℤS PS.π.hom)
    (M : Modules.{u, u} B integerBase ℤS PS.Y.1 PS.Y.2)
    [hM : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS PS.Y.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS PS.Y.1 PS.Y.2).O)).property M]
    (P : ℤ → ℤ) {W : BigFppfOver B integerBase ℤS} {ν : yoneda.obj W ⟶ PS.base.obj}
    (h : PS.directImageSituation.IsRepresentedSeparatedFinitePresentation W ν
      (PS.directImageSituation.hilbertPolynomialQuot M (hL := hM) P)) :
    PS.sourceSituation.IsRepresentedSeparatedFinitePresentation W ν
      (PS.sourceSituation.hilbertPolynomialQuot ((modulePullback B integerBase ℤS PS.π).obj M)
        (hL := isInvertible_modulePullback B integerBase ℤS PS.π M) P) := by
  let Φ := PS.directImageHilbertPolynomialQuotIso hπ M P
  refine IsRepresentedSeparatedFinitePresentation.of_iso (D := PS.directImageSituation)
    (D' := PS.sourceSituation) (𝟙 _) (Category.comp_id _) Φ.symm ?_ h
  ext T z
  show ULift.up (yonedaEquiv (Φ.inv.app T z).1.toBase.hom) =
    ULift.up (yonedaEquiv z.1.toBase.hom)
  rw [← PS.directImageHilbertPolynomialQuotIso_hom_app_toBase hπ M P (Φ.inv.app T z)]
  exact congrArg (fun y => ULift.up.{u + 1} (yonedaEquiv y.1.toBase.hom))
    (types_congr_hom (Φ.inv_hom_id_app T) z)

/-- The direct image along the inverse of an isomorphism preserves modules of finite
presentation. -/
private theorem isFinitePresentationOnSite_modulePushforward_of_isIso
    {X Y : AlgebraicSpaces B integerBase ℤS} (e : X ≅ Y)
    (F : Modules.{u, u} B integerBase ℤS Y.1 Y.2)
    (hF : SheafOfModules.IsFinitePresentationOnSite F) :
    SheafOfModules.IsFinitePresentationOnSite ((modulePushforward B integerBase ℤS e.inv).obj F) :=
  .of_iso ((modulePushforwardInvIsoModulePullback B integerBase ℤS e).app F).symm
    (isFinitePresentationOnSite_modulePullback B integerBase ℤS e.hom F hF)

/-- **Stacks 0DP8 for an immersion into `ℙⁿ`.** Let `i : U ⟶ ℙⁿ_W` be an immersion over an
affine scheme `W` and `M₀` an invertible module on `h_U` with `M₀^{⊗ d} ≅ i^*𝒪(1)`, `d ≥ 1`. Under
the hypothesis `hA`, `Quot^{P, M₀}_{F/U/W}` is represented over `W` for every finitely presented
quasi-coherent `F` on `h_U`. -/
private theorem isRepresented_schemeQuotSituation_of_tensorPowModule
    (hA : ∀ (W' U' : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U' ⟶ W')
      (i : U' ⟶ projectiveSite B n W'), IsAffine ((𝒯).obj W') →
      _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) →
      i ≫ projectiveSiteStructure B n W' = q →
      ∀ (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
        (F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2)
        (hF' : F'.IsQuasicoherentOnSite), SheafOfModules.IsFinitePresentationOnSite F' →
      ∀ (P' : ℤ → ℤ) (p' : Polynomial ℚ), (∀ m : ℤ, p'.eval (m : ℚ) = (P' m : ℚ)) →
        (schemeQuotSituation q hq F' hF').IsRepresentedSeparatedFinitePresentation W' (𝟙 _)
          ((schemeQuotSituation q hq F' hF').hilbertPolynomialQuot (projectiveTwist i) P'))
    {W U : BigFppfOver B integerBase ℤS} {n : ℕ} {q : U ⟶ W} {i : U ⟶ projectiveSite B n W}
    (hW : IsAffine ((𝒯).obj W)) (hi : _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i))
    (hiq : i ≫ projectiveSiteStructure B n W = q)
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    (hF : F.IsQuasicoherentOnSite) (hFfp : SheafOfModules.IsFinitePresentationOnSite F)
    (M₀ : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
    [hM₀ : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (schemeSpace U).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (schemeSpace U).1 (schemeSpace U).2).O)).property M₀]
    (hM₀qc : M₀.IsQuasicoherentOnSite)
    [hN : Stacks.Ample.IsInvertibleModule ((𝒯).obj U)
      (restrictToChartScheme B integerBase ℤS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (idEtaleChart B integerBase ℤS U))]
    {d : ℕ} (hd : 1 ≤ d)
    (e : Stacks.Ample.tensorPowModule ((𝒯).obj U)
        (restrictToChartScheme B integerBase ℤS (yoneda.obj U)
          (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (idEtaleChart B integerBase ℤS U))
        (d : ℤ) ≅
      (Scheme.Modules.pullback ((𝒯).map i)).obj (projectiveSpaceTwistingSheaf n ((𝒯).obj W)))
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
      ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot M₀ (hL := hM₀) P) := by
  let M := (modulePullback B integerBase ℤS (productFst n (schemeSpace W))).obj
    (twistingModuleBase B n)
  have hM : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (productSpace n (schemeSpace W)).1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (productSpace n (schemeSpace W)).1 (productSpace n (schemeSpace W)).2).O)).property M :=
    stacksIsInvertible_modulePullback_obj B integerBase ℤS
      (productFst n (schemeSpace W)) (twistingModuleBase B n)
  have hMqc : M.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_of_isInvertible B integerBase ℤS _ M
      (Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ hM)
  have hM₀' : Stacks.SheafOfModules.IsInvertible
      (structurePresheaf B integerBase ℤS (yoneda.obj U))
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B integerBase ℤS
        (yoneda.obj U) (isAlgebraicSpace_yoneda B integerBase ℤS U)).O)).property M₀ := hM₀
  let eL : projectiveTwist i ≅
      invertibleTensorPower B integerBase ℤS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B integerBase ℤS U) M₀ (d : ℤ) :=
    modulePullbackProjectiveSiteIso i M hMqc (isoReadingTwistingModuleIso n W) ≪≫
      (associatedSpaceModule U).mapIso e.symm ≪≫
      (invertibleTensorPowerAssociatedIso U M₀ (hM₀ := hM₀') hM₀qc (hN := hN) (d : ℤ)).symm
  have hP' : ∀ m : ℤ, (p.comp (Polynomial.C (d : ℚ) * Polynomial.X)).eval (m : ℚ) =
      ((fun m => P ((d : ℤ) * m)) m : ℚ) := fun m => by
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    exact_mod_cast hP ((d : ℤ) * m)
  have hd' : ((d : ℕ) : ℤ) ≠ 0 := by omega
  let DS := schemeQuotSituation q hq F hF
  exact IsRepresentedSeparatedFinitePresentation.of_eq
    ((hilbertPolynomialQuot_congr DS (projectiveTwist i)
        (hL' := isInvertible_invertibleTensorPower B integerBase ℤS _ _ M₀ (d : ℤ)) eL
        (fun m => P ((d : ℤ) * m))).trans
      (hilbertPolynomialQuot_invertibleTensorPower DS M₀ (hL := hM₀) hP hd'))
    (hA W U n q i hW hi hiq hq F hF hFfp _ _ hP')

/-- **Transport of `Quot^P` along `X_W ≅ h_U`.** Let `x : h_U ⟶ X` and `q : U ⟶ W` exhibit `h_U`
as the base change of `X ⟶ B` along `ξ : h_W ⟶ B`. If `Quot^{P, x^*L}_{F'/U/W}` is represented
over `W` for every finitely presented quasi-coherent `F'` on `h_U`, then so is
`Quot^{P, L_W}_{F_W/X_W/W}`. -/
private theorem isRepresented_canonicalBaseChanged_of_isPullback
    (D : QuotSituation B integerBase ℤS) (hsep : IsSeparated B integerBase ℤS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    (P : ℤ → ℤ) {W U : BigFppfOver B integerBase ℤS} (ξ : yoneda.obj W ⟶ D.Y.obj)
    (x : yoneda.obj U ⟶ D.X.1) (q : U ⟶ W) (hsq : IsPullback x (yoneda.map q) D.f.hom ξ)
    (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
    (h : ∀ (F : Modules.{u, u} B integerBase ℤS (schemeSpace U).1 (schemeSpace U).2)
      (hF : F.IsQuasicoherentOnSite), SheafOfModules.IsFinitePresentationOnSite F →
      (schemeQuotSituation q hq F hF).IsRepresentedSeparatedFinitePresentation W (𝟙 _)
        ((schemeQuotSituation q hq F hF).hilbertPolynomialQuot
          ((modulePullback B integerBase ℤS (ObjectProperty.homMk x : schemeSpace U ⟶ D.X)).obj L)
          (hL := isInvertible_modulePullback B integerBase ℤS
            (ObjectProperty.homMk x : schemeSpace U ⟶ D.X) L) P)) :
    IsRepresentedSeparatedFinitePresentation
      (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) W (𝟙 _)
      (@hilbertPolynomialQuot B integerBase ℤS
        (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
        ((modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
        (isInvertible_modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P) := by
  let ξ' : schemeSpace W ⟶ D.Y := ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ
  let DW := D.canonicalBaseChanged ξ'
  let x' : schemeSpace U ⟶ D.X := ObjectProperty.homMk x
  have hsq' : IsPullback x' (schemeSpaceMap q) D.f ξ' :=
    isPullback_homMk B integerBase ℤS D.X.2 (isAlgebraicSpace_yoneda B integerBase ℤS W) D.Y.2
      (isAlgebraicSpace_yoneda B integerBase ℤS U) hsq
  let ι : DW.X ≅ schemeSpace U :=
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase ℤS D.f ξ').isoIsPullback _ _ hsq'
  have hι : ι.hom ≫ x' = D.baseChangedSourceProjection ξ' :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have : IsIso ι.hom.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).mapIso ι).hom)
  have hιci : IsClosedImmersion B integerBase ℤS ι.hom.hom :=
    isClosedImmersion_of_isIso B integerBase ℤS ι.hom.hom
  let PS : QuotPushforwardSituation B integerBase ℤS :=
    { base := schemeSpace W
      X := DW.X
      Y := schemeSpace U
      π := ι.hom
      structureX := DW.f
      structureY := schemeSpaceMap q
      comp := IsPullback.isoIsPullback_hom_snd _ _ _ _
      F := DW.F
      quasicoherent := DW.quasicoherent
      affine := isAffineHom_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci
      quasiFinite := isQuasiFinite_of_isFinite B integerBase ℤS ι.hom.hom DW.X.2 (schemeSpace U).2
        (isFinite_of_isClosedImmersion B integerBase ℤS ι.hom.hom hιci)
      separatedX :=
        isSeparated_of_isPullback B integerBase ℤS (IsPullback.of_hasPullback D.f.hom ξ'.hom) hsep
      separatedY := isSeparated_of_isPullback B integerBase ℤS hsq hsep
      finitePresentationX := DW.finitePresentation
      finitePresentationY := hq }
  have h₃ := isRepresented_sourceSituation PS hιci _
    (hM := isInvertible_modulePullback B integerBase ℤS x' L) P
    (h _ (isQuasicoherentOnSite_modulePushforward_of_isIso B integerBase ℤS ι.symm DW.F
        DW.quasicoherent)
      (isFinitePresentationOnSite_modulePushforward_of_isIso ι.symm DW.F
        (isFinitePresentationOnSite_modulePullback B integerBase ℤS _ D.F hFfp)))
  let e₀ : (modulePullback B integerBase ℤS ι.hom).obj
        ((modulePullback B integerBase ℤS x').obj L) ≅
      (modulePullback B integerBase ℤS (D.baseChangedSourceProjection ξ')).obj L :=
    (modulePullbackCompIso B integerBase ℤS ι.hom x').app L ≪≫
      eqToIso (congrArg (fun k => (modulePullback B integerBase ℤS k).obj L) hι)
  exact IsRepresentedSeparatedFinitePresentation.of_eq (hilbertPolynomialQuot_congr (D := DW) _
    (hL := isInvertible_modulePullback B integerBase ℤS ι.hom _
      (hL := isInvertible_modulePullback B integerBase ℤS x' L))
    (hL' := isInvertible_modulePullback B integerBase ℤS (D.baseChangedSourceProjection ξ') L)
    e₀ P) h₃

/-- **The affine case of Stacks 0DPD, reduced to an immersion into `ℙⁿ`.** Let `F/X/B` be a Quot
situation with `X ⟶ B` separated, `F` of finite presentation, `L` an invertible `𝒪_X`-module
ample on `X/B` (Stacks 0D31) and `P` a numerical polynomial. Suppose (`hA`) that for every affine
scheme `W'` of the site, immersion `i : U' ⟶ ℙⁿ_{W'}` over `W'` with `U' ⟶ W'` of finite
presentation, finitely presented `F'` on `h_{U'}` and numerical `P'`, the subfunctor
`Quot^{P', i^*𝒪(1)}_{F'/U'/W'}` is represented by a scheme separated, locally of finite
presentation and quasi-compact over `W'`. Then for every affine scheme `W` with `ξ : h_W ⟶ B`, so
is `Quot^{P, L_W}_{F_W/X_W/W}`. -/
theorem isRepresentedSeparatedFinitePresentation_canonicalBaseChanged
    (hA : ∀ (W' U' : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U' ⟶ W')
      (i : U' ⟶ projectiveSite B n W'), IsAffine ((𝒯).obj W') →
      _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) →
      i ≫ projectiveSiteStructure B n W' = q →
      ∀ (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
        (F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2)
        (hF' : F'.IsQuasicoherentOnSite), SheafOfModules.IsFinitePresentationOnSite F' →
      ∀ (P' : ℤ → ℤ) (p' : Polynomial ℚ), (∀ m : ℤ, p'.eval (m : ℚ) = (P' m : ℚ)) →
        (schemeQuotSituation q hq F' hF').IsRepresentedSeparatedFinitePresentation W' (𝟙 _)
          ((schemeQuotSituation q hq F' hF').hilbertPolynomialQuot (projectiveTwist i) P'))
    (D : QuotSituation B integerBase ℤS) (hsep : IsSeparated B integerBase ℤS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase ℤS D.f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ))
    (W : BigFppfOver B integerBase ℤS) (ξ : yoneda.obj W ⟶ D.Y.obj)
    (hW : IsAffine ((𝒯).obj W)) :
    IsRepresentedSeparatedFinitePresentation
      (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) W (𝟙 _)
      (@hilbertPolynomialQuot B integerBase ℤS
        (D.canonicalBaseChanged (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))
        ((modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ))).obj L)
        (isInvertible_modulePullback B integerBase ℤS (D.baseChangedSourceProjection
          (ObjectProperty.homMk (Y := D.Y) (X := schemeSpace W) ξ)) L) P) := by
  have hrep := hamp.relativelyRepresentable
  let U := hrep.pullback ξ
  let x := hrep.fst ξ
  let q : U ⟶ W := hrep.snd ξ
  have hsq : IsPullback x (yoneda.map q) D.f.hom ξ := hrep.isPullback ξ
  obtain ⟨hN, n, d, hd, i, hi, hiq, ⟨e⟩⟩ :=
    exists_immersion_projectiveSite_of_isRelativelyAmple D.finitePresentation hamp W U hW ξ x q hsq
  let x' : schemeSpace U ⟶ D.X := ObjectProperty.homMk x
  have hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom :=
    isFinitePresentation_yoneda_map_of_isPullback D.finitePresentation hsq
  exact isRepresented_canonicalBaseChanged_of_isPullback D hsep hFfp L P ξ x q hsq hq
    fun F hF hFfp' => isRepresented_schemeQuotSituation_of_tensorPowModule hA hW hi hiq hq F hF
      hFfp' _ (hM₀ := isInvertible_modulePullback B integerBase ℤS x' L)
      (isQuasicoherentOnSite_modulePullback_of_isInvertible x' L hL) (hN := hN) hd e hP

/-- **Stacks 0DPD from its affine case.** Under the hypotheses of
`QuotSituation.isRepresentedSeparatedFinitePresentation_canonicalBaseChanged` (`X ⟶ B` separated
and of finite presentation, `F` of finite presentation, `L` ample on `X/B`, `P` numerical, and the
affine statement `hA` for immersions into `ℙⁿ`), `Quot^{P, L}_{F/X/B}` is an algebraic space
separated and of finite presentation over `B` (the reduction to affine bases is Stacks 03KG). -/
theorem isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_immersion
    (hA : ∀ (W' U' : BigFppfOver B integerBase ℤS) (n : ℕ) (q : U' ⟶ W')
      (i : U' ⟶ projectiveSite B n W'), IsAffine ((𝒯).obj W') →
      _root_.AlgebraicGeometry.IsImmersion ((𝒯).map i) →
      i ≫ projectiveSiteStructure B n W' = q →
      ∀ (hq : IsFinitePresentation B integerBase ℤS (schemeSpaceMap q).hom)
        (F' : Modules.{u, u} B integerBase ℤS (schemeSpace U').1 (schemeSpace U').2)
        (hF' : F'.IsQuasicoherentOnSite), SheafOfModules.IsFinitePresentationOnSite F' →
      ∀ (P' : ℤ → ℤ) (p' : Polynomial ℚ), (∀ m : ℤ, p'.eval (m : ℚ) = (P' m : ℚ)) →
        (schemeQuotSituation q hq F' hF').IsRepresentedSeparatedFinitePresentation W' (𝟙 _)
          ((schemeQuotSituation q hq F' hF').hilbertPolynomialQuot (projectiveTwist i) P'))
    (D : QuotSituation B integerBase ℤS) (hsep : IsSeparated B integerBase ℤS D.f.hom)
    (hFfp : SheafOfModules.IsFinitePresentationOnSite D.F)
    (L : Modules.{u, u} B integerBase ℤS D.X.1 D.X.2)
    [hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B integerBase ℤS D.X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B integerBase ℤS D.X.1 D.X.2).O)).property L]
    (hamp : IsRelativelyAmple B integerBase ℤS D.f L)
    {P : ℤ → ℤ} {p : Polynomial ℚ} (hP : ∀ m : ℤ, p.eval (m : ℚ) = (P m : ℚ)) :
    D.IsSeparatedFinitePresentationAlgebraicSpaceOver (D.hilbertPolynomialQuot L P) := by
  refine D.isSeparatedFinitePresentationAlgebraicSpaceOver_hilbertPolynomialQuot_of_represented
    L P fun W ξ hW => ?_
  obtain ⟨Z, r, e, he, hr⟩ :=
    isRepresentedSeparatedFinitePresentation_canonicalBaseChanged hA D hsep hFfp L hamp hP W ξ hW
  exact ⟨Z, r, e, he.trans (congrArg (fun k => Functor.whiskerRight k uliftFunctor.{u + 1, u})
    (Category.comp_id _)), hr⟩

end AlgebraicGeometry.Space.QuotSituation

end
