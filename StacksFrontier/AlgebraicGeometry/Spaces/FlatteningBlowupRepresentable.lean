module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningBlowupComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeIdealEtaleFittingDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget

/-!
# Flattening by blowing up: the case of a scheme over an algebraic space

This file assembles the proof of Stacks 087C, flattening by blowing up for algebraic spaces,
from the case of an affine base and the source a scheme, which is Stacks 0815 for schemes read
on algebraic spaces.  Given a surjective étale `φ : W ⟶ A` with `W` affine, the case of an affine
base flattens the pullback of the module to `X_W = X ×_A W` by a blowup of `W` in a centre
`Z_W`; Stacks 087B produces a centre `Z` on `A` with `φ⁻¹Z = Z_W + Z'`; and the blowup of `A` in
`Z` is the one sought, its base change to `W` being the blowup in `Z_W` followed by a blowup in
the inverse image of `Z'`.

## Main results

* `AlgebraicGeometry.Space.isRepresentableSpace_fiberProduct`: a fibre product of two schemes
  over an algebraic space is a scheme.
* `AlgebraicGeometry.Space.isPullback_restrictOverBaseChange` and
  `AlgebraicGeometry.Space.flatteningHypotheses_baseChange`: the hypotheses of Stacks 087C pass to
  the base change along an étale morphism from a quasi-compact space.
* `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isRepresentableSpace`: Stacks 087C for a
  source which is a scheme.
* `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_schemeCase`: Stacks 087C.

## References

* [Stacks Project, Tag 087C](https://stacks.math.columbia.edu/tag/087C)
* [Stacks Project, Tag 087B](https://stacks.math.columbia.edu/tag/087B)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 085S](https://stacks.math.columbia.edu/tag/085S)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 05VW](https://stacks.math.columbia.edu/tag/05VW)
-/

/- `exists_isFlatteningBlowup_of_schemeCase` below carries two hypotheses.  The first, `hscheme`,
is the case of an affine base, which is Stacks 0815 for schemes read on algebraic spaces; it is
discharged by `exists_isFlatteningBlowup_of_isAffineSpace`.  The second, `h07VR`, is the statement
of Stacks 07VR, the input of the form of Stacks 087B used here,
`exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces`; it is discharged by
`exists_integralFiniteSystem_of_isFinite`.  Stacks 0865 part (2) and 0868 part (1) are used
through `exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver` and need nothing further. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A fibre product of two schemes over an algebraic space is a scheme**: the diagonal of an
algebraic space is representable. -/
theorem isRepresentableSpace_fiberProduct {A X W : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (φ : W ⟶ A) (hX : IsRepresentableSpace B S hS X) (hW : IsRepresentableSpace B S hS W) :
    IsRepresentableSpace B S hS (AlgebraicSpaces.fiberProduct B S hS f φ) := by
  obtain ⟨T, ⟨eX⟩⟩ := hX
  obtain ⟨V, ⟨eW⟩⟩ := hW
  obtain ⟨a, snd, fst, h⟩ := relativelyRepresentable_of_isAlgebraicSpace B S hS A.2
    (eW.inv ≫ φ.hom) (eX.inv ≫ f.hom)
  have hpb : IsPullback (yoneda.map snd ≫ eX.inv) (fst ≫ eW.inv) f.hom φ.hom :=
    h.flip.of_iso (Iso.refl _) eX.symm eW.symm (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  exact ⟨a, ⟨hpb.isoPullback.symm⟩⟩

section BaseChange

variable {A X W : AlgebraicSpaces B S hS} (f : X ⟶ A) (φ : W ⟶ A) (U : OpenSubspaces B S hS A.1)

/-- The inverse image `U_W = φ⁻¹(U)` of an open subspace of `A` along `φ : W ⟶ A`. -/
abbrev OpenSubspaces.pullback : OpenSubspaces B S hS W.1 :=
  ⟨U.1.preimage φ.hom, isOpenSubspace_preimage B S hS φ.hom U.1 A.2 W.2 U.2⟩

/-- The morphism `U_W ⟶ U`. -/
abbrev OpenSubspaces.pullbackMap : (U.pullback φ).toSpace ⟶ U.toSpace :=
  ObjectProperty.homMk (U.1.fromPreimage φ.hom)

/-- The square formed by `U_W ⟶ U`, the inclusions of `U_W` and `U`, and `φ : W ⟶ A`
commutes. -/
theorem OpenSubspaces.pullbackMap_ι :
    U.pullbackMap φ ≫ U.toSpaceι = (U.pullback φ).toSpaceι ≫ φ :=
  ObjectProperty.hom_ext _ (Subfunctor.isPullback_preimage φ.hom U.1).w

/-- The morphism `(X_W)_{U_W} ⟶ X_U` of restrictions over the open subspaces. -/
noncomputable def restrictOverBaseChange :
    restrictOver (baseChangeHom f φ) (U.pullback φ) ⟶ restrictOver f U :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift
    (restrictOverι (baseChangeHom f φ) (U.pullback φ) ≫ baseChangeProj f φ)
    (restrictOverHom (baseChangeHom f φ) (U.pullback φ) ≫ U.pullbackMap φ)
    (by
      rw [Category.assoc, Category.assoc, (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ).w,
        OpenSubspaces.pullbackMap_ι, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ φ) (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (baseChangeHom f φ) (U.pullback φ).toSpaceι).w)

/-- `(X_W)_{U_W} ⟶ X_U` followed by the inclusion `X_U ⟶ X` is the inclusion
`(X_W)_{U_W} ⟶ X_W` followed by the projection `X_W ⟶ X`. -/
theorem restrictOverBaseChange_ι :
    restrictOverBaseChange f φ U ≫ restrictOverι f U =
      restrictOverι (baseChangeHom f φ) (U.pullback φ) ≫ baseChangeProj f φ :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift_fst _ _ _

/-- `(X_W)_{U_W} ⟶ X_U` followed by `X_U ⟶ U` is `(X_W)_{U_W} ⟶ U_W` followed by
`U_W ⟶ U`. -/
theorem restrictOverBaseChange_hom :
    restrictOverBaseChange f φ U ≫ restrictOverHom f U =
      restrictOverHom (baseChangeHom f φ) (U.pullback φ) ≫ U.pullbackMap φ :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι).lift_snd _ _ _

/-- `(X_W)_{U_W}` is `X_U ×_U U_W`. -/
theorem isPullback_restrictOverBaseChange :
    IsPullback (restrictOverBaseChange f φ U) (restrictOverHom (baseChangeHom f φ) (U.pullback φ))
      (restrictOverHom f U) (U.pullbackMap φ) := by
  have outer := (AlgebraicSpaces.isPullback_fiberProduct B S hS (baseChangeHom f φ)
    (U.pullback φ).toSpaceι).paste_horiz (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ)
  refine IsPullback.of_right ?_ (restrictOverBaseChange_hom f φ U)
    (AlgebraicSpaces.isPullback_fiberProduct B S hS f U.toSpaceι)
  rw [restrictOverBaseChange_ι, OpenSubspaces.pullbackMap_ι]
  exact outer

/-- The restriction over `U_W` of the pullback of `F` to `X_W` is the pullback of `F_U`. -/
noncomputable def restrictOverBaseChangeModuleIso (F : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS (restrictOverι (baseChangeHom f φ) (U.pullback φ))).obj
        ((modulePullback B S hS (baseChangeProj f φ)).obj F) ≅
      (modulePullback B S hS (restrictOverBaseChange f φ U)).obj
        ((modulePullback B S hS (restrictOverι f U)).obj F) :=
  ((modulePullbackCompIso B S hS _ (baseChangeProj f φ)).app F) ≪≫
    eqToIso (by rw [← restrictOverBaseChange_ι]) ≪≫
    ((modulePullbackCompIso B S hS (restrictOverBaseChange f φ U) (restrictOverι f U)).app F).symm

/-- **The hypotheses of Stacks 087C pass to a base change along an étale `φ : W ⟶ A`**, with
`W` quasi-compact and `A` quasi-separated: the base change `X_W ⟶ W` is locally of finite
presentation, `X_W` and `U_W` are quasi-compact if `X` and `U` are, the pullback of `F` to
`X_W` is quasi-coherent of finite type, and its restriction over `U_W` is of finite
presentation and flat over `U_W` (Stacks 05VW). -/
theorem flatteningHypotheses_baseChange (hZ : B.Contains (⊤_ Scheme.{u}))
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hφ : IsEtale B S hS φ.hom) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite) (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    IsQuasiCompactSpace B S hS (AlgebraicSpaces.fiberProduct B S hS f φ).1 ∧
      IsLocallyOfFinitePresentation B S hS (baseChangeHom f φ).hom ∧
      ((modulePullback B S hS (baseChangeProj f φ)).obj F).IsQuasicoherentOnSite ∧
      ((modulePullback B S hS (baseChangeProj f φ)).obj F).IsFiniteTypeOnSite ∧
      IsQuasiCompactSpace B S hS (U.pullback φ).1.toFunctor ∧
      ((modulePullback B S hS (restrictOverι (baseChangeHom f φ) (U.pullback φ))).obj
        ((modulePullback B S hS (baseChangeProj f φ)).obj F)).IsFinitePresentationOnSite ∧
      IsFlatOver B S hS (restrictOver (baseChangeHom f φ) (U.pullback φ)).2
        (restrictOverHom (baseChangeHom f φ) (U.pullback φ)).hom
        ((modulePullback B S hS (restrictOverι (baseChangeHom f φ) (U.pullback φ))).obj
          ((modulePullback B S hS (baseChangeProj f φ)).obj F)) := by
  have hφqc : IsQuasiCompact B S hS φ.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hWqc φ.hom
  have hψ : IsEtale B S hS (baseChangeProj f φ).hom :=
    isEtale_of_isPullback B S hS _ _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ).flip
      hφ
  have hψqc : IsQuasiCompact B S hS (baseChangeProj f φ).hom :=
    isQuasiCompact_of_isPullback B S hS (IsPullback.of_hasPullback f.hom φ.hom).flip hφqc
  have hφUqc : IsQuasiCompact B S hS (U.pullbackMap φ).hom :=
    isQuasiCompact_of_isPullback B S hS (Subfunctor.isPullback_preimage φ.hom U.1).flip hφqc
  have e := restrictOverBaseChangeModuleIso f φ U F
  have hκfp := isFinitePresentationOnSite_modulePullback B S hS (restrictOverBaseChange f φ U)
    _ hFUfp
  refine ⟨isQuasiCompactSpace_source_of_isQuasiCompact B S hS X.2 hXqc hψqc,
    (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
      (AlgebraicSpaces.isPullback_fiberProduct B S hS f φ) hf,
    isQuasicoherentOnSite_modulePullback_of_isEtale B S hS _ hψ F hFqc,
    isFiniteTypeOnSite_modulePullback B S hS _ F hFft,
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS U.2.1 hUqc hφUqc,
    SheafOfModules.IsFinitePresentationOnSite.of_iso e.symm hκfp, ?_⟩
  refine (isFlatOver_iff_of_iso B S hS _ _ e).2 ?_
  have := hFUfp
  have := hκfp
  exact isFlatOver_modulePullback B S hS (isPullback_restrictOverBaseChange f φ U) _ hFUflat

end BaseChange

/-- **Stacks 087C for a source which is a scheme, over the case of an affine base and Stacks
087B.**  Let `A` be quasi-compact and
quasi-separated, `U ⊆ A` a quasi-compact open subspace, and `f : X ⟶ A` locally of finite
presentation with `X` a quasi-compact scheme; let `F` be a quasi-coherent `𝒪_X`-module of finite
type with `F_U` of finite presentation and flat over `U`.  Then there is a flattening blowup.

This is the second paragraph of the proof of Stacks 087C.  Choose an affine scheme `W` with a
surjective étale `φ : W ⟶ A` (Stacks 03H6).  The case of an affine base (`hscheme`) applied to
`X_W ⟶ W` gives a centre `Z_W` on `W`; Stacks 087B, proved through Stacks 07VR (`h07VR`), gives
a centre `Z` on `A` with `φ⁻¹Z = Z_W + Z'`.  Over `W` the blowup in `Z_W + Z'` is the blowup in
`Z_W` followed by a further blowup, along which the strict transform stays flat and finitely
presented
(`AlgebraicGeometry.Space.exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver`); it is the
base change of the blowup `b` of `A` in `Z` (Stacks 085S), and the strict transform along `b`
is recognized on the étale cover
(`AlgebraicGeometry.Space.isFlatteningBlowup_of_baseChange`). -/
theorem exists_isFlatteningBlowup_of_isRepresentableSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hscheme : ∀ (A X : AlgebraicSpaces B S hS),
      IsAffineSpace B S hS A.1 → IsRepresentableSpace B S hS X →
      ∀ (f : X ⟶ A), IsQuasiCompactSpace B S hS X.1 →
        IsLocallyOfFinitePresentation B S hS f.hom →
      ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ (U : OpenSubspaces B S hS A.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
        ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite →
        IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
          ((modulePullback B S hS (restrictOverι f U)).obj F) →
      ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
        IsFlatteningBlowup f F U Z b)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X : AlgebraicSpaces B S hS} (hXrep : IsRepresentableSpace B S hS X) (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b := by
  obtain ⟨W₀, φ₀, hW₀, hφs, hφe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS A.1 A.2).1 hAqc
  let W : AlgebraicSpaces B S hS := ⟨yoneda.obj W₀, isAlgebraicSpace_yoneda B S hS W₀⟩
  let φ : W ⟶ A := ObjectProperty.homMk φ₀
  have hWqc : IsQuasiCompactSpace B S hS W.1 := isQuasiCompactSpace_yoneda_of_isAffine B S hS W₀ hW₀
  have hφsurj : IsSurjective B S hS φ.hom :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS A.1 A.2 W₀ φ₀).1 hφs
  have hφsep : IsSeparated B S hS φ.hom :=
    have := hW₀
    isSeparated_of_isEtale_of_scheme_isSeparated B S hS A.1 A.2 W₀ inferInstance φ₀ hφe
  have hφqc : IsQuasiCompact B S hS φ.hom :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ A.2 hAqs hWqc φ.hom
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    flatteningHypotheses_baseChange f φ U hZ hAqs hWqc hφe hXqc hf F hFqc hFft hUqc hFUfp hFUflat
  obtain ⟨ZW, W₁, c, hZWfp, hUZW, hc, hG₁fp, hG₁flat⟩ := hscheme W _ ⟨W₀, hW₀, ⟨Iso.refl _⟩⟩
    (isRepresentableSpace_fiberProduct f φ hXrep ⟨W₀, ⟨Iso.refl _⟩⟩) (baseChangeHom f φ) h1 h2
    _ h3 h4 (U.pullback φ) h5 h6 h7
  obtain ⟨Z, hZfp, hUZ, Z', hZ'fp, hsum⟩ :=
    exists_isFinitePresentation_preimageClosedSubspace_eq_sumClosedSubspaces h07VR hZ φ U hAqc
      hAqs hφqc hφsep hφe hUqc ZW hZWfp hUZW
  obtain ⟨W₂, c₂, hY, hNfp, hNflat⟩ :=
    exists_isBlowupAlong_sum_isFinitePresentation_isFlatOver (baseChangeHom f φ) _ Z' hZ'fp hc
      hG₁fp hG₁flat
  obtain ⟨A', b, hb⟩ := exists_isBlowupAlong Z
  have hφflat : IsFlat B S hS φ.hom := isFlat_of_isEtale B S hS hφe
  have h85S := isBlowupAlong_pullbackFst_of_isFlat hφflat hb
  rw [hsum] at h85S
  obtain ⟨ε, hε⟩ := hY.exists_iso h85S
  have hsq : IsPullback (c₂ ≫ c) (ε.hom ≫ pullback.snd φ b) φ b :=
    (IsPullback.of_hasPullback φ b).of_iso ε.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp [← hε]) (by simp) (by simp) (by simp)
  have hE : (sumClosedSubspaces B S hS W ZW Z').1.preimage (c₂ ≫ c).hom =
      (Z.1.preimage b.hom).preimage (ε.hom ≫ pullback.snd φ b).hom := by
    have h1 : (sumClosedSubspaces B S hS W ZW Z').1 = Z.1.preimage φ.hom := by
      rw [← hsum]; rfl
    rw [h1, ← Subfunctor.preimage_comp, ← Subfunctor.preimage_comp]
    exact congrArg (fun k => Z.1.preimage k) (congrArg InducedCategory.Hom.hom hsq.w)
  rw [hE] at hNfp hNflat
  exact ⟨Z, A', b, isFlatteningBlowup_of_baseChange hφe hφsurj hsq hZfp hUZ hb hNfp hNflat⟩

/-- **Stacks 087C, flattening by blowing up, over the case of an affine base (`hscheme`) and
Stacks 07VR (`h07VR`, through which Stacks 087B is proved).**  Let
`A` be a quasi-compact and quasi-separated algebraic space, let `f : X ⟶ A` be locally of finite
presentation with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module of finite type and
let `U ⊆ A` be a quasi-compact open subspace such that `F_U` is of finite presentation and flat
over `U`.  Then there is a `U`-admissible blowup `A' ⟶ A` such that the strict transform of `F`
is an `𝒪_{X ×_A A'}`-module of finite presentation, flat over `A'`.

The source is first replaced by a surjective étale chart which is a quasi-compact scheme
(`AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isRepresentableSpace_source`), and that
case is `AlgebraicGeometry.Space.exists_isFlatteningBlowup_of_isRepresentableSpace`. -/
theorem exists_isFlatteningBlowup_of_schemeCase (hZ : B.Contains (⊤_ Scheme.{u}))
    {A : AlgebraicSpaces B S hS} (hAqc : IsQuasiCompactSpace B S hS A.1)
    (hAqs : IsAbsolutelyQuasiSeparated B S hS hZ A.1) (U : OpenSubspaces B S hS A.1)
    (hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor)
    (hscheme : ∀ (A X : AlgebraicSpaces B S hS),
      IsAffineSpace B S hS A.1 → IsRepresentableSpace B S hS X →
      ∀ (f : X ⟶ A), IsQuasiCompactSpace B S hS X.1 →
        IsLocallyOfFinitePresentation B S hS f.hom →
      ∀ (F : Modules.{u, u} B S hS X.1 X.2), F.IsQuasicoherentOnSite → F.IsFiniteTypeOnSite →
      ∀ (U : OpenSubspaces B S hS A.1), IsQuasiCompactSpace B S hS U.1.toFunctor →
        ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite →
        IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
          ((modulePullback B S hS (restrictOverι f U)).obj F) →
      ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
        IsFlatteningBlowup f F U Z b)
    (h07VR : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X' ⟶ Y'),
      IsAlgebraicSpace B S hS X' → IsAlgebraicSpace B S hS Y' → IsFinite B S hS g →
      IsQuasiCompactSpace B S hS Y' →
      IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y' →
      ∃ s : IntegralFiniteSystem B S hS g,
        letI := s.indexPreorder
        ∀ (i j : s.indexType) (h : i ≤ j),
          IsClosedImmersion B S hS (s.diagram.map (homOfLE h).op))
    {X : AlgebraicSpaces B S hS} (f : X ⟶ A)
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hf : IsLocallyOfFinitePresentation B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) (hFqc : F.IsQuasicoherentOnSite)
    (hFft : F.IsFiniteTypeOnSite)
    (hFUfp : ((modulePullback B S hS (restrictOverι f U)).obj F).IsFinitePresentationOnSite)
    (hFUflat : IsFlatOver B S hS (restrictOver f U).2 (restrictOverHom f U).hom
      ((modulePullback B S hS (restrictOverι f U)).obj F)) :
    ∃ (Z : ClosedSubspaces B S hS A.1) (A' : AlgebraicSpaces B S hS) (b : A' ⟶ A),
      IsFlatteningBlowup f F U Z b :=
  exists_isFlatteningBlowup_of_isRepresentableSpace_source U
    (fun _ f' G hrep hqc hlfp hGqc hGft hGfp hGflat =>
      exists_isFlatteningBlowup_of_isRepresentableSpace hZ hAqc hAqs U hUqc hscheme h07VR
        hrep f' hqc hlfp G hGqc hGft hGfp hGflat)
    f hXqc hf F hFqc hFft hFUfp hFUflat

end AlgebraicGeometry.Space

end
