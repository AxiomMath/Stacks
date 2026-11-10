module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealLattice
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleContainmentAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget

/-!
# A finite type submodule over a quasi-compact étale space lies in one from below

Let `X` be a quasi-compact and quasi-separated algebraic space, `ℱ` a quasi-coherent
`𝒪_X`-module, `g : T ⟶ X` an étale morphism from a quasi-compact algebraic space and
`𝒢 ⊆ ℱ|_T` a submodule of finite type.  This file proves that there is a quasi-coherent
submodule `𝒦 ⊆ ℱ` of finite type with `𝒢 ⊆ 𝒦|_T`.  For `T` an affine étale chart this says that
the quasi-coherent submodules of finite type of `ℱ` exhaust it in the sense the proof of
Stacks 0DM0 uses.

## Main definitions

* `AlgebraicGeometry.Space.ContainmentProperty`: the containment property of an algebraic space.

## Main results

* `AlgebraicGeometry.Space.containmentProperty_of_isQuasiCompactSpace`: every quasi-compact and
  quasi-separated algebraic space has the containment property.
* `AlgebraicGeometry.Space.exists_le_etaleSubmoduleRestrict`: the containment statement.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_EtaleSubmoduleContainment :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_EtaleSubmoduleContainment
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_EtaleSubmoduleContainment B S hS).has_limit _

/-- **The containment property of an algebraic space `Y`**: for every quasi-coherent
`𝒪_Y`-module `ℱ` and every étale `g : T ⟶ Y` from a quasi-compact algebraic space, every
submodule of finite type of `ℱ|_T` is contained in the restriction to `T` of a quasi-coherent
submodule of `ℱ` of finite type. -/
def ContainmentProperty (Y : AlgebraicSpaces B S hS) : Prop :=
  ∀ (F : Modules.{u, u} B S hS Y.1 Y.2), F.IsQuasicoherentOnSite →
    ∀ (T : AlgebraicSpaces B S hS) (g : T ⟶ Y) (hg : IsEtale B S hS g.hom),
      IsQuasiCompactSpace B S hS T.1 →
      ∀ G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule,
        G.toSheafOfModules.IsFiniteType →
          ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
            K.toSheafOfModules.IsFiniteType ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K

/-- **The affine case of the containment property.** -/
theorem containmentProperty_of_isAffineSpace (W : AlgebraicSpaces B S hS)
    (hWa : IsAffineSpace B S hS W.1) : ContainmentProperty B S hS W :=
  fun F hF _ g hg hTqc G hGf =>
    exists_le_etaleSubmoduleRestrict_of_isAffineSpace B S hS W hWa F hF g hg hTqc G hGf

section FiberProduct

variable {W T Y : AlgebraicSpaces B S hS} (g : T ⟶ W) (h : Y ⟶ W)

/-- A section of the fibre product over an object of the site, with prescribed projections. -/
theorem exists_fiberProduct_app_eq {Z : (BigFppfOver B S hS)ᵒᵖ} (a : T.1.obj Z) (b : Y.1.obj Z)
    (hab : g.hom.app Z a = h.hom.app Z b) :
    ∃ w : (AlgebraicSpaces.fiberProduct B S hS g h).1.obj Z,
      (pullback.fst g.hom h.hom).app Z w = a ∧ (pullback.snd g.hom h.hom).app Z w = b := by
  refine ⟨(pullbackObjIso g.hom h.hom Z).inv
    ((Types.pullbackIsoPullback (g.hom.app Z) (h.hom.app Z)).inv ⟨(a, b), hab⟩), ?_, ?_⟩
  · have := ConcreteCategory.congr_hom (pullbackObjIso_inv_comp_fst g.hom h.hom Z)
      ((Types.pullbackIsoPullback (g.hom.app Z) (h.hom.app Z)).inv ⟨(a, b), hab⟩)
    simp only [types_comp_apply] at this
    exact this.trans (Types.pullbackIsoPullback_inv_fst_apply _ _ _)
  · have := ConcreteCategory.congr_hom (pullbackObjIso_inv_comp_snd g.hom h.hom Z)
      ((Types.pullbackIsoPullback (g.hom.app Z) (h.hom.app Z)).inv ⟨(a, b), hab⟩)
    simp only [types_comp_apply] at this
    exact this.trans (Types.pullbackIsoPullback_inv_snd_apply _ _ _)

/-- The fibre product of two quasi-compact algebraic spaces over a quasi-separated one is
quasi-compact. -/
theorem isQuasiCompactSpace_fiberProduct (hZ : B.Contains (⊤_ Scheme.{u}))
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) (hT : IsQuasiCompactSpace B S hS T.1)
    (hY : IsQuasiCompactSpace B S hS Y.1) :
    IsQuasiCompactSpace B S hS (AlgebraicSpaces.fiberProduct B S hS g h).1 := by
  change IsQuasiCompactSpace B S hS (pullback g.hom h.hom)
  exact isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hY h.hom T.1 T.2 hT g.hom

end FiberProduct

/-- **Transfer of the containment property across a fibre product.**  Let `g : T ⟶ W` and
`h : Y ⟶ W` be étale, with `T ×_W Y` quasi-compact and `Y` having the containment property.
Then every submodule `𝒢 ⊆ ℱ|_T` of finite type, for `ℱ` quasi-coherent, is dominated over `Y`
by a quasi-coherent submodule `𝒜 ⊆ ℱ|_Y` of finite type: at every geometric point of `W`, the
germ set of `𝒢` at any lift to `T` is contained in the germ set of `𝒜` at any lift to `Y`. -/
theorem exists_etaleGermSet_subset_of_containmentProperty {W T Y : AlgebraicSpaces B S hS}
    (g : T ⟶ W) (hg : IsEtale B S hS g.hom) (h : Y ⟶ W) (hh : IsEtale B S hS h.hom)
    (hPqc : IsQuasiCompactSpace B S hS (AlgebraicSpaces.fiberProduct B S hS g h).1)
    (hY : ContainmentProperty B S hS Y) (F : Modules.{u, u} B S hS W.1 W.2)
    (hF : F.IsQuasicoherentOnSite)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ A : ((etaleModulePullback.{u, u} B S hS h hh).obj F).Submodule,
      A.toSheafOfModules.IsQuasicoherentOnSite ∧ A.toSheafOfModules.IsFiniteType ∧
      ∀ (x : GeometricPoint B S hS W.1) (t : GeometricPointLift B S hS g.hom x)
        (y : GeometricPointLift B S hS h.hom x),
        etaleGermSet B S hS g hg G t ⊆ etaleGermSet B S hS h hh A y := by
  let P := AlgebraicSpaces.fiberProduct B S hS g h
  let p₁ : P ⟶ T := ObjectProperty.homMk (pullback.fst g.hom h.hom)
  let p₂ : P ⟶ Y := ObjectProperty.homMk (pullback.snd g.hom h.hom)
  have sq : IsPullback p₁ p₂ g h := AlgebraicSpaces.isPullback_fiberProduct B S hS g h
  have hp₂ : IsEtale B S hS p₂.hom := isEtale_of_isPullback B S hS p₁ p₂ g h sq hg
  have hp₁ : IsEtale B S hS p₁.hom := isEtale_of_isPullback B S hS p₂ p₁ h g sq.flip hh
  have e : p₁ ≫ g = p₂ ≫ h := sq.w
  have hp₁g : IsEtale B S hS (p₁ ≫ g).hom := isEtale_comp B S hS hp₁ hg
  have hp₂h : IsEtale B S hS (p₂ ≫ h).hom := isEtale_comp B S hS hp₂ hh
  let G₁ := etaleSubmoduleCongr B S hS e hp₁g hp₂h
    (etaleSubmoduleAlong B S hS p₁ hp₁ g hg hp₁g G)
  have hG₁f : G₁.toSheafOfModules.IsFiniteType := by
    refine (isFiniteType_etaleSubmoduleCongr_iff B S hS e hp₁g hp₂h _).2 ?_
    exact isFiniteType_of_iso' B S hS (etaleSubmoduleAlongIso B S hS p₁ hp₁ g hg hp₁g G).symm
      (isFiniteType_etaleModulePullback B S hS p₁ hp₁ _ hGf)
  let G₂ := etaleSubmoduleCompToIter B S hS p₂ hp₂ h hh hp₂h G₁
  have hG₂f : G₂.toSheafOfModules.IsFiniteType :=
    isFiniteType_of_iso' B S hS
      (etaleSubmoduleCompToIterIso B S hS p₂ hp₂ h hh hp₂h G₁).symm hG₁f
  obtain ⟨A, hAq, hAf, hA⟩ := hY _ (isQuasicoherentOnSite_etaleModulePullback B S hS h hh F hF)
    P p₂ hp₂ hPqc G₂ hG₂f
  have hA' : G₁ ≤ etaleSubmoduleAlong B S hS p₂ hp₂ h hh hp₂h A := fun V s hs => hA V hs
  refine ⟨A, hAq, hAf, fun x t y => ?_⟩
  obtain ⟨w, hw₁, hw₂⟩ := exists_fiberProduct_app_eq B S hS g h t.1 y.1 (t.2.trans y.2.symm)
  let a : GeometricPointLift B S hS p₁.hom (liftGeometricPoint B S hS g t) := ⟨w, hw₁⟩
  let b : GeometricPointLift B S hS p₂.hom (liftGeometricPoint B S hS h y) := ⟨w, hw₂⟩
  have h₁ := etaleGermSet_along B S hS g hg p₁ hp₁ hp₁g G t a
  have h₂ := etaleGermSet_along B S hS h hh p₂ hp₂ hp₂h A y b
  have h₃ := etaleGermSet_etaleSubmoduleCongr B S hS e hp₁g hp₂h
    (etaleSubmoduleAlong B S hS p₁ hp₁ g hg hp₁g G) (GeometricPointLift.comp B S hS g p₁ t a)
    (GeometricPointLift.comp B S hS h p₂ y b) rfl
  have h₄ := etaleGermSet_mono B S hS (p₂ ≫ h) hp₂h hA' (GeometricPointLift.comp B S hS h p₂ y b)
  intro z hz
  rw [← h₂]
  refine h₄ ?_
  change z ∈ etaleGermSet B S hS (p₂ ≫ h) hp₂h (etaleSubmoduleCongr B S hS e hp₁g hp₂h
    (etaleSubmoduleAlong B S hS p₁ hp₁ g hg hp₁g G)) (GeometricPointLift.comp B S hS h p₂ y b)
  rwa [h₃, h₁]

/-- **The induction step for the containment property.**  Let `(Uo ⊆ W, f : V ⟶ W)` be an
elementary distinguished square with `W` quasi-separated, `Uo` quasi-compact and `V` affine.  If
`Uo` has the containment property, so does `W`. -/
theorem containmentProperty_of_isElementaryDistinguishedSquare (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hPU : ContainmentProperty B S hS (openSubspaceSpace B S hS Uo hsq.isOpenSubspace)) :
    ContainmentProperty B S hS W := by
  classical
  intro F hF T g hg hTqc G hGf
  have hUo := hsq.isOpenSubspace
  let Uos := openSubspaceSpace B S hS Uo hUo
  let j := openSubspaceHom B S hS Uo hUo
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS Uo hUo
  let Vs := edsEtale B S hS hsq
  let f := edsEtaleHom B S hS hsq
  have hf : IsEtale B S hS f.hom := isEtale_edsEtaleHom B S hS hsq
  have hVqc : IsQuasiCompactSpace B S hS V := by
    obtain ⟨T, hT, ⟨e⟩⟩ := hVa
    exact IsQuasiCompactSpace.of_iso B S hS (isQuasiCompactSpace_yoneda_of_isAffine B S hS T hT)
      e.symm
  have hPV : ContainmentProperty B S hS Vs := containmentProperty_of_isAffineSpace B S hS Vs hVa
  have hjF := isQuasicoherentOnSite_etaleModulePullback B S hS j hj F hF
  have hfF := isQuasicoherentOnSite_etaleModulePullback B S hS f hf F hF
  obtain ⟨A₁, hA₁q, hA₁f, hA₁⟩ := exists_etaleGermSet_subset_of_containmentProperty B S hS g hg
    j hj (isQuasiCompactSpace_fiberProduct B S hS g j hZ hWqs hTqc hUoqc) hPU F hF G hGf
  obtain ⟨B₁, hB₁q, hB₁f, hB₁⟩ := exists_etaleGermSet_subset_of_containmentProperty B S hS g hg
    f hf (isQuasiCompactSpace_fiberProduct B S hS g f hZ hWqs hTqc hVqc) hPV F hF G hGf
  obtain ⟨A₂, hA₂q, hA₂f, hA₂⟩ := exists_etaleGermSet_subset_of_containmentProperty B S hS f hf
    j hj (isQuasiCompactSpace_fiberProduct B S hS f j hZ hWqs hVqc hUoqc) hPU F hF B₁ hB₁f
  let A := A₁ ⊔ A₂
  have hAq : A.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_sup B S hS _ _ hjF A₁ A₂ hA₁q hA₂q
  have hAf : A.toSheafOfModules.IsFiniteType := isFiniteType_sup B S hS A₁ A₂ hA₁f hA₂f
  have hfqc : IsQuasiCompact B S hS fV :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs hVqc fV
  let V₀ : Subfunctor Vs.1 := Uo.preimage fV
  have hV₀ : IsOpenSubspace B S hS V₀ :=
    isOpenSubspace_preimage B S hS fV Uo W.2 hsq.isAlgebraicSpace hUo
  have hV₀qc : IsQuasiCompactSpace B S hS V₀.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 hsq.isAlgebraicSpace fV hfqc hUo
      hUoqc
  let ι₀ := openSubspaceHom B S hS (W := Vs) V₀ hV₀
  have hι₀ : IsEtale B S hS ι₀.hom := isEtale_openSubspaceHom B S hS (W := Vs) V₀ hV₀
  let σ₀ : openSubspaceSpace B S hS (W := Vs) V₀ hV₀ ⟶ Uos :=
    ObjectProperty.homMk (Uo.fromPreimage fV)
  have e₀ : σ₀ ≫ j = ι₀ ≫ f := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Uo fV)
  have hι₀f : IsEtale B S hS (ι₀ ≫ f).hom := isEtale_comp B S hS hι₀ hf
  have hσ₀j : IsEtale B S hS (σ₀ ≫ j).hom := e₀ ▸ hι₀f
  have hσ₀ : IsEtale B S hS σ₀.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ σ₀.hom Uo.ι (Subfunctor.instMonoFunctorTypeι Uo) hσ₀j
  let CW := etaleSubmoduleCongr B S hS e₀ hσ₀j hι₀f
    (etaleSubmoduleAlong B S hS σ₀ hσ₀ j hj hσ₀j A)
  let C := etaleSubmoduleCompToIter B S hS ι₀ hι₀ f hf hι₀f CW
  have hC : C.toSheafOfModules.IsQuasicoherentOnSite ∧ C.toSheafOfModules.IsFiniteType := by
    obtain ⟨h1, h2⟩ := etaleSubmoduleAlong_isQuasicoherentOnSite_isFiniteType B S hS σ₀ hσ₀ j
      hj hσ₀j A hAq hAf
    have h1' := (isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS e₀ hσ₀j hι₀f _).2 h1
    have h2' := (isFiniteType_etaleSubmoduleCongr_iff B S hS e₀ hσ₀j hι₀f _).2 h2
    exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleCompToIterIso B S hS ι₀ hι₀ f hf hι₀f CW).symm h1',
      isFiniteType_of_iso' B S hS (etaleSubmoduleCompToIterIso B S hS ι₀ hι₀ f hf hι₀f CW).symm h2'⟩
  obtain ⟨A', hA'q, hA'f, hA'⟩ := extensionProperty_of_isAffineSpace B S hS hZ Vs hVa _ hfF
    V₀ hV₀ hV₀qc C hC.1 hC.2
  have hA'W : etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f A' = CW :=
    congrArg (etaleSubmoduleIterToComp B S hS ι₀ hι₀ f hf hι₀f) hA'
  let BV := A' ⊔ B₁
  have hBVq : BV.toSheafOfModules.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_sup B S hS _ _ hfF A' B₁ hA'q hB₁q
  have hBVf : BV.toSheafOfModules.IsFiniteType := isFiniteType_sup B S hS A' B₁ hA'f hB₁f
  have hB₁le : etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f B₁ ≤ CW := by
    refine le_of_forall_etaleGermSet_subset B S hS (ι₀ ≫ f) hι₀f fun x t' => ?_
    let v : GeometricPointLift B S hS f.hom x := ⟨ι₀.hom.app _ t'.1, t'.2⟩
    let p : GeometricPointLift B S hS ι₀.hom (liftGeometricPoint B S hS f v) := ⟨t'.1, rfl⟩
    have hu : j.hom.app _ (σ₀.hom.app _ t'.1) = x.val.value :=
      (congrArg (fun φ => φ.hom.app _ t'.1) e₀).trans t'.2
    let w : GeometricPointLift B S hS j.hom x := ⟨σ₀.hom.app _ t'.1, hu⟩
    let q : GeometricPointLift B S hS σ₀.hom (liftGeometricPoint B S hS j w) := ⟨t'.1, rfl⟩
    have ht₁ : t' = GeometricPointLift.comp B S hS f ι₀ v p := rfl
    have h₁ := etaleGermSet_along B S hS f hf ι₀ hι₀ hι₀f B₁ v p
    have h₂ := etaleGermSet_etaleSubmoduleCongr B S hS e₀ hσ₀j hι₀f
      (etaleSubmoduleAlong B S hS σ₀ hσ₀ j hj hσ₀j A)
      (GeometricPointLift.comp B S hS j σ₀ w q) t' rfl
    have h₃ := etaleGermSet_along B S hS j hj σ₀ hσ₀ hσ₀j A w q
    intro z hz
    rw [h₂, h₃]
    rw [ht₁, h₁] at hz
    exact etaleGermSet_mono B S hS j hj (le_sup_right : A₂ ≤ A) w (hA₂ x v w hz)
  have hBVW : etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f BV = CW := by
    change etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f (A' ⊔ B₁) = CW
    rw [etaleSubmoduleAlong_sup, hA'W]
    exact sup_eq_left.2 hB₁le
  have hagree : EdsGermAgree B S hS hsq Uo hUo A BV := by
    intro x t u
    have hu := value_mem_of_geometricPointLift B S hS Uo hUo u
    have hmem : t.1 ∈ V₀.obj (op (x.val.siteObject B S hS W.1)) := by
      have h := t.2
      change fV.app _ t.1 = x.val.value at h
      change fV.app _ t.1 ∈ Uo.obj _
      rwa [h]
    let t₁ : GeometricPointLift B S hS ι₀.hom (liftGeometricPoint B S hS f t) :=
      ⟨⟨t.1, hmem⟩, rfl⟩
    let p : GeometricPointLift B S hS σ₀.hom (liftGeometricPoint B S hS j u) :=
      ⟨⟨t.1, hmem⟩, Subtype.ext (t.2.trans u.2.symm)⟩
    calc etaleGermSet B S hS f hf BV t
        = etaleGermSet B S hS (ι₀ ≫ f) hι₀f (etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f BV)
            (GeometricPointLift.comp B S hS f ι₀ t t₁) :=
          (etaleGermSet_along B S hS f hf ι₀ hι₀ hι₀f BV t t₁).symm
      _ = etaleGermSet B S hS (ι₀ ≫ f) hι₀f CW (GeometricPointLift.comp B S hS f ι₀ t t₁) := by
          rw [hBVW]
      _ = etaleGermSet B S hS (σ₀ ≫ j) hσ₀j (etaleSubmoduleAlong B S hS σ₀ hσ₀ j hj hσ₀j A)
            (GeometricPointLift.comp B S hS j σ₀ u p) :=
          etaleGermSet_etaleSubmoduleCongr B S hS e₀ hσ₀j hι₀f _ _ _ rfl
      _ = etaleGermSet B S hS j hj A u :=
          etaleGermSet_along B S hS j hj σ₀ hσ₀ hσ₀j A u p
  obtain ⟨K, hKj, hKf⟩ := exists_etaleSubmodule_eds_glue B S hS hsq Uo hUo le_rfl hagree
  have hK := isQuasicoherentOnSite_isFiniteType_of_pair B S hS j f hj hf
    (fun z => points_covered_of_isElementaryDistinguishedSquare B S hS hsq z) K
    (by rw [hKj]; exact ⟨hAq, hAf⟩) (by rw [hKf]; exact ⟨hBVq, hBVf⟩)
  refine ⟨K, hK.1, hK.2, ?_⟩
  refine le_of_forall_etaleGermSet_subset B S hS g hg fun x t => ?_
  rw [etaleGermSet_etaleSubmoduleRestrict]
  by_cases hx : Nonempty (GeometricPointLift B S hS j.hom x)
  · obtain ⟨u⟩ := hx
    calc etaleGermSet B S hS g hg G t ⊆ etaleGermSet B S hS j hj A₁ u := hA₁ x t u
      _ ⊆ etaleGermSet B S hS j hj A u :=
          etaleGermSet_mono B S hS j hj (le_sup_left : A₁ ≤ A) u
      _ = etaleGermSet B S hS j hj (etaleSubmoduleRestrict B S hS j hj K) u := by rw [hKj]
      _ = submoduleGermSet B S hS K x := etaleGermSet_etaleSubmoduleRestrict B S hS j hj K u
  · have hx' : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := fun hmem =>
      hx ((nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo hUo x).2 hmem)
    obtain ⟨v⟩ := nonempty_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x hx'
    calc etaleGermSet B S hS g hg G t ⊆ etaleGermSet B S hS f hf B₁ v := hB₁ x t v
      _ ⊆ etaleGermSet B S hS f hf BV v :=
          etaleGermSet_mono B S hS f hf (le_sup_right : B₁ ≤ BV) v
      _ = etaleGermSet B S hS f hf (etaleSubmoduleRestrict B S hS f hf K) v := by rw [hKf]
      _ = submoduleGermSet B S hS K x := etaleGermSet_etaleSubmoduleRestrict B S hS f hf K v

/-- **Every quasi-compact and quasi-separated algebraic space has the containment property.** -/
theorem containmentProperty_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ContainmentProperty B S hS X :=
  qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y, ContainmentProperty B S hS ⟨Y, hY⟩)
    (fun V hVa hY => containmentProperty_of_isAffineSpace B S hS ⟨V.1.left.1, hY⟩ hVa)
    (fun W _ _ _ _ hsq _ hWqs hUqc hVa hPU _ _ hY =>
      containmentProperty_of_isElementaryDistinguishedSquare B S hS hZ (W := ⟨W.1.left.1, hY⟩)
        hsq hWqs hUqc hVa (hPU _)) X.2

/-- **A finite type submodule over a quasi-compact étale space lies in one from below.**  Let `X`
be a quasi-compact and quasi-separated algebraic space, `ℱ` a quasi-coherent `𝒪_X`-module,
`g : T ⟶ X` an étale morphism from a quasi-compact algebraic space and `𝒢 ⊆ ℱ|_T` a submodule of
finite type.  Then there is a quasi-coherent submodule `𝒦 ⊆ ℱ` of finite type with
`𝒢 ⊆ 𝒦|_T`. -/
theorem exists_le_etaleSubmoduleRestrict (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) {T : AlgebraicSpaces B S hS} (g : T ⟶ X)
    (hg : IsEtale B S hS g.hom) (hTqc : IsQuasiCompactSpace B S hS T.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K :=
  containmentProperty_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs F hF T g hg hTqc G hGf

end AlgebraicGeometry.Space

end
