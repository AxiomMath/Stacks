module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleComap
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubmoduleExhaustion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionQcqs

/-!
# Exhaustion by finite type quasi-coherent submodules on a qcqs algebraic space

Let `X` be a quasi-compact and quasi-separated algebraic space and `ℱ` a quasi-coherent
`𝒪_X`-module.  This file proves that every germ of `ℱ` at a geometric point is the germ of a
section of a quasi-coherent submodule of `ℱ` of finite type, and deduces the statement which the
proof of Stacks 085M takes from the colimit assertion of Stacks 0829: for every étale
`g : Y ⟶ X` with `Y` quasi-compact and every submodule `𝒢 ⊆ ℱ|_Y` of finite type there is a
quasi-coherent submodule `𝒦 ⊆ ℱ` of finite type with `𝒢 ⊆ 𝒦|_Y`.

## The argument

The source obtains both from Stacks 07V9, that is from absolute Noetherian approximation.  The
argument here avoids it, by the induction principle of Stacks 08GP
(`AlgebraicGeometry.Space.qcqs_induction_on_self`), as for Stacks 0853 in
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectExtensionQcqs`.  The affine
case is `AlgebraicGeometry.Space.finiteTypeGermExhaustion_of_isAffineSpace`.  For an elementary
distinguished square `(Uo ⊆ W, f : V ⟶ W)` with `V` affine, let `x̄` be a geometric point of `W`.

* If `x̄` lies in `Uo`, a germ at `x̄` is the germ of a submodule `𝒜 ⊆ ℱ|_{Uo}` of finite type, and
  `𝒜` extends to `W` by Stacks 0853.
* Otherwise `x̄` lifts to `V`, and a germ at `x̄` is the germ of a submodule `ℬ ⊆ ℱ|_V` of finite
  type.  On `V₀ = f⁻¹(Uo)`, quasi-compact and étale over `Uo`, the induction hypothesis puts
  `ℬ|_{V₀}` inside `𝒜|_{V₀}` for some `𝒜 ⊆ ℱ|_{Uo}` of finite type; Stacks 0853 on the affine `V`
  extends `𝒜|_{V₀}` to `𝒞 ⊆ ℱ|_V`; then `𝒞 ⊔ ℬ` restricts to `𝒜|_{V₀}` on `V₀`, so `𝒜` and
  `𝒞 ⊔ ℬ` glue across the square to a submodule of `ℱ` of finite type whose germ at `x̄` contains
  that of `ℬ`.

## Main results

* `AlgebraicGeometry.Space.finiteTypeGermExhaustion_of_isQuasiCompactSpace`: the exhaustion.
* `AlgebraicGeometry.Space.exists_finiteType_le_etaleSubmoduleRestrict`: the containment.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0853](https://stacks.math.columbia.edu/tag/0853)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Helpers

variable {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
  {M : Modules.{u, u} B S hS X.1 X.2}

/-- **Exhaustion of the restriction, read at a lift.**  If `Y` has
`AlgebraicGeometry.Space.FiniteTypeGermExhaustion`, then every germ of a local section of a
quasi-coherent `ℱ` at a geometric point of `X` lifting to `Y` lies in the germ set, at that lift,
of a quasi-coherent submodule of `ℱ|_Y` of finite type. -/
theorem exists_mem_etaleGermSet_of_finiteTypeGermExhaustion
    (hY : FiniteTypeGermExhaustion B S hS Y) (hM : M.IsQuasicoherentOnSite)
    {x : GeometricPoint B S hS X.1} (t : GeometricPointLift B S hS g.hom x)
    (V : SmallEtale B S hS X.1) (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V)
    (s : M.val.obj (op V)) :
    ∃ N : ((etaleModulePullback.{u, u} B S hS g hg).obj M).Submodule,
      N.toSheafOfModules.IsQuasicoherentOnSite ∧ N.toSheafOfModules.IsFiniteType ∧
        (etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V p
          (etaleModuleSectionsPresheaf B S hS M) s ∈ etaleGermSet B S hS g hg N t := by
  let ι := (restrictionPresheafFiberIso (A := Type u) B S hS g hg t).app
    (etaleModuleSectionsPresheaf B S hS M)
  obtain ⟨e', he'⟩ := (ConcreteCategory.bijective_of_isIso ι.hom).2
    ((etaleSitePoint B S hS X.1 x X.2).toPresheafFiber V p
      (etaleModuleSectionsPresheaf B S hS M) s)
  obtain ⟨V', w', n, rfl⟩ := (liftSitePoint B S hS g t).toPresheafFiber_jointly_surjective
    (P := (smallEtalePostcomp B S hS g hg).op ⋙ etaleModuleSectionsPresheaf B S hS M) e'
  obtain ⟨N, hNq, hNf, hN⟩ := hY _ (isQuasicoherentOnSite_etaleModulePullback B S hS g hg M hM)
    (liftGeometricPoint B S hS g t) V' w' n
  refine ⟨N, hNq, hNf, ?_⟩
  rw [etaleGermSet_eq_image_submoduleGermSet]
  exact ⟨_, hN, he'⟩

end Helpers

section Transport

/-- Quasi-coherence and finite type survive restricting a submodule along `k₁`, transporting it
along `k₁ ≫ g₁ = k₂ ≫ g₂` and reading it over `k₂`. -/
theorem isQuasicoherentOnSite_isFiniteType_etaleSubmoduleCompToIter_congr
    {X Y Z₁ Z₂ : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS X.1 X.2}
    (k₁ : Y ⟶ Z₁) (hk₁ : IsEtale B S hS k₁.hom) (g₁ : Z₁ ⟶ X) (hg₁ : IsEtale B S hS g₁.hom)
    (k₂ : Y ⟶ Z₂) (hk₂ : IsEtale B S hS k₂.hom) (g₂ : Z₂ ⟶ X) (hg₂ : IsEtale B S hS g₂.hom)
    (e : k₁ ≫ g₁ = k₂ ≫ g₂) (h₁ : IsEtale B S hS (k₁ ≫ g₁).hom)
    (h₂ : IsEtale B S hS (k₂ ≫ g₂).hom)
    (N : ((etaleModulePullback.{u, u} B S hS g₁ hg₁).obj M).Submodule)
    (hNq : N.toSheafOfModules.IsQuasicoherentOnSite) (hNf : N.toSheafOfModules.IsFiniteType) :
    (etaleSubmoduleCompToIter B S hS k₂ hk₂ g₂ hg₂ h₂ (etaleSubmoduleCongr B S hS e h₁ h₂
        (etaleSubmoduleAlong B S hS k₁ hk₁ g₁ hg₁ h₁ N))).toSheafOfModules.IsQuasicoherentOnSite ∧
      (etaleSubmoduleCompToIter B S hS k₂ hk₂ g₂ hg₂ h₂ (etaleSubmoduleCongr B S hS e h₁ h₂
        (etaleSubmoduleAlong B S hS k₁ hk₁ g₁ hg₁ h₁ N))).toSheafOfModules.IsFiniteType := by
  obtain ⟨hq, hf⟩ :=
    etaleSubmoduleAlong_isQuasicoherentOnSite_isFiniteType B S hS k₁ hk₁ g₁ hg₁ h₁ N hNq hNf
  exact ⟨SheafOfModules.IsQuasicoherentOnSite.of_iso
      (etaleSubmoduleCompToIterIso B S hS k₂ hk₂ g₂ hg₂ h₂ _).symm
      ((isQuasicoherentOnSite_etaleSubmoduleCongr_iff B S hS e h₁ h₂ _).2 hq),
    isFiniteType_of_iso' B S hS (etaleSubmoduleCompToIterIso B S hS k₂ hk₂ g₂ hg₂ h₂ _).symm
      ((isFiniteType_etaleSubmoduleCongr_iff B S hS e h₁ h₂ _).2 hf)⟩

/-- Germ sets of two submodules whose restrictions to a common `Y` agree, read at lifts with a
common lift to `Y`, agree. -/
theorem etaleGermSet_eq_of_etaleSubmoduleAlong_eq {X Y Z₁ Z₂ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2}
    (k₁ : Y ⟶ Z₁) (hk₁ : IsEtale B S hS k₁.hom) (g₁ : Z₁ ⟶ X) (hg₁ : IsEtale B S hS g₁.hom)
    (k₂ : Y ⟶ Z₂) (hk₂ : IsEtale B S hS k₂.hom) (g₂ : Z₂ ⟶ X) (hg₂ : IsEtale B S hS g₂.hom)
    (e : k₂ ≫ g₂ = k₁ ≫ g₁) (h₁ : IsEtale B S hS (k₁ ≫ g₁).hom)
    (h₂ : IsEtale B S hS (k₂ ≫ g₂).hom)
    {N₁ : ((etaleModulePullback.{u, u} B S hS g₁ hg₁).obj M).Submodule}
    {N₂ : ((etaleModulePullback.{u, u} B S hS g₂ hg₂).obj M).Submodule}
    (h : etaleSubmoduleAlong B S hS k₁ hk₁ g₁ hg₁ h₁ N₁ =
      etaleSubmoduleCongr B S hS e h₂ h₁ (etaleSubmoduleAlong B S hS k₂ hk₂ g₂ hg₂ h₂ N₂))
    {x : GeometricPoint B S hS X.1} (t₁ : GeometricPointLift B S hS g₁.hom x)
    (t₂ : GeometricPointLift B S hS g₂.hom x)
    (s₁ : GeometricPointLift B S hS k₁.hom (liftGeometricPoint B S hS g₁ t₁))
    (s₂ : GeometricPointLift B S hS k₂.hom (liftGeometricPoint B S hS g₂ t₂))
    (hs : (GeometricPointLift.comp B S hS g₁ k₁ t₁ s₁).1 =
      (GeometricPointLift.comp B S hS g₂ k₂ t₂ s₂).1) :
    etaleGermSet B S hS g₁ hg₁ N₁ t₁ = etaleGermSet B S hS g₂ hg₂ N₂ t₂ := by
  rw [← etaleGermSet_along B S hS g₁ hg₁ k₁ hk₁ h₁ N₁ t₁ s₁, h,
    etaleGermSet_etaleSubmoduleCongr B S hS e h₂ h₁ _ _ _ hs.symm,
    etaleGermSet_along B S hS g₂ hg₂ k₂ hk₂ h₂ N₂ t₂ s₂]

/-- Germ sets of two submodules whose restrictions to a common `Y` are contained in one another,
read at lifts with a common lift to `Y`, are contained in one another. -/
theorem etaleGermSet_subset_of_etaleSubmoduleCongr_le {X Y Z₁ Z₂ : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2}
    (k₁ : Y ⟶ Z₁) (hk₁ : IsEtale B S hS k₁.hom) (g₁ : Z₁ ⟶ X) (hg₁ : IsEtale B S hS g₁.hom)
    (k₂ : Y ⟶ Z₂) (hk₂ : IsEtale B S hS k₂.hom) (g₂ : Z₂ ⟶ X) (hg₂ : IsEtale B S hS g₂.hom)
    (e : k₁ ≫ g₁ = k₂ ≫ g₂) (h₁ : IsEtale B S hS (k₁ ≫ g₁).hom)
    (h₂ : IsEtale B S hS (k₂ ≫ g₂).hom)
    {N₁ : ((etaleModulePullback.{u, u} B S hS g₁ hg₁).obj M).Submodule}
    {N₂ : ((etaleModulePullback.{u, u} B S hS g₂ hg₂).obj M).Submodule}
    (h : etaleSubmoduleCongr B S hS e h₁ h₂ (etaleSubmoduleAlong B S hS k₁ hk₁ g₁ hg₁ h₁ N₁) ≤
      etaleSubmoduleAlong B S hS k₂ hk₂ g₂ hg₂ h₂ N₂)
    {x : GeometricPoint B S hS X.1} (t₁ : GeometricPointLift B S hS g₁.hom x)
    (t₂ : GeometricPointLift B S hS g₂.hom x)
    (s₁ : GeometricPointLift B S hS k₁.hom (liftGeometricPoint B S hS g₁ t₁))
    (s₂ : GeometricPointLift B S hS k₂.hom (liftGeometricPoint B S hS g₂ t₂))
    (hs : (GeometricPointLift.comp B S hS g₁ k₁ t₁ s₁).1 =
      (GeometricPointLift.comp B S hS g₂ k₂ t₂ s₂).1) :
    etaleGermSet B S hS g₁ hg₁ N₁ t₁ ⊆ etaleGermSet B S hS g₂ hg₂ N₂ t₂ := by
  rw [← etaleGermSet_along B S hS g₁ hg₁ k₁ hk₁ h₁ N₁ t₁ s₁,
    ← etaleGermSet_along B S hS g₂ hg₂ k₂ hk₂ h₂ N₂ t₂ s₂,
    ← etaleGermSet_etaleSubmoduleCongr B S hS e h₁ h₂ _ _ _ hs]
  exact etaleGermSet_mono B S hS _ h₂ h _

/-- A lift along `g` and a lift along an open `Uo` of the same geometric point have a common lift
to the preimage `g⁻¹(Uo)`. -/
theorem exists_geometricPointLift_preimage {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    {Uo : Subfunctor X.1} (hUo : IsOpenSubspace B S hS Uo)
    (hV₀ : IsOpenSubspace B S hS (Uo.preimage g.hom)) {x : GeometricPoint B S hS X.1}
    (t : GeometricPointLift B S hS g.hom x)
    (u : GeometricPointLift B S hS (openSubspaceHom B S hS Uo hUo).hom x) :
    ∃ (t₁ : GeometricPointLift B S hS (openSubspaceHom B S hS (Uo.preimage g.hom) hV₀).hom
        (liftGeometricPoint B S hS g t))
      (p₁ : GeometricPointLift B S hS
        (ObjectProperty.homMk (Uo.fromPreimage g.hom) :
          openSubspaceSpace B S hS (Uo.preimage g.hom) hV₀ ⟶
            openSubspaceSpace B S hS Uo hUo).hom
        (liftGeometricPoint B S hS (openSubspaceHom B S hS Uo hUo) u)),
      (GeometricPointLift.comp B S hS g _ t t₁).1 =
        (GeometricPointLift.comp B S hS (openSubspaceHom B S hS Uo hUo) _ u p₁).1 := by
  have hmem : t.1 ∈ (Uo.preimage g.hom).obj (op (x.val.siteObject B S hS X.1)) := by
    have h := t.2
    change g.hom.app _ t.1 = x.val.value at h
    show g.hom.app _ t.1 ∈ Uo.obj _
    rw [h]
    exact value_mem_of_geometricPointLift B S hS Uo hUo u
  exact ⟨⟨⟨t.1, hmem⟩, rfl⟩, ⟨⟨t.1, hmem⟩, Subtype.ext (t.2.trans u.2.symm)⟩, rfl⟩

end Transport

section Step

variable {B S hS}

/-- **The induction step at a point of the open subspace.**  A germ at a geometric point of `W`
lying in a quasi-compact open subspace `Uo` with the exhaustion property is a germ of a
quasi-coherent submodule of finite type: it is so on `Uo`, and Stacks 0853 extends. -/
theorem exists_mem_submoduleGermSet_of_lift_openSubspace (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} (hWqc : IsQuasiCompactSpace B S hS W.1)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1) {Uo : Subfunctor W.1}
    (hUo : IsOpenSubspace B S hS Uo) (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor)
    (hPU : FiniteTypeGermExhaustion B S hS (openSubspaceSpace B S hS Uo hUo))
    {F : Modules.{u, u} B S hS W.1 W.2} (hF : F.IsQuasicoherentOnSite)
    {x : GeometricPoint B S hS W.1}
    (u : GeometricPointLift B S hS (openSubspaceHom B S hS Uo hUo).hom x)
    (V : SmallEtale B S hS W.1) (p : (etaleSitePoint B S hS W.1 x W.2).fiber.obj V)
    (s : F.val.obj (op V)) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧
      (etaleSitePoint B S hS W.1 x W.2).toPresheafFiber V p
        (etaleModuleSectionsPresheaf B S hS F) s ∈ submoduleGermSet B S hS K x := by
  obtain ⟨A, hAq, hAf, hA⟩ := exists_mem_etaleGermSet_of_finiteTypeGermExhaustion B S hS
    (openSubspaceHom B S hS Uo hUo) (isEtale_openSubspaceHom B S hS Uo hUo) hPU hF u V p s
  obtain ⟨K, hKq, hKf, hK⟩ := extensionProperty_of_isQuasiCompactSpace B S hS hZ W hWqc hWqs F
    hF Uo hUo hUoqc A hAq hAf
  refine ⟨K, hKq, hKf, ?_⟩
  rwa [← etaleGermSet_etaleSubmoduleRestrict B S hS _ (isEtale_openSubspaceHom B S hS Uo hUo) K u,
    hK]

/-- **Glueing across the square, at a germ.**  Quasi-coherent submodules of finite type of
`ℱ|_{Uo}` and `ℱ|_V` whose germ sets agree glue to one of `ℱ`, whose germ sets contain theirs. -/
theorem exists_mem_submoduleGermSet_of_edsGermAgree
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV) {F : Modules.{u, u} B S hS W.1 W.2}
    {A : ((etaleModulePullback.{u, u} B S hS (openSubspaceHom B S hS Uo hsq.isOpenSubspace)
      (isEtale_openSubspaceHom B S hS Uo hsq.isOpenSubspace)).obj F).Submodule}
    {N : ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).obj F).Submodule}
    (hA : A.toSheafOfModules.IsQuasicoherentOnSite ∧ A.toSheafOfModules.IsFiniteType)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite ∧ N.toSheafOfModules.IsFiniteType)
    (h : EdsGermAgree B S hS hsq Uo hsq.isOpenSubspace A N) {x : GeometricPoint B S hS W.1}
    (t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x) {z}
    (hz : z ∈ etaleGermSet B S hS _ (isEtale_edsEtaleHom B S hS hsq) N t) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ z ∈ submoduleGermSet B S hS K x := by
  obtain ⟨K, hKj, hKf⟩ := exists_etaleSubmodule_eds_glue B S hS hsq Uo hsq.isOpenSubspace le_rfl h
  have hK := isQuasicoherentOnSite_isFiniteType_of_pair B S hS _ _
    (isEtale_openSubspaceHom B S hS Uo hsq.isOpenSubspace) (isEtale_edsEtaleHom B S hS hsq)
    (points_covered_of_isElementaryDistinguishedSquare B S hS hsq) K
    (by rw [hKj]; exact hA) (by rw [hKf]; exact hN)
  refine ⟨K, hK.1, hK.2, ?_⟩
  rwa [← etaleGermSet_etaleSubmoduleRestrict B S hS _ (isEtale_edsEtaleHom B S hS hsq) K t, hKf]

/-- **The induction step at a point lifting to the étale member of the square.**  Let
`(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square with `W` quasi-compact and
quasi-separated, `Uo` quasi-compact and `V` affine, `Uo` and `V` having the exhaustion property.
A germ at a geometric point of `W` lifting to `V` is a germ of a quasi-coherent submodule of
finite type.

A germ of `ℬ ⊆ ℱ|_V` at the lift is given; `ℬ|_{V₀}` lies in `𝒜|_{V₀}` for some `𝒜 ⊆ ℱ|_{Uo}`;
the extension `𝒞` of `𝒜|_{V₀}` to `V` makes `𝒞 ⊔ ℬ` agree with `𝒜` over `V₀`, and the two glue. -/
theorem exists_mem_submoduleGermSet_of_lift_edsEtale (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hPU : FiniteTypeGermExhaustion B S hS (openSubspaceSpace B S hS Uo hsq.isOpenSubspace))
    (hPV : FiniteTypeGermExhaustion B S hS (edsEtale B S hS hsq))
    {F : Modules.{u, u} B S hS W.1 W.2} (hF : F.IsQuasicoherentOnSite)
    {x : GeometricPoint B S hS W.1}
    (t : GeometricPointLift B S hS (edsEtaleHom B S hS hsq).hom x)
    (Vc : SmallEtale B S hS W.1) (p : (etaleSitePoint B S hS W.1 x W.2).fiber.obj Vc)
    (s : F.val.obj (op Vc)) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧
      (etaleSitePoint B S hS W.1 x W.2).toPresheafFiber Vc p
        (etaleModuleSectionsPresheaf B S hS F) s ∈ submoduleGermSet B S hS K x := by
  have hUo := hsq.isOpenSubspace
  let j := openSubspaceHom B S hS Uo hUo
  have hj : IsEtale B S hS j.hom := isEtale_openSubspaceHom B S hS Uo hUo
  let f := edsEtaleHom B S hS hsq
  have hf : IsEtale B S hS f.hom := isEtale_edsEtaleHom B S hS hsq
  let Vs := edsEtale B S hS hsq
  have hFf := isQuasicoherentOnSite_etaleModulePullback B S hS f hf F hF
  obtain ⟨Bm, hBq, hBf, hBx⟩ := exists_mem_etaleGermSet_of_finiteTypeGermExhaustion B S hS f hf
    hPV hF t Vc p s
  let V₀ : Subfunctor Vs.1 := Uo.preimage fV
  have hV₀ : IsOpenSubspace B S hS V₀ :=
    isOpenSubspace_preimage B S hS fV Uo W.2 hsq.isAlgebraicSpace hUo
  have hV₀qc : IsQuasiCompactSpace B S hS V₀.toFunctor :=
    isQuasiCompactSpace_preimage_of_isQuasiCompact B S hS W.2 hsq.isAlgebraicSpace fV
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ W.2 hWqs
        (IsAffineSpace.isQuasiCompactSpace hVa) fV) hUo hUoqc
  let ι₀ := openSubspaceHom B S hS (W := Vs) V₀ hV₀
  have hι₀ : IsEtale B S hS ι₀.hom := isEtale_openSubspaceHom B S hS (W := Vs) V₀ hV₀
  let σ₀ : openSubspaceSpace B S hS (W := Vs) V₀ hV₀ ⟶ openSubspaceSpace B S hS Uo hUo :=
    ObjectProperty.homMk (Uo.fromPreimage fV)
  have e₁ : σ₀ ≫ j = ι₀ ≫ f := ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι Uo fV)
  have hι₀f : IsEtale B S hS (ι₀ ≫ f).hom := isEtale_comp B S hS hι₀ hf
  have hσ₀j : IsEtale B S hS (σ₀ ≫ j).hom := e₁ ▸ hι₀f
  have hσ₀ : IsEtale B S hS σ₀.hom :=
    @isEtale_of_comp_mono B S hS _ _ _ σ₀.hom Uo.ι (Subfunctor.instMonoFunctorTypeι Uo) hσ₀j
  obtain ⟨A, hAq, hAf, hBA⟩ := exists_le_etaleSubmoduleRestrict_of_finiteTypeGermExhaustion hPU
    (isQuasicoherentOnSite_etaleModulePullback B S hS j hj F hF) σ₀ hσ₀ hV₀qc _
    (isQuasicoherentOnSite_isFiniteType_etaleSubmoduleCompToIter_congr B S hS ι₀ hι₀ f hf σ₀ hσ₀
      j hj e₁.symm hι₀f hσ₀j Bm hBq hBf).2
  have hB₂A : etaleSubmoduleCongr B S hS e₁.symm hι₀f hσ₀j
      (etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f Bm) ≤
        etaleSubmoduleAlong B S hS σ₀ hσ₀ j hj hσ₀j A :=
    SheafOfModules.Submodule.le_iff.2 fun Z _ hy => SheafOfModules.Submodule.le_iff.1 hBA Z hy
  have hCm := isQuasicoherentOnSite_isFiniteType_etaleSubmoduleCompToIter_congr B S hS
    σ₀ hσ₀ j hj ι₀ hι₀ f hf e₁ hσ₀j hι₀f A hAq hAf
  obtain ⟨C, hCq, hCf, hC⟩ := extensionProperty_of_isAffineSpace B S hS hZ Vs hVa _ hFf V₀ hV₀
    hV₀qc _ hCm.1 hCm.2
  have hC' : etaleSubmoduleAlong B S hS ι₀ hι₀ f hf hι₀f C = etaleSubmoduleCongr B S hS e₁ hσ₀j
      hι₀f (etaleSubmoduleAlong B S hS σ₀ hσ₀ j hj hσ₀j A) :=
    congrArg (etaleSubmoduleIterToComp B S hS ι₀ hι₀ f hf hι₀f) hC
  have hagree : EdsGermAgree B S hS hsq Uo hUo A (C ⊔ Bm) := by
    intro x' t' u'
    obtain ⟨t₁, p₁, h₁⟩ := exists_geometricPointLift_preimage B S hS f hUo hV₀ t' u'
    have hCA := etaleGermSet_eq_of_etaleSubmoduleAlong_eq B S hS ι₀ hι₀ f hf σ₀ hσ₀ j hj e₁ hι₀f
      hσ₀j hC' t' u' t₁ p₁ h₁
    exact Set.Subset.antisymm (etaleGermSet_sup_subset B S hS f hf j hj C Bm A t' u' hCA.le
      (etaleGermSet_subset_of_etaleSubmoduleCongr_le B S hS ι₀ hι₀ f hf σ₀ hσ₀ j hj e₁.symm hι₀f
        hσ₀j hB₂A t' u' t₁ p₁ h₁))
      (hCA.symm.subset.trans (etaleGermSet_mono B S hS f hf le_sup_left t'))
  exact exists_mem_submoduleGermSet_of_edsGermAgree hsq ⟨hAq, hAf⟩
    (isQuasicoherentOnSite_isFiniteType_sup B S hS hFf C Bm ⟨hCq, hCf⟩ ⟨hBq, hBf⟩) hagree t
    (etaleGermSet_mono B S hS f hf le_sup_right t hBx)

/-- **The induction step.**  Let `(Uo ⊆ W, f : V ⟶ W)` be an elementary distinguished square
with `W` quasi-compact and quasi-separated, `Uo` quasi-compact and `V` affine.  If `Uo` and `V`
have the exhaustion property, so does `W`: a geometric point of `W` lies in `Uo` or lifts to
`V`. -/
theorem finiteTypeGermExhaustion_of_isElementaryDistinguishedSquare
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
    (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)
    (hWqc : IsQuasiCompactSpace B S hS W.1) (hWqs : IsAbsolutelyQuasiSeparated B S hS hZ W.1)
    (hUoqc : IsQuasiCompactSpace B S hS Uo.toFunctor) (hVa : IsAffineSpace B S hS V)
    (hPU : FiniteTypeGermExhaustion B S hS (openSubspaceSpace B S hS Uo hsq.isOpenSubspace))
    (hPV : FiniteTypeGermExhaustion B S hS (edsEtale B S hS hsq)) :
    FiniteTypeGermExhaustion B S hS W := by
  intro F hF x Vc p s
  by_cases hx : Nonempty (GeometricPointLift B S hS
    (openSubspaceHom B S hS Uo hsq.isOpenSubspace).hom x)
  · exact exists_mem_submoduleGermSet_of_lift_openSubspace hZ hWqc hWqs hsq.isOpenSubspace hUoqc
      hPU hF hx.some Vc p s
  · have hxo : x.image ∉ Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) := fun h =>
      hx ((nonempty_geometricPointLift_ι_iff_mem_range_pointsMap B S hS W.2 Uo
        hsq.isOpenSubspace x).2 h)
    obtain ⟨t⟩ := nonempty_geometricPointLift_of_notMem_range_pointsMap B S hS W.2 Uo fV hsq x hxo
    exact exists_mem_submoduleGermSet_of_lift_edsEtale hZ hsq hWqs hUoqc hVa hPU hPV hF t Vc p s

end Step

/-- **Every quasi-compact and quasi-separated algebraic space has the exhaustion property**, by
the induction principle of Stacks 08GP: every germ of a quasi-coherent module at a geometric
point is a germ of one of its quasi-coherent submodules of finite type. -/
theorem finiteTypeGermExhaustion_of_isQuasiCompactSpace (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    FiniteTypeGermExhaustion B S hS X :=
  qcqs_induction_on_self B S hS hZ X hXqc hXqs
    (fun Y _ => ∀ hY : IsAlgebraicSpace B S hS Y, FiniteTypeGermExhaustion B S hS ⟨Y, hY⟩)
    (fun V hVa hY => finiteTypeGermExhaustion_of_isAffineSpace (X := ⟨V.1.left.1, hY⟩) hVa)
    (fun W _ _ _ _ hsq hWqc hWqs hUqc hVa hPU hPV _ hY =>
      finiteTypeGermExhaustion_of_isElementaryDistinguishedSquare hZ (W := ⟨W.1.left.1, hY⟩)
        hsq hWqc hWqs hUqc hVa (hPU _) (hPV _)) X.2

/-- **A finite type submodule of the restriction to a quasi-compact étale space lies in the
restriction of a finite type quasi-coherent submodule.**  Let `X` be a quasi-compact and
quasi-separated algebraic space, `ℱ` a quasi-coherent `𝒪_X`-module, `g : Y ⟶ X` étale with `Y`
quasi-compact and `𝒢 ⊆ ℱ|_Y` a submodule of finite type.  Then there is a quasi-coherent
submodule `𝒦 ⊆ ℱ` of finite type with `𝒢 ⊆ 𝒦|_Y`.

This is the step of the proof of Stacks 085M which the source takes from the colimit assertion of
Stacks 0829; it is proved here without Stacks 07V9. -/
theorem exists_finiteType_le_etaleSubmoduleRestrict (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {F : Modules.{u, u} B S hS X.1 X.2} (hF : F.IsQuasicoherentOnSite)
    {Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (G : ((etaleModulePullback.{u, u} B S hS g hg).obj F).Submodule)
    (hGf : G.toSheafOfModules.IsFiniteType) :
    ∃ K : F.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
      K.toSheafOfModules.IsFiniteType ∧ G ≤ etaleSubmoduleRestrict B S hS g hg K :=
  exists_le_etaleSubmoduleRestrict_of_finiteTypeGermExhaustion
    (finiteTypeGermExhaustion_of_isQuasiCompactSpace B S hS hZ X hXqc hXqs) hF g hg hYqc G hGf

end AlgebraicGeometry.Space

end
