module

public import StacksFrontier.AlgebraicGeometry.AmpleLocalGeneration.FromExtension
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.RelativelyAmple.AffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceImmersionTwistVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The support of the direct image of the twists along a projective immersion

Let `D : h_Z ⟶ X ×_S P^n_S` be a closed immersion of algebraic spaces over `S` whose source is
represented by an object `Z` of the big fppf site and whose composite with the coordinates is
`h_k` for `k : Z ⟶ P^n_S`, as in
`AlgebraicGeometry.Space.ProjectiveSpaceImmersion.exists_isZero_rightDerived_twistPow`; let
`q : h_Z ⟶ X` be the composite with the projection and `ℒ = k^* 𝒪_{P^n_S}(1)`.  If `X` is
quasi-compact, then for `d ≫ 0` the support of `q_* ((𝒪_Z ⊗ ℒ^{⊗ d})^a)` contains the image of
`|q|`.

## Main results

* `AlgebraicGeometry.Space.supportOfSheaf_representedAssociatedModule_eq_univ`: the associated
  module `M^a` of an invertible module `M` on the scheme underlying an object `T` of the site has
  full support on `h_T`.
* `AlgebraicGeometry.Space.image_supportOfSheaf_subset_supportOfSheaf_modulePushforward_of_epi`:
  for `f : X ⟶ Y` and an `𝒪_X`-module `N` which is a quotient of the inverse image of an
  `𝒪_Y`-module, `|f|(Supp N) ⊆ Supp(f_* N)`.
* `AlgebraicGeometry.Space.ProjectiveSpaceImmersion.exists_range_subset_supportOfSheaf_twistPow`:
  the statement above.

## References

* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01VT](https://stacks.math.columbia.edu/tag/01VT)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 071Z](https://stacks.math.columbia.edu/tag/071Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The associated module of an invertible module has full support.**  For an invertible
module `M` on the scheme underlying an object `T` of the site, the support of `M^a` on `h_T` is
everything. -/
theorem supportOfSheaf_representedAssociatedModule_eq_univ (T : BigFppfOver B S hS)
    (M : ((BigFppfOver.toScheme B S hS).obj T).Modules)
    [hM : IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj T) M] :
    supportOfSheaf B S hS (yoneda.obj T) ((SheafOfModules.toSheaf _).obj
      ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj M)) =
      Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  let T₀ := (BigFppfOver.toScheme B S hS).obj T
  have : Stacks.SheafOfModules.IsInvertible T₀.presheaf
      (structureSheafRing T₀.toRingedSpace).property M :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ M).mpr hM
  obtain ⟨Uo, hUo, he⟩ := Stacks.Modules.exists_restrict_iso_unit_of_isInvertible (Y := T₀) M
  let y := pointsEquivScheme B S hS T x
  obtain ⟨z, hz⟩ : ∃ z, y ∈ Uo z := TopologicalSpace.Opens.mem_iSup.1 (by rw [hUo]; trivial)
  obtain ⟨e⟩ := he z
  let Ac := selfChart B S hS T
  let W' : BigFppfOver B S hS := chartOpenOver B S hS Ac (Uo z)
  let q : W' ⟶ T := chartOpenOverι B S hS Ac (Uo z)
  have hTq : (BigFppfOver.toScheme B S hS).map q = (Uo z).ι := rfl
  have : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map q) :=
    hTq ▸ Scheme.Opens.instIsOpenImmersionι (U := Uo z)
  have hqφ : IsEtale B S hS (representedSpaceMap B S hS q).hom :=
    isEtale_schemeSpaceMap B S hS _ q inferInstance
  let y' : (BigFppfOver.toScheme B S hS).obj W' := ⟨y, hz⟩
  let x' := (pointsEquivScheme B S hS W').symm y'
  have hx' : pointsMap B S hS (yoneda.obj W') (representedSpaceMap B S hS q).hom x' = x := by
    apply (pointsEquivScheme B S hS T).injective
    change pointsToScheme B S hS T (pointsMap B S hS _ (yoneda.map q) _) = _
    rw [pointsToScheme_pointsMap_yoneda]
    change (BigFppfOver.toScheme B S hS).map q
      ((pointsEquivScheme B S hS W') ((pointsEquivScheme B S hS W').symm y')) = y
    rw [Equiv.apply_symm_apply]
    rfl
  have hsupp := supportOfSheaf_toSheaf_etaleModulePullback B S hS (representedSpaceMap B S hS q)
    hqφ ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj M)
  let E : (etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS q) hqφ).obj
      ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj M) ≅
      structureSheafModule B S hS ⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ :=
    (representedAssociatedModuleEtalePullbackIso B S hS q hqφ).app M ≪≫
      (representedAssociatedModule B S hS W' (isAlgebraicSpace_yoneda B S hS W')).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback ((BigFppfOver.toScheme B S hS).map q)).symm.app
          M ≪≫ e) ≪≫
      representedAssociatedModuleObjUnitIso B S hS W' (isAlgebraicSpace_yoneda B S hS W')
  have h1 : x' ∈ supportOfSheaf B S hS (yoneda.obj W') ((SheafOfModules.toSheaf _).obj
      ((etaleModulePullback.{u, u} B S hS (representedSpaceMap B S hS q) hqφ).obj
        ((representedAssociatedModule B S hS T (isAlgebraicSpace_yoneda B S hS T)).obj M))) := by
    rw [supportOfSheaf_eq_of_iso B S hS ⟨yoneda.obj W', isAlgebraicSpace_yoneda B S hS W'⟩ E,
      supportOfSheaf_structureSheafModule]
    trivial
  rw [hsupp] at h1
  rwa [← hx']

/-- **The image of the support of a quotient of an inverse image lies in the support of the direct
image.**  Let `f : X ⟶ Y` be a morphism of algebraic spaces, `N` an `𝒪_X`-module and
`g : f^* A ⟶ N` an epimorphism from the inverse image of an `𝒪_Y`-module.  Then
`|f|(Supp N) ⊆ Supp(f_* N)`. -/
theorem image_supportOfSheaf_subset_supportOfSheaf_modulePushforward_of_epi
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (N : Modules.{u, u} B S hS X.1 X.2)
    (A : Modules.{u, u} B S hS Y.1 Y.2) (g : (modulePullback B S hS f).obj A ⟶ N) [Epi g] :
    pointsMap B S hS X.1 f.hom '' supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj N) ⊆
      supportOfSheaf B S hS Y.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS f).obj N)) := by
  let adj := modulePullbackAdjunction B S hS f
  have hfac : (modulePullback B S hS f).map (adj.homEquiv A N g) ≫ adj.counit.app N = g :=
    (adj.homEquiv_counit (g := adj.homEquiv A N g)).symm.trans
      ((adj.homEquiv A N).symm_apply_apply g)
  have : Epi (adj.counit.app N) := epi_of_epi_fac hfac
  rintro _ ⟨x, hx, rfl⟩
  exact supportOfSheaf_modulePullback_subset_preimage B S hS f _
    (supportOfSheaf_toSheaf_subset_of_epi B S hS X (adj.counit.app N) hx)

/-- **The support of the direct image of a globally generated associated module.**  For a
morphism `ψ : W ⟶ U` of the site and a module `F` on the scheme underlying `W` generated by a
family of global sections, `|h_ψ|(Supp F^a) ⊆ Supp((h_ψ)_* F^a)`. -/
theorem image_supportOfSheaf_subset_supportOfSheaf_modulePushforward_of_generatingSections
    {W U : BigFppfOver B S hS} (ψ : W ⟶ U) (F : ((BigFppfOver.toScheme B S hS).obj W).Modules)
    (σ : F.GeneratingSections) [Finite σ.I] :
    pointsMap B S hS (yoneda.obj W) (yoneda.map ψ) '' supportOfSheaf B S hS (yoneda.obj W)
        ((SheafOfModules.toSheaf _).obj
          ((representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).obj F)) ⊆
      supportOfSheaf B S hS (yoneda.obj U) ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS (representedSpaceMap B S hS ψ)).obj
          ((representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)).obj F))) := by
  let Ψ := representedSpaceMap B S hS ψ
  let repW := representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)
  let OU := structureSheafModule B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  have hcolim (V : BigFppfOver B S hS) :
      HasColimitsOfShape (Discrete σ.I)
        (Modules.{u, u} B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V)) :=
    @hasColimitsOfShape_discrete _ _ (@hasFiniteCoproducts_of_hasFiniteBiproducts _ _ _
      (@Abelian.hasFiniteBiproducts _ _ (SheafOfModules.instAbelian _))) σ.I _
  have := hcolim U
  have := hcolim W
  have : PreservesColimitsOfShape (Discrete σ.I) (modulePullback B S hS Ψ) :=
    (modulePullbackAdjunction B S hS Ψ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete σ.I) repW :=
    (representedAssociatedModuleZariskiAdjunction B S hS W).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  have hrepW : repW.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (representedAssociatedModuleZariskiAdjunction B S hS W)
  let e : (modulePullback B S hS Ψ).obj (∐ fun _ : σ.I => OU) ≅
      repW.obj (SheafOfModules.free σ.I) :=
    PreservesCoproduct.iso (modulePullback B S hS Ψ) (fun _ : σ.I => OU) ≪≫
      Sigma.mapIso (fun _ => modulePullbackUnitIso B S hS Ψ) ≪≫
      Sigma.mapIso (fun _ => (representedAssociatedModuleObjUnitIso B S hS W
        (isAlgebraicSpace_yoneda B S hS W)).symm) ≪≫
      (PreservesCoproduct.iso repW (fun _ : σ.I => SheafOfModules.unit _)).symm
  have : Epi (repW.map σ.π) := @Functor.map_epi _ _ _ _ repW hrepW _ _ σ.π σ.epi
  have hep : Epi (e.hom ≫ repW.map σ.π) :=
    @epi_comp _ _ _ _ _ e.hom (IsIso.epi_of_iso e.hom) _ this
  exact @image_supportOfSheaf_subset_supportOfSheaf_modulePushforward_of_epi B S hS _ _ Ψ _ _
    (e.hom ≫ repW.map σ.π) hep

namespace ProjectiveSpaceImmersion

variable {B S hS} {n : ℕ} {hP : B.Contains (projectiveSpaceOver n S)} {X : AlgebraicSpaces B S hS}
  {Z : BigFppfOver B S hS}

/-- **The support of the direct image of the twists contains the image, for `d ≫ 0`.**  If `X`
is quasi-compact, there is `d₁` such that for every `d ≥ d₁` the support of
`q_* ((𝒪_Z ⊗ ℒ^{⊗ d})^a)` contains the image of `|q|`, where `q = D.hom` and
`ℒ = k^* 𝒪_{P^n_S}(1)`. -/
theorem exists_range_subset_supportOfSheaf_twistPow
    (D : ProjectiveSpaceImmersion B S hS n hP ⟨yoneda.obj Z, isAlgebraicSpace_yoneda B S hS Z⟩ X)
    (k : Z ⟶ projectiveSpaceSiteObj B S hS n hP) (hk : (D.imm ≫ D.coord).hom = yoneda.map k)
    (hX : IsQuasiCompactSpace B S hS X.1) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      Set.range (pointsMap B S hS (yoneda.obj Z) D.hom.hom) ⊆
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
          ((modulePushforward B S hS D.hom).obj
            ((representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
              (twistPow k d)))) := by
  let T := BigFppfOver.toScheme B S hS
  have hq := D.relativelyRepresentable_hom
  obtain ⟨U, f, hU, hsurj, het⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hX
  let V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk f, isEtaleChart_of_isEtale B S hS f het⟩
  have : IsAffine (T.obj V.1.left) := hU
  obtain ⟨π, hπ, hproj, hample⟩ := exists_chart_isRelativelyAmple D k hk V
  let ψ := hq.snd V.1.hom
  let W := hq.pullback V.1.hom
  let L' := (Scheme.Modules.pullback (T.map π)).obj (schemeTwist k)
  have hamp : IsAmple (T.obj W) L' :=
    (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple (T.obj W) L').1
      (Scheme.Modules.isAmple_of_isRelativelyAmple (T.map ψ) L' hample)
  obtain ⟨n₀, hn₀⟩ := Stacks.AmpleLocalGeneration.isEventuallyGloballyGenerated_of_isAmple L' hamp
    (unitModule (T.obj W)) inferInstance inferInstance
  refine ⟨n₀.toNat, fun d hd => ?_⟩
  obtain ⟨σ, hσ⟩ := hn₀ d (by omega)
  let FW := Stacks.RelativeVeryAmple.tensorModules (T.obj W) (unitModule (T.obj W))
    (tensorPowModule (T.obj W) L' (d : ℤ))
  let eT := Stacks.AmplePullbackPart1.tensorIsoTensorModules (T.obj W) (unitModule (T.obj W))
    (tensorPowModule (T.obj W) L' (d : ℤ))
  let σ' : FW.GeneratingSections :=
    @SheafOfModules.GeneratingSections.ofEpi _ _ _ _ _ _ _ _ σ eT.hom
      (@IsIso.epi_of_iso _ _ _ _ eT.hom (Iso.isIso_hom eT))
  have : Finite σ'.I := hσ
  let i : schemeSpace U ⟶ X := ObjectProperty.homMk f
  have sq : IsPullback (representedSpaceMap B S hS π) (representedSpaceMap B S hS ψ) D.hom i := by
    refine IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ ?_) ?_
    · change yoneda.map π ≫ D.hom.hom = yoneda.map ψ ≫ f
      rw [hπ]
      exact hq.w V.1.hom
    · change IsPullback (yoneda.map π) (yoneda.map ψ) D.hom.hom f
      rw [hπ]
      exact hq.isPullback V.1.hom
  have hφ : IsEtale B S hS (representedSpaceMap B S hS π).hom :=
    isEtale_of_isPullback B S hS _ _ i D.hom sq.flip het
  let N := (representedAssociatedModule B S hS Z (isAlgebraicSpace_yoneda B S hS Z)).obj
    (twistPow k d)
  let repW := representedAssociatedModule B S hS W (isAlgebraicSpace_yoneda B S hS W)
  let e₁₂ : (etaleModulePullback B S hS (representedSpaceMap B S hS π) hφ).obj N ≅ repW.obj FW :=
    (representedAssociatedModuleEtalePullbackIso B S hS π hφ).app (twistPow k d) ≪≫
      repW.mapIso (pullbackTwistPowIso k (T.map π) d)
  have : IsInvertibleModule (T.obj Z) (twistPow k d) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules (T.obj Z) (unitModule (T.obj Z))
      (tensorPowModule (T.obj Z) (schemeTwist k) (d : ℤ))
  have hNsupp := supportOfSheaf_representedAssociatedModule_eq_univ B S hS Z (twistPow k d)
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj W) (isAlgebraicSpace_yoneda B S hS W)
  have := hasInjectiveResolutions_modules B S hS (yoneda.obj Z) (isAlgebraicSpace_yoneda B S hS Z)
  have := modulePushforward_additive B S hS (representedSpaceMap B S hS ψ)
  have := modulePushforward_additive B S hS D.hom
  have := preservesFiniteLimits_modulePushforward B S hS D.hom
  have := preservesFiniteLimits_modulePushforward B S hS (representedSpaceMap B S hS ψ)
  let ebc : (modulePushforward B S hS (representedSpaceMap B S hS ψ)).obj (repW.obj FW) ≅
      (etaleModulePullback B S hS i het).obj ((modulePushforward B S hS D.hom).obj N) :=
    (modulePushforward B S hS (representedSpaceMap B S hS ψ)).mapIso e₁₂.symm ≪≫
      ((modulePushforward B S hS (representedSpaceMap B S hS ψ)).rightDerivedZeroIsoSelf.app
        _).symm ≪≫
      (moduleHigherPushforwardEtaleBaseChangeIso B S hS (representedSpaceMap B S hS π)
        (representedSpaceMap B S hS ψ) D.hom i sq het 0).app N ≪≫
      (etaleModulePullback B S hS i het).mapIso
        ((modulePushforward B S hS D.hom).rightDerivedZeroIsoSelf.app N)
  rintro _ ⟨z, rfl⟩
  obtain ⟨u, hu⟩ := (surjective_iff_surjective_pointsMap B S hS X.1 X.2 U f).1 hsurj
    (pointsMap B S hS (yoneda.obj Z) D.hom.hom z)
  obtain ⟨w, -, hwu⟩ := exists_point_of_isPullback B S hS sq z u hu.symm
  have hw : w ∈ supportOfSheaf B S hS (yoneda.obj W) ((SheafOfModules.toSheaf _).obj
      (repW.obj FW)) := by
    rw [← supportOfSheaf_eq_of_iso B S hS ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩ e₁₂,
      supportOfSheaf_toSheaf_etaleModulePullback, hNsupp]
    trivial
  have hu' := image_supportOfSheaf_subset_supportOfSheaf_modulePushforward_of_generatingSections
    B S hS ψ FW σ' ⟨w, hw, rfl⟩
  replace hu' := (Set.ext_iff.1 (supportOfSheaf_eq_of_iso B S hS (schemeSpace U) ebc) _).1 hu'
  replace hu' := (Set.ext_iff.1 (supportOfSheaf_toSheaf_etaleModulePullback B S hS i het
    ((modulePushforward B S hS D.hom).obj N)) _).1 hu'
  rw [← hu, ← hwu]
  exact hu'

end ProjectiveSpaceImmersion

end AlgebraicGeometry.Space

end
