module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedGlobalSectionsCoproductsAffine

/-!
# The cohomology of a quasi-compact quasi-separated algebraic space is uniformly bounded

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `RΓ` be
a right derived functor of the global sections `Γ(X, −) : Mod(𝒪_X) ⥤ Ab`. There is one integer
`N` such that `RΓ` carries every object of `D_QCoh(𝒪_X)` living in degrees `≤ c` to an object
living in degrees `≤ c + N`.

On an affine `Y` étale over `X`, `Γ(X, y_* −)` is the sections functor at the terminal chart of
`Y`, which has no higher derived functors on quasi-coherent modules ([Stacks, Tag 03DW]); so by
[Stacks, Tag 08F7] (3) with `N = 1` its right derived functor carries `D^{≤ c}_QCoh(𝒪_Y)` into
`D^{≤ c}(Ab)`. The induction principle of [Stacks, Tag 08GP]
(`AlgebraicGeometry.Space.exists_isLE_derivedPushforward_of_affine`) globalises this.

## Main results

* `AlgebraicGeometry.Space.isLE_rightDerived_pushforwardGlobalSections_of_isAffineSpace`: the
  affine case.
* `AlgebraicGeometry.Space.exists_isLE_rightDerived_baseRingGlobalSections`: the uniform bound.

## References

* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasColimitsOfShape_discrete_derivedCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **On an affine space, global sections of a direct image do not raise an upper bound on
`D_QCoh`.** Let `y : Y ⟶ X` with `Y` affine and `RF` a right derived functor of
`Γ(X, y_* −) : Mod(𝒪_Y) ⥤ Ab`. If `E ∈ D_QCoh(𝒪_Y)` lives in degrees `≤ c`, so does `RF E`:
`Γ(X, y_* −)` is the sections functor at the terminal chart of `Y`, without higher derived
functors on quasi-coherent modules, and Stacks 08F7 (3) applies with `N = 1`. -/
theorem isLE_rightDerived_pushforwardGlobalSections_of_isAffineSpace {X Y : AlgebraicSpaces B S hS}
    (y : Y ⟶ X) {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)
    (hY : IsAffineSpace B S hS Y.1)
    (RF : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : (modulePushforward B S hS y ⋙
        baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS Y.1 Y.2) (ComplexShape.up ℤ))]
    (E : DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2)) (hE : qcohDerivedProp B S hS Y E)
    (c : ℤ) (hc : E.IsLE c) : (RF.obj E).IsLE c := by
  obtain ⟨T, hT, ⟨e⟩⟩ := hY
  have hU := isTerminal_isoChart B S hS e.symm
  have hUaff : IsAffineChart B S hS Y.1 (isoChart B S hS e.symm) := hT
  let F := modulePushforward B S hS y ⋙ baseRingGlobalSectionsAddCommGrp B S hS X φ
  let eF : F ≅ Stacks.Cohomology.SiteInverseLimits.sectionsFunctor
      (smallEtaleRingedSite B S hS Y.1 Y.2) (isoChart B S hS e.symm) :=
    pushforwardGlobalSectionsIsoOfIsTerminal B S hS y φ hU
  have hgr := isGrothendieckAbelian_modules B S hS Y.1 Y.2
  have := enoughInjectives_modules B S hS Y.1 Y.2
  have := (modulePullbackAdjunction B S hS y).isRightAdjoint
  have := (baseRingTensorModuleAdjunction B S hS X φ).isRightAdjoint
  have : PreservesLimitsOfShape (Discrete ℕ) F := inferInstanceAs (PreservesLimitsOfShape
    (Discrete ℕ) (modulePushforward B S hS y ⋙ baseRingGlobalSectionsModule B S hS X φ ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))
  have hvan : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj M) := fun M hM n hn ↦
    (isZero_rightDerived_sectionsFunctor_of_isAffineChart B S hS Y.1 Y.2 M hM _ hUaff n hn).of_iso
      { hom := (NatTrans.rightDerived eF.hom n).app M
        inv := (NatTrans.rightDerived eF.inv n).app M
        hom_inv_id := by simp [← NatTrans.comp_app, ← NatTrans.rightDerived_comp]
        inv_hom_id := by simp [← NatTrans.comp_app, ← NatTrans.rightDerived_comp] }
  have hRF : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, ((1 : ℕ) : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M) := by
    intro M hM p hp
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    exact (hvan M hM n (by omega)).of_iso (CategoryTheory.rightDerivedPlusObjIso F M n)
  have h := isLE_rightDerived_obj_of_isLE B S hS Y.1 Y.2 F RF α 1 hRF E hE c hc
  simpa using h

/-- **The cohomology of a quasi-compact quasi-separated algebraic space is uniformly bounded on
`D_QCoh`.** Let `X` be quasi-compact and quasi-separated and `RΓ` a right derived functor of
`Γ(X, −) : Mod(𝒪_X) ⥤ Ab` (read through any ring map `φ : R →+* Γ(X, 𝒪_X)`). There is an
integer `N` such that `RΓ` carries every object of `D_QCoh(𝒪_X)` living in degrees `≤ c` to an
object living in degrees `≤ c + N`. The affine case is
`AlgebraicGeometry.Space.isLE_rightDerived_pushforwardGlobalSections_of_isAffineSpace`; the
induction is Stacks 08GP along the Mayer–Vietoris triangles of Stacks 08JK. -/
theorem exists_isLE_rightDerived_baseRingGlobalSections
    (hZ : B.Contains (⊤_ Scheme.{u})) {X : AlgebraicSpaces B S hS}
    (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    {R : Type u} [CommRing R] (φ : R →+* modelGlobalFunctions B S hS X)
    (RΓ : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ DerivedCategory AddCommGrpCat.{u})
    (α : (baseRingGlobalSectionsAddCommGrp B S hS X φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RΓ)
    [RΓ.IsRightDerivedFunctor α
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ))] :
    ∃ N : ℤ, ∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
      qcohDerivedProp B S hS X E → ∀ c : ℤ, E.IsLE c → (RΓ.obj E).IsLE (c + N) := by
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_modules B S hS X.1 X.2
  let _ := Functor.IsRightDerivedFunctor.commShift RΓ α
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) ℤ
  have : RΓ.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor _ RΓ α
  have hid : (𝟭 (DerivedCategory (Modules.{u, u} B S hS X.1 X.2))).IsRightDerivedFunctor
      (pushforwardIdMapHomotopyCategoryIso B S hS X).hom
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X.1 X.2) (ComplexShape.up ℤ)) :=
    Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
      _ DerivedCategory.Qh _ _ fun _ _ ↦ inferInstance
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_of_affine B S hS hZ hXqc hXqs (𝟙 X) RΓ
    (fun Y => qcohDerivedProp B S hS Y)
    (fun e he K hK => derivedQuasicoherent_etaleModulePullback B S hS e he K hK)
    (fun Y y hy hY K hK c hc R αR hR ↦
      have := hR
      have := isRightDerivedFunctor_comp_derivedPushforward B S hS (y ≫ 𝟙 X)
        (by simpa using hy) (baseRingGlobalSectionsAddCommGrp B S hS X φ) R αR RΓ α
      isLE_rightDerived_pushforwardGlobalSections_of_isAffineSpace B S hS (y ≫ 𝟙 X) φ hY
        (R ⋙ RΓ)
        (pushforwardCompRightDerivedUnit B S hS (y ≫ 𝟙 X)
          (baseRingGlobalSectionsAddCommGrp B S hS X φ) R αR RΓ α) K hK c hc)
  exact ⟨N, fun E hE c hc => hN E hE c hc (𝟭 _) (pushforwardIdMapHomotopyCategoryIso B S hS X).hom
    hid⟩

end AlgebraicGeometry.Space

end
