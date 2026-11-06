module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.BaseChangeMapBoundedBelow
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsOpenImmersionBaseChange

/-!
# The base change map of `D(-_étale, Λ)` and its descent to `D⁺`, after any functor

The theorem
`EtaleCoefficients.isIso_baseChangeMap_app_iff_isIso_derivedBaseChangePlus_app` says that at a
bounded below object `K` the unbounded base change map
`Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap` and its descent `derivedBaseChangePlus` to
`D⁺` are invertible together. Both are, at a bounded below complex of injectives, the localized
degreewise comparison followed by a unit, up to isomorphisms on both sides; so the same holds after
applying **any functor** `H` out of the unbounded derived category
(`isIso_map_baseChangeMap_app_iff_isIso_map_ι_map_derivedBaseChangePlus_app`). With `H` a derived
direct image this compares the derived direct images of the two maps.

## References

* [Stacks Project, Tag 0F1H](https://stacks.math.columbia.edu/tag/0F1H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- If `u₁ ≫ φ ≫ u₂ = c ≫ ψ ≫ d` with `u₁`, `u₂`, `c`, `d` invertible, then `H(φ)` is invertible
exactly when `H(ψ)` is, for any functor `H`. -/
theorem isIso_map_iff_of_comp_eq {𝒞 ℰ : Type*} [Category* 𝒞] [Category* ℰ] (H : 𝒞 ⥤ ℰ)
    {X₀ X₁ X₂ X₃ Y₁ Y₂ : 𝒞} (u₁ : X₀ ⟶ X₁) (φ : X₁ ⟶ X₂) (u₂ : X₂ ⟶ X₃) (c : X₀ ⟶ Y₁)
    (ψ : Y₁ ⟶ Y₂) (d : Y₂ ⟶ X₃) (hu₁ : IsIso u₁) (hu₂ : IsIso u₂) (hc : IsIso c) (hd : IsIso d)
    (h : u₁ ≫ φ ≫ u₂ = c ≫ ψ ≫ d) : IsIso (H.map φ) ↔ IsIso (H.map ψ) := by
  have h' := congrArg H.map h
  simp only [Functor.map_comp] at h'
  rw [← isIso_comp_left_iff (H.map u₁), ← isIso_comp_right_iff _ (H.map u₂), Category.assoc, h',
    isIso_comp_left_iff, isIso_comp_right_iff]

/-- If `φ ≫ u = c ≫ ψ` with `u` and `c` invertible, then `H(φ)` is invertible exactly when `H(ψ)`
is, for any functor `H`. -/
private theorem isIso_map_iff_of_comp_eq_of_isIso {𝒞 ℰ : Type*} [Category* 𝒞] [Category* ℰ]
    (H : 𝒞 ⥤ ℰ) {X Y X' Y' : 𝒞} (φ : X ⟶ Y) (u : Y ⟶ Y') (c : X ⟶ X') (ψ : X' ⟶ Y')
    [IsIso u] [IsIso c] (h : φ ≫ u = c ≫ ψ) : IsIso (H.map φ) ↔ IsIso (H.map ψ) :=
  isIso_map_iff_of_comp_eq H (𝟙 _) φ u c ψ (𝟙 _) inferInstance inferInstance inferInstance
    inferInstance (by simpa using h)

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]


/-- **`isIso_app_ι_iff_isIso_derived_app` after any functor.** In the situation of
`Stacks.Cohomology.BaseChange.isIso_app_ι_iff_isIso_derived_app`, for every functor `H` out of
`D(D)` and every bounded below `K`, `H` of the transformation `bc` at `K` is invertible exactly
when `H` of the descent of `τ` at `K` is. -/
theorem isIso_map_app_ι_iff_isIso_map_ι_map_derived_app {ℰ : Type*} [Category* ℰ]
    (H : DerivedCategory D ⥤ ℰ)
    {gDp : DerivedCategory A ⥤ DerivedCategory B} {fD : DerivedCategory B ⥤ DerivedCategory D}
    {eD : DerivedCategory A ⥤ DerivedCategory C} {hDp : DerivedCategory C ⥤ DerivedCategory D}
    (bc : gDp ⋙ fD ⟶ eD ⋙ hDp)
    (ug : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ gDp)
    (uh : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ hDp)
    [hDp.IsRightDerivedFunctor uh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (cf : DerivedCategory.Qh ⋙ fD ⟶ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (ce : DerivedCategory.Qh ⋙ eD ⟶
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (τ : F ⋙ G ⟶ G' ⋙ F')
    (hfac : ∀ K, UnitFac DerivedCategory.Qh DerivedCategory.Qh bc ug uh cf ce
      (fun K => (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) K)
    (hug : ∀ L : CochainComplex.Plus (InjectiveObject A), IsIso (ug.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj))))
    (hcf : ∀ K, IsIso (cf.app K)) (hce : ∀ K, IsIso (ce.app K))
    (hres : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (K : DerivedCategory.Plus A) :
    IsIso (H.map (bc.app (DerivedCategory.Plus.ι.obj K))) ↔
      IsIso (H.map (DerivedCategory.Plus.ι.map
        ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app K))) := by
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff K n).1 hn
  obtain ⟨L, _, ⟨i⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let Kh := (HomotopyCategory.Plus.quotient A).obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)
  let j : DerivedCategory.Plus.Qh.obj Kh ≅ K :=
    (ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso A).app
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L).obj) :
      DerivedCategory.Plus.Qh.obj Kh ≅
        DerivedCategory.Plus.Q.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)) ≪≫ i
  refine (NatTrans.isIso_app_iff_of_iso (Functor.whiskerLeft DerivedCategory.Plus.ι
      (Functor.whiskerRight bc H)) j).symm.trans (Iff.trans ?_
    (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
      (Functor.whiskerRight (derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith))
        DerivedCategory.Plus.ι) H) j))
  simp only [Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let M := G'.mapHomotopyCategoryPlus.obj Kh
  have hug' : IsIso (ug.app ((HomotopyCategory.Plus.ι A).obj Kh)) := hug L
  have hcf' : IsIso (cf.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
    ((HomotopyCategory.Plus.ι A).obj Kh))) := hcf _
  have hce' : IsIso (ce.app ((HomotopyCategory.Plus.ι A).obj Kh)) := hce _
  have hf := hfac ((HomotopyCategory.Plus.ι A).obj Kh)
  unfold UnitFac at hf
  have h₁ := isIso_map_iff_of_comp_eq H _ (bc.app (DerivedCategory.Qh.obj
    ((HomotopyCategory.Plus.ι A).obj Kh))) _ _
    (DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app
      ((HomotopyCategory.Plus.ι A).obj Kh)) ≫
      uh.app ((G'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.Plus.ι A).obj Kh)))
    (𝟙 _) inferInstance inferInstance hcf' (IsIso.id _)
    (hf.trans (congrArg (_ ≫ ·) (Category.comp_id _).symm))
  have he := Functor.boundedDerivedIso_hom_app F' hDp uh hres M
  have h₂ : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh) ≫
        F'.rightDerivedFunctorPlusUnith.app M) ≫
      (Functor.boundedDerivedIso F' hDp uh hres).hom.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Qh.map ((mapPlus τ).app Kh).hom ≫
        uh.app ((HomotopyCategory.Plus.ι C).obj M) := by
    have h := congrArg (fun t => t ≫ (Functor.boundedDerivedIso F' hDp uh hres).hom.app
      (DerivedCategory.Plus.Qh.obj M)) (DerivedCategory.Plus.ι.map_comp
        (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh)) (F'.rightDerivedFunctorPlusUnith.app M))
    exact h.trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) he))
  have h₃ := isIso_map_iff_of_comp_eq_of_isIso H (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh) ≫ F'.rightDerivedFunctorPlusUnith.app M))
    ((Functor.boundedDerivedIso F' hDp uh hres).hom.app (DerivedCategory.Plus.Qh.obj M)) (𝟙 _)
    (DerivedCategory.Qh.map ((mapPlus τ).app Kh).hom ≫ uh.app ((HomotopyCategory.Plus.ι C).obj M))
    (h₂.trans (Category.id_comp _).symm)
  have hfac' := derived_fac_app F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith) Kh
  rw [onHomotopy_app] at hfac'
  have h₄ := isIso_map_iff_of_comp_eq (DerivedCategory.Plus.ι ⋙ H)
    (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app Kh))
    ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app
      (DerivedCategory.Plus.Qh.obj Kh)) (𝟙 _)
    ((asIso G.rightDerivedFunctorPlusUnith).inv.app (F.mapHomotopyCategoryPlus.obj Kh))
    (DerivedCategory.Plus.Qh.map ((mapPlus τ).app Kh) ≫ F'.rightDerivedFunctorPlusUnith.app M)
    (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app Kh))
    inferInstance (IsIso.id _) inferInstance inferInstance
    ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (hfac'.trans
      (congrArg (_ ≫ ·) (Category.assoc _ _ _).symm)))
  exact h₁.trans (h₃.symm.trans h₄.symm)

end Stacks.Cohomology.BaseChange

open AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable (Λ : Type (u + 1)) [CommRing Λ]
  {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The base change map of `D(-_étale, Λ)` and its descent to `D⁺`, after any functor**: for a
bounded below `K` and any functor `H` out of `D(X'_étale, Λ)`, `H` of `baseChangeMap` at `K` is
invertible exactly when `H` of `derivedBaseChangePlus` at `K` is. -/
theorem isIso_map_baseChangeMap_app_iff_isIso_map_ι_map_derivedBaseChangePlus_app
    {ℰ : Type*} [Category* ℰ] (H : DerivedModules Λ X' ⥤ ℰ)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))) :
    IsIso (H.map ((baseChangeMap Λ f' g h e w).app (DerivedCategory.Plus.ι.obj K))) ↔
      IsIso (H.map (DerivedCategory.Plus.ι.map ((derivedBaseChangePlus Λ f' g h e w).app K))) :=
  Stacks.Cohomology.BaseChange.isIso_map_app_ι_iff_isIso_map_ι_map_derived_app
    (ringedToposHom Λ g).pushforwardTopos (ringedToposHom Λ h).pushforwardTopos
    (ringedToposHom Λ f').pullbackTopos (ringedToposHom Λ e).pullbackTopos H
    (baseChangeMap Λ f' g h e w) (derivedPushforwardUnit (ringedToposHom Λ g))
    (derivedPushforwardUnit (ringedToposHom Λ h)) (derivedPullbackComparison (ringedToposHom Λ f'))
    (derivedPullbackComparison (ringedToposHom Λ e)) (moduleBaseChange Λ f' g h e w)
    (baseChangeMap_fac Λ f' g h e w)
    (fun L => isIso_derivedPushforwardUnit_app_of_isKInjective (ringedToposHom Λ g)
      (((InjectiveObject.ι (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)
      (inferInstanceAs (CochainComplex.IsKInjective (((InjectiveObject.ι (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj))))
    (isIso_derivedPullbackComparison_app_ringedToposHom Λ f')
    (isIso_derivedPullbackComparison_app_ringedToposHom Λ e)
    (exists_quasiIso_isKInjective (ringedTopos Λ Y)) K

/-- The base change map of `D(-_étale, Λ)` does not depend on the proof of commutativity of the
square. -/
theorem isIso_map_baseChangeMap_app_congr {X' S T Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S)
    (h : Y ⟶ X') (e : Y ⟶ T) (w w' : h ≫ f' = e ≫ g) {ℰ : Type*} [Category* ℰ]
    (H : DerivedModules Λ X' ⥤ ℰ) (K : DerivedModules Λ T)
    (hK : IsIso (H.map ((baseChangeMap Λ f' g h e w).app K))) :
    IsIso (H.map ((baseChangeMap Λ f' g h e w').app K)) := by
  have hw : w = w' := Subsingleton.elim _ _
  subst hw
  exact hK

/-- **The direct image of a morphism of `D⁺(X_étale, Λ)`, read on abelian sheaves.** If the
derived direct image along `c` of `φ` is invertible, so is `R⁺c_*` of the underlying morphism of
complexes of abelian sheaves (`pushforwardForgetPlusIso`). -/
theorem isIso_rightDerivedFunctorPlus_map_forgetDerivedPlus_map_of_isIso {X Z : Scheme.{u}}
    (c : X ⟶ Z) {A B : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O))} (φ : A ⟶ B)
    (hφ : IsIso ((pushforward Λ c).map (DerivedCategory.Plus.ι.map φ))) :
    IsIso ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
      ((forgetDerivedPlus Λ X).map φ)) := by
  have h₁ : IsIso ((DerivedCategory.Plus.ι ⋙ pushforward Λ c ⋙ forgetDerived Λ Z).map φ) := by
    show IsIso ((forgetDerived Λ Z).map ((pushforward Λ c).map (DerivedCategory.Plus.ι.map φ)))
    infer_instance
  have h₂ := (NatIso.isIso_map_iff (pushforwardForgetPlusIso Λ c) φ).1 h₁
  change IsIso (DerivedCategory.Plus.ι.map ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
    ((forgetDerivedPlus Λ X).map φ))) at h₂
  exact isIso_of_reflects_iso _ DerivedCategory.Plus.ι

/-- A sheaf of `ℤ/m`-modules placed in degree zero, in `D⁺(T_étale, ℤ/m)`. -/
abbrev singlePlus (m : ℕ) (T : Scheme.{u}) (F : SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)) :
    DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)) :=
  (DerivedCategory.Plus.singleFunctor _ 0).obj F

/-- The underlying complex of abelian sheaves of a sheaf of `ℤ/m`-modules placed in degree zero
is its underlying abelian sheaf placed in degree zero. -/
def forgetDerivedPlusSingleIso (m : ℕ) (T : Scheme.{u}) (F : SheafOfModules.{u + 1}
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O)) :
    (forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj (singlePlus m T F) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleToSheaf (ULift.{u + 1} (ZMod m)) T).obj F) :=
  mapDerivedCategoryPlusSingleFunctorObjIso _ F

/-- **The direct image of the abelian base change map and of the base change map of
`D⁺(-_étale, ℤ/m)`, on underlying complexes of abelian sheaves, are invertible together.** -/
theorem isIso_rightDerivedFunctorPlus_map_smallEtaleDerivedBaseChangeAb_app_iff (m : ℕ)
    {X' S T Y : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
    (w : h ≫ f' = e ≫ g) {Z : Scheme.{u}} (c : X' ⟶ Z)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app
          ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K))) ↔
      IsIso ((smallEtalePushforwardAb c).rightDerivedFunctorPlus.map
        ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) X').map
          ((derivedBaseChangePlus (ULift.{u + 1} (ZMod m)) f' g h e w).app K))) := by
  have hsq := Stacks.Cohomology.BaseChange.derived_exactTransport_app
    (hF := rightAcyclic_smallEtalePushforwardAb_etaleToSheaf _ g)
    (hF' := rightAcyclic_smallEtalePushforwardAb_etaleToSheaf _ h)
    (hG := fun _ _ => (smallEtalePullbackAb f').rightAcyclic_of_exact _)
    (hG' := fun _ _ => (smallEtalePullbackAb e).rightAcyclic_of_exact _)
    (moduleBaseChange_natTransCompat f' g h e w m) K
  exact (Stacks.Cohomology.BaseChange.isIso_map_iff_of_comp_eq_of_isIso
    (smallEtalePushforwardAb c).rightDerivedFunctorPlus _ _ _
    ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K))
    (hsq.trans (Category.assoc _ _ _).symm)).symm


end Stacks.EtaleCohomology.EtaleCoefficients

end
