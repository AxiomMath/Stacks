module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisHomOpEVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CyclotomicDualCoeffacement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionGalois

/-!
# Coeffacements of `M ↦ Γ^Gal(X̄, ℋom^•_ℤ(I_M, K))`

On a smooth geometrically connected curve `X` over `k`, for `m ≥ 1` every finite `Λ`-module `N`
with a continuous action of `π₁(X, x̄)` has an epimorphism `π' : N' ⟶ N` such that, for every
`π : N ⟶ M` and every lift `φ : I_{N'} ⟶ I_M` of `π' ≫ π` to injective resolutions of
`(j_! ℱ_-)[0]`, precomposition with `φ` is zero on `Hᵐ(Γ^Gal(X̄, ℋom^•_ℤ(-, K)))`
(`AlgebraicGeometry.galoisHomOpE_coeffacement`). Through `E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_-, ℱ_μ))`
(`AlgebraicGeometry.galoisHomOpECyclotomicDerivedIso`, taken natural in `M` as a hypothesis),
forgetting the Galois action (`Stacks.EtaleCohomology.galoisRightDerivedPlusForgetIso`) and
`ℋom_ℤ(ℱ_M, ℱ_μ) ≅ ℱ_{Hom(M, μ_n)}` (`AlgebraicGeometry.representationSheafHomOpNatIso`), the map
is `Hᵐ(X_k̄, ℱ_{Hom(π' ≫ π, μ_n)})`, which factors through `Hᵐ(X_k̄, ℱ_{Hom(π', μ_n)}) = 0`
(`AlgebraicGeometry.exists_epi_map_cyclotomicDual_eq_zero`).

This is the coeffacement input `hD` of the descending induction
`AlgebraicGeometry.quasiIso_poincarePairing` of Tag 03VM.

## References

* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry Stacks.GroupCohomology Stacks.Frobenius Stacks.EtaleCohomology
open Stacks.AbelianInternalHom Stacks.ConstantSheaf

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the coefficient
universe `0`. -/
local instance (priority := 3000) etaleModules_enoughInjectives_galoisHomOpECoeffacement
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, pinned at `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_galoisHomOpECoeffacement (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k))
  [IsCurve k f] [Smooth f] [GeometricallyConnected f] (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] [Algebra.IsAlgebraic k kbar] [Algebra.IsSeparable k kbar]
  [CompactSpace (kbar ≃ₐ[k] kbar)]
  (y : GeometricPoint (fieldBaseChange (Over.mk f) kbar)) (n : ℕ) [NeZero n]
  (j : CompactificationOf (Over.mk f))
  (K₀ : letI := connectedSpace_of_isCurve B X f
    CochainComplex.InjectiveResolution
      ((CochainComplex.singleFunctor _ 0).obj
        ((etaleModuleExtensionByZero (ZMod n) j.immersion).obj
          ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))))
  (Λ : Type) [Ring Λ] [Finite Λ] [Algebra (ZMod n) Λ]

/-- A morphism killed by one of two naturally isomorphic functors is killed by the other. -/
private theorem map_eq_zero_of_iso_of_map_eq_zero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {g : X ⟶ Y} (h : F.map g = 0) :
    G.map g = 0 := by
  rw [← NatIso.naturality_1 e g, h, zero_comp, comp_zero]

/-- **Coeffacements of `M ↦ Hᵐ(Γ^Gal(X̄, ℋom^•_ℤ(I_M, K)))` for `m ≥ 1`**, given the
naturality in `M` of `E ≅ RΓ^Gal(X, ℋom_ℤ(ℱ_M, ℱ_μ))` and the elementwise effaceability of
`P ↦ H^*(X_k̄, ℱ_P)` over `Λᵐᵒᵖ`, for `n = #Λ` invertible in `k`. -/
theorem galoisHomOpE_coeffacement [ConnectedSpace X.1] (hn : Nat.card Λ = n)
    (hΛ : IsUnit ((Nat.card Λ : ℕ) : k))
    (hEff : (geometricRepresentationCohomology.{u, 0} B X
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ f kbar).ElementwiseEffaceable)
    [K₀.cocomplex.IsStrictlyGE 0]
    (hG' : ∀ M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom)),
      IsFinitePresentationLocallyConstantModuleSheaf.{u + 1, u, 0, 0} X.1.smallEtaleTopology
        (ZMod n) ((etaleModuleRestrictScalars (algebraMap (ZMod n) Λ) X.1).obj
            ((representationSheaf B X
            (y.map (fieldBaseChangeObjProj B X f kbar
            (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M)))
    (hω : letI := connectedSpace_of_isCurve B X f
      Stacks.ModuleInternalHom.IsLocallyConstantInjective X.1.smallEtaleTopology (ZMod n)
        ((representationSheaf B X _ (ZMod n)).obj (cyclotomicContinuousModule B X f kbar y n)))
    (hnat : ∀ (M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) (π : N ⟶ M)
        (IM : CochainComplex.InjectiveResolution
        ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M))))
      (IN : CochainComplex.InjectiveResolution
        ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj N))))
              (φ : IN.cocomplex ⟶ IM.cocomplex)
              (_ : (IN.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map π)) ≫ IM.ι)),
      DerivedCategory.Q.map
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
          (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
              (cyclotomicIntResolution B X f kbar y n j K₀)) φ)) ≫
              (galoisHomOpECyclotomicDerivedIso B X f kbar y n j K₀ Λ N IN (hG' N) hω).hom =
        (galoisHomOpECyclotomicDerivedIso B X f kbar y n j K₀ Λ M IM (hG' M) hω).hom ≫
            (DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ
            (Over.mk f) kbar ⋙
          DerivedCategory.Plus.ι).map
              ((etaleHomOpRepresentationFunctor B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ n
              (cyclotomicContinuousModule B X f kbar y n)).map π.op))
    (m : ℕ) (hm : 1 ≤ m) (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ
        (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) :
    ∃ (N' : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) (π' : N' ⟶ N), Epi π' ∧
      ∀ (M : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1
          (y.map (fieldBaseChangeObjProj B X f kbar
          (contains_fieldBaseChange_of_isCurve B X f kbar)).hom))) (π : N ⟶ M)
          (IM : CochainComplex.InjectiveResolution
        ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj M))))
        (IN : CochainComplex.InjectiveResolution
        ((CochainComplex.singleFunctor (EtaleModules.{u, 0} Λ (Over.mk j.toBase).left) 0).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).obj N'))))
              (φ : IN.cocomplex ⟶ IM.cocomplex)
              (_ : (IN.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
              ((representationSheaf B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ).map (π' ≫ π))) ≫ IM.ι)),
        HomologicalComplex.homologyMap
            (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
          (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
              (cyclotomicIntResolution B X f kbar y n j K₀)) φ)) (m : ℤ) = 0 := by
  subst hn
  obtain ⟨N', π', hπ', hz⟩ := exists_epi_map_cyclotomicDual_eq_zero B X f kbar y Λ hΛ hEff m hm N
  refine ⟨N', π', hπ', fun M π IM IN φ hφ => ?_⟩
  -- the map `Hᵐ(X_k̄, ℱ_{Hom(π' ≫ π, μ_n)})` is zero
  have hZ :
      ((geometricRepresentationCohomology.{u, 0} B X
      (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ f kbar).functor m).map
      ((cyclotomicDual B X f kbar y (Nat.card Λ) Λ).map (π' ≫ π).op) = 0 := by
    rw [op_comp, Functor.map_comp, Functor.map_comp, hz, comp_zero]
  -- hence so is `Hᵐ(X_k̄, -)` of the restriction of `ℋom_ℤ(ℱ_{π' ≫ π}, ℱ_μ)`
  have hmid :
      ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus
      (m : ℤ)).map ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj (Over.mk f) kbar)).map
      ((representationSheaf B X
      (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λᵐᵒᵖ).map
      ((cyclotomicDual B X f kbar y (Nat.card Λ) Λ).map (π' ≫ π).op))) = 0 :=
    map_eq_zero_of_iso_of_map_eq_zero (Stacks.DerivedIndexing.rightDerivedIso _ m) hZ
  have hK :
      ((etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus
      (m : ℤ)).map ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj (Over.mk f) kbar)).map
      ((etaleHomOpRepresentationFunctor B X
      (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Nat.card Λ)
      (cyclotomicContinuousModule B X f kbar y (Nat.card Λ))).map (π' ≫ π).op)) = 0 := by
    exact map_eq_zero_of_iso_of_map_eq_zero
      (Functor.isoWhiskerRight (representationSheafHomOpNatIso B X
        (y.map (fieldBaseChangeObjProj B X f kbar
        (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Nat.card Λ)
        (cyclotomicContinuousModule B X f kbar y (Nat.card Λ))).symm
        ((etaleModuleInverseImage.{u, 0} Λᵐᵒᵖ (fieldBaseChangeProj (Over.mk f) kbar)) ⋙
        (etaleModuleGlobalSections.{u, 0} Λᵐᵒᵖ
          (fieldBaseChange (Over.mk f) kbar)).rightDerivedPlus (m : ℤ))) hmid
  -- hence so is `Hᵐ(X_k̄, -)` with its Galois action
  have hU : (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λᵐᵒᵖ (kbar ≃ₐ[k] kbar)).map
      (((galoisGlobalSections Λᵐᵒᵖ (Over.mk f) kbar).rightDerivedPlus (m : ℤ)).map
      ((etaleHomOpRepresentationFunctor B X
      (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Nat.card Λ)
      (cyclotomicContinuousModule B X f kbar y (Nat.card Λ))).map (π' ≫ π).op)) = 0 :=
    map_eq_zero_of_iso_of_map_eq_zero (galoisRightDerivedPlusForgetIso Λᵐᵒᵖ f kbar (m : ℤ)).symm hK
  have hT : ((galoisGlobalSections Λᵐᵒᵖ (Over.mk f) kbar).rightDerivedPlus (m : ℤ)).map
      ((etaleHomOpRepresentationFunctor B X
      (y.map (fieldBaseChangeObjProj B X f kbar
      (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Nat.card Λ)
      (cyclotomicContinuousModule B X f kbar y (Nat.card Λ))).map (π' ≫ π).op) = 0 :=
    (Stacks.Injectives.continuousModuleUnderlying.{0, u, u + 1} Λᵐᵒᵖ
        (kbar ≃ₐ[k] kbar)).map_injective (hU.trans (Functor.map_zero _ _ _).symm)
  -- hence so is `Hᵐ` of `E_M ⟶ E_{N'}` in the derived category
  have hQ : (DerivedCategory.homologyFunctor (GaloisModules Λᵐᵒᵖ k kbar) (m : ℤ)).map
      (DerivedCategory.Q.map
          (((galoisGlobalSections Λᵐᵒᵖ (Over.mk j.toBase) kbar).mapHomologicalComplex _).map
      (homOpComplexPrecomp (M := etaleHomOpTarget (Over.mk j.toBase)
        (cyclotomicIntResolution B X f kbar y (Nat.card Λ) j K₀)) φ))) = 0 := by
    have h := (Iso.eq_comp_inv _).2 (hnat M N' (π' ≫ π) IM IN φ hφ)
    have hTg : (DerivedCategory.homologyFunctor (GaloisModules Λᵐᵒᵖ k kbar) (m : ℤ)).map
        ((DerivedCategory.Plus.singleFunctor _ 0 ⋙ galoisDerivedGlobalSections Λᵐᵒᵖ
            (Over.mk f) kbar ⋙
          DerivedCategory.Plus.ι).map
              ((etaleHomOpRepresentationFunctor B X
              (y.map (fieldBaseChangeObjProj B X f kbar
              (contains_fieldBaseChange_of_isCurve B X f kbar)).hom) Λ (Nat.card Λ)
              (cyclotomicContinuousModule B X f kbar y (Nat.card Λ))).map (π' ≫ π).op)) = 0 := hT
    rw [h, Functor.map_comp, Functor.map_comp, hTg, comp_zero, zero_comp]
  -- and on the cohomology of the complexes
  exact map_eq_zero_of_iso_of_map_eq_zero
    (DerivedCategory.homologyFunctorFactors (GaloisModules Λᵐᵒᵖ k kbar) (m : ℤ)) hQ

end AlgebraicGeometry

end
