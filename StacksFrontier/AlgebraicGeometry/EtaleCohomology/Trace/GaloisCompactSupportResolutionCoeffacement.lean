module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GaloisCompactSupportResolutionModel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCompactSupportDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveSecondCohomologyRightExact

/-!
# The compactly supported side of the Poincaré pairing: vanishing and coeffacements

For the chain model `Γ(X̄_k̄, I|_{X̄_k̄})` of `RΓ_c(X_k̄, F)`, `I` an injective resolution of
`j_! F` on the compactification (`Stacks.EtaleCohomology.galoisCompactSupportResolutionIso`), this
file records the two inputs of the descending induction of Tag 03VM on the compactly supported
side:

* `Hᵐ_c(X_k̄, F) = 0` for `m > 2`
  (`Stacks.EtaleCohomology.isZero_galoisCompactSupportCohomologyGroup_of_two_lt`, through the
  smooth projective model of `X_k̄` and Tag 03SC), hence the cohomology of the chain model
  vanishes above degree `2`;
* a morphism `π : P ⟶ M` of finite modules with `H_c^{2-i}(π) = 0` for the left derived functors
  `Tᵢ = H_c^{2-i}(X_k̄, ℱ_-)` of Tag 03VM
  (`AlgebraicGeometry.compactSupportRepresentationHomology`) induces zero on `H^{2-i}` of the chain
  models, for every morphism of resolutions over `j_! ℱ_π`
  (`AlgebraicGeometry.homologyMap_compactSupportResolution_eq_zero`).

## References

* [Stacks Project, Tag 03SC](https://stacks.math.columbia.edu/tag/03SC)
* [Stacks Project, Tag 03VM](https://stacks.math.columbia.edu/tag/03VM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Frobenius
open Stacks.GroupCohomology

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_resolutionCoeffacement
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

section Vanishing

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] (Λ : Type) [Ring Λ] [Finite Λ]

include q in
/-- **`Hⁿ(C, N) = 0` for `n > 2`** for a sheaf `N` of modules over a finite ring on a curve over
an algebraically closed field (Tag 03SC). -/
theorem isZero_rightDerivedPlus_of_two_lt_of_isCurve (N : EtaleModules.{u, 0} Λ C) (n : ℕ)
    (hn : 2 < n) :
    IsZero (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus (n : ℤ)).obj N) := by
  have h : Subsingleton (Sheaf.H.{u + 1} ((etaleModuleUnderlyingAbelian C ℤ).obj
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) C).obj N)) n) :=
    ({ k := K
       X := C
       structureMorphism := q
       dimension_le_one := (IsCurve.topologicalKrullDim_eq_one (f := q)).le
       F := (etaleModuleUnderlyingAbelian C ℤ).obj
        ((etaleModuleRestrictScalars (Int.castRingHom Λ) C).obj N)
       isTorsion := torsionSheafProperty_etaleModuleUnderlyingAbelian Λ N } :
      TorsionSheafSituation.{u, 0}).isVanishingAboveDegreeTwo n hn
  exact isZero_rightDerivedPlus_of_subsingleton_sheafH C N n h

end Vanishing

section CompactSupport

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar] (Λ : Type) [Ring Λ] [Finite Λ]

/-- **`Hᵐ_c(X_k̄, F) = 0` for `m > 2`**, for a smooth geometrically connected curve `X` over `k`
and a sheaf of modules over a finite ring. -/
theorem isZero_galoisCompactSupportCohomologyGroup_of_two_lt (F : EtaleModules.{u, 0} Λ X)
    (m : ℤ) (hm : 2 < m) :
    IsZero (galoisCompactSupportCohomologyGroup.{u, 0} Λ f j kbar
      ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).obj F) m) := by
  have := (geometricSmoothModel f j kbar).isCurve
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg (by omega)⟩
  exact IsZero.of_iso (isZero_rightDerivedPlus_of_two_lt_of_isCurve
    (geometricSmoothModel f j kbar).q Λ _ n (by omega))
    (galoisCompactSupportSmoothModelIso f j kbar Λ F n)

variable [Algebra.IsSeparable k kbar]

/-- **The chain model of `RΓ_c(X_k̄, F)` has no cohomology above degree `2`.** -/
theorem isZero_homology_compactSupportResolution_of_two_lt (F : EtaleModules.{u, 0} Λ X)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj F))) (m : ℤ)
    (hm : 2 < m) :
    IsZero ((((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
          (((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _).obj
              I.cocomplex)).homology m) :=
  IsZero.of_iso (isZero_galoisCompactSupportCohomologyGroup_of_two_lt f j kbar Λ F m hm)
    (galoisCompactSupportResolutionIso (f := f) kbar F I m)

end CompactSupport

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- Enough injectives for sheaves of `Λ`-modules on the small étale site, pinned at the object
universe. -/
local instance (priority := 3000) etaleModules_enoughInjectives_compactSupportCoeffacement
    (Λ : Type) [Ring Λ] (Y : Scheme.{u}) : EnoughInjectives (EtaleModules.{u, 0} Λ Y) :=
  etaleModules_enoughInjectives.{u, 0} Λ Y

/-- Sheafification of presheaves of `Λ`-modules on the small étale site, pinned at `u + 1`. -/
local instance (priority := 3000) etaleModules_hasSheafify_compactSupportCoeffacement (Λ : Type)
    [Ring Λ] (Y : Scheme.{u}) : HasSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  etaleModules_hasSheafify.{u, 0} Λ Y

variable (B : BigEtaleSite.{u}) (X : B.Scheme) [ConnectedSpace X.1]
  (x : GeometricPoint X.1) (Λ : Type) [Ring Λ] [Finite Λ]
  {k : Type u} [Field k] (f : X.1 ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
  [GeometricallyConnected f] (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar]
  [Algebra k kbar] [IsAlgClosed kbar]

/-- If `a ≫ e = e' ≫ b` with `e` and `e'` isomorphisms, then `a = 0` if and only if `b = 0`. -/
private theorem eq_zero_iff_of_comp_isIso_eq_comp {C : Type*} [Category C] [Preadditive C]
    {A B A' B' : C} {a : A ⟶ B} {b : A' ⟶ B'} {e : B ⟶ B'} {e' : A ⟶ A'} [IsIso e] [IsIso e']
    (h : a ≫ e = e' ≫ b) : a = 0 ↔ b = 0 := by
  constructor
  · rintro rfl
    simpa using h.symm
  · rintro rfl
    simpa using h

/-- **A coeffacement for `Tᵢ = H_c^{2-i}(X_k̄, ℱ_-)` is zero on `H_c^{2-i}`** in the model
`RΓ(X̄_k̄, (j_! -)|_{X̄_k̄})`: if `Tᵢ(π) = 0` then `π` induces zero on
`galoisCompactSupportCohomologyGroup` in degree `2 - i`. -/
theorem galoisCompactSupportCohomologyMap_representationSheaf_eq_zero (i : ℕ) (hi : i ≤ 2)
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (π : M ⟶ N)
    (h : ((compactSupportRepresentationHomology B X x Λ f j kbar).functor i).map π = 0) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) ((2 - i : ℕ) : ℤ)).map
      (Stacks.EtaleCohomology.galoisCompactSupportCohomologyMap Λ f j kbar
        ((Stacks.DerivedIndexing.singlePlusFunctor _ 0).map
          ((representationSheaf B X x Λ).map π))) = 0 := by
  have h₁ : ((Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
      (geometricSmoothModel f j kbar).Vb).rightDerived (2 - i)).map
        ((compactSupportRepresentationSheaf B X x Λ f j kbar).map π) = 0 := by
    interval_cases i <;> exact h
  have h₂ := (Stacks.DerivedIndexing.rightDerivedIso
      (Stacks.EtaleCohomology.etaleModuleGlobalSections.{u, 0} Λ
        (geometricSmoothModel f j kbar).Vb) (2 - i)).hom.naturality
        ((compactSupportRepresentationSheaf B X x Λ f j kbar).map π)
  exact (eq_zero_iff_of_comp_isIso_eq_comp
    (Stacks.EtaleCohomology.galoisCompactSupportSmoothModelIso_hom_naturality f j kbar Λ
      ((representationSheaf B X x Λ).map π) ((2 - i : ℕ) : ℤ))).2
    (((eq_zero_iff_of_comp_isIso_eq_comp h₂).1 h₁))

/-- **A coeffacement for `Tᵢ` is zero on the chain models**: for `π : M ⟶ N` with `Tᵢ(π) = 0`,
`i ≤ 2`, and any morphism `φ : I ⟶ I'` of injective resolutions of `j_! ℱ_M` and `j_! ℱ_N` over
`j_! ℱ_π`, the map `Γ(X̄_k̄, φ|)` is zero on `H^{2-i}`. -/
theorem homologyMap_compactSupportResolution_eq_zero [Algebra.IsSeparable k kbar] (i : ℕ)
    (hi : i ≤ 2)
    {M N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup X.1 x)}
    (π : M ⟶ N)
    (h : ((compactSupportRepresentationHomology B X x Λ f j kbar).functor i).map π = 0)
    (I : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
        ((representationSheaf B X x Λ).obj M))))
    (I' : CochainComplex.InjectiveResolution ((CochainComplex.singleFunctor _ 0).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj
        ((representationSheaf B X x Λ).obj N))))
    (φ : I.cocomplex ⟶ I'.cocomplex)
    (hφ : I.ι ≫ φ = (CochainComplex.singleFunctor _ 0).map
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).map
        ((representationSheaf B X x Λ).map π)) ≫ I'.ι) :
    HomologicalComplex.homologyMap
      ((etaleModuleGlobalSections.{u, 0} Λ
        (fieldBaseChange (Over.mk j.toBase) kbar)).mapHomologicalComplex _ |>.map
          ((etaleModuleInverseImage.{u, 0} Λ
            (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapHomologicalComplex _ |>.map φ))
      ((2 - i : ℕ) : ℤ) = 0 := by
  exact (eq_zero_iff_of_comp_isIso_eq_comp
    (galoisCompactSupportResolutionIso_hom_naturality (f := f) (kbar := kbar)
      ((representationSheaf B X x Λ).map π) I I' φ hφ ((2 - i : ℕ) : ℤ))).2
    (galoisCompactSupportCohomologyMap_representationSheaf_eq_zero B X x Λ f j kbar i hi π h)

end AlgebraicGeometry

end
