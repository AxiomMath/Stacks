module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.NoncommConstructibleFlatRepresentative
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfFiniteTor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology

/-!
# Constructible flat representatives over a finite ring, on Mathlib's small étale site

This file transports
`Stacks.EtaleCohomology.exists_constructibleFlat_representative_of_projective_cokernel` from the
small étale site of Stacks 021B to Mathlib's small étale site, along the equivalence
`AlgebraicGeometry.SmallEtale.sheafEquiv` of the two categories of sheaves of `Λ`-modules.

## Main results

* `Stacks.EtaleCohomology.isRepresentedByConstructibleFlatEtaleComplex_of_projective_cokernel`: for
  a finite, possibly noncommutative, ring `Λ`, an object of `D(X_étale, Λ)` on a quasi-compact and
  quasi-separated scheme with constructible underlying abelian cohomology sheaves vanishing outside
  `[a, b]`, whose bounded above representatives with finite projective stalks have projective
  stalks of the cokernel of the differential into degree `a`, is represented by a bounded complex
  of constructible flat sheaves of `Λ`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ]

/-- Restriction of scalars to `ℤ` commutes with the transport to the small étale site of Stacks
021B. -/
def etaleModulesToSmallEtaleIntRestrictIso :
    etaleModulesToSmallEtale B X Λ ⋙ intRestrictScalarsSheaf B X Λ ≅
      etaleModuleRestrictScalars (Int.castRingHom Λ) X.obj ⋙ etaleModulesToSmallEtale B X ℤ :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [Finite Λ]

/-- **Constructible flat representatives over a finite ring, on Mathlib's small étale site.** On a
quasi-compact and quasi-separated scheme `X`, let `K` be an object of `D(X_étale, Λ)`, `Λ` a finite
ring, whose cohomology sheaves vanish outside `[a, b]` and have constructible underlying abelian
sheaves. Suppose that for every bounded above complex representing `K`, concentrated in degrees
`≤ b` and with finite projective stalks, the cokernel of the differential into degree `a` has
projective stalks. Then `K` is represented by a bounded complex of constructible flat sheaves of
`Λ`-modules. -/
theorem isRepresentedByConstructibleFlatEtaleComplex_of_projective_cokernel
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X.obj)) (a b : ℤ)
    (hcons : ∀ i : ℤ, IsBigSiteConstructibleEtaleModule B X ℤ
      ((etaleModuleRestrictScalars (Int.castRingHom Λ) X.obj).obj
        ((DerivedCategory.homologyFunctor _ i).obj K)))
    (hvan : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hproj : ∀ (Y : CochainComplex (EtaleModules.{u, 0} Λ X.obj) ℤ),
      Nonempty (DerivedCategory.Q.obj Y ≅ K) → Y.IsStrictlyLE b →
      (∀ (n : ℤ) (s : GeometricPoint X.obj),
        Module.Finite Λ ((etaleModuleStalk.{u, 0} B X Λ s).obj (Y.X n)) ∧
          Module.Projective Λ ((etaleModuleStalk.{u, 0} B X Λ s).obj (Y.X n))) →
      ∀ s : GeometricPoint X.obj, Module.Projective Λ
        ((etaleModuleStalk.{u, 0} B X Λ s).obj (cokernel (Y.d (a - 1) a)))) :
    IsRepresentedByConstructibleFlatEtaleComplex B X Λ K := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  have := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, 0} B X ℤ
  let ε := SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{u + 1} Λ)
  let ρ := etaleModulesToSmallEtale B X Λ
  let σ := ε.functor
  have : σ.Additive := Functor.additive_of_preserves_binary_products _
  let K₂ := ρ.mapDerivedCategory.obj K
  let eH : ∀ i : ℤ, (DerivedCategory.homologyFunctor _ i).obj K₂ ≅
      ρ.obj ((DerivedCategory.homologyFunctor _ i).obj K) := fun i =>
    (ρ.mapDerivedCategoryHomologyIso i).app K
  rw [isRepresentedByConstructibleFlatEtaleComplex_iff]
  obtain ⟨F, hFa, hFb, hF, ⟨eF⟩⟩ :=
    exists_constructibleFlat_representative_of_projective_cokernel B X Λ K₂ a b
      (fun i => by
        refine (IsIntConstructible B X Λ).prop_of_iso (eH i).symm ?_
        exact (isConstructibleModuleSheafProperty.{u, u + 1, 0} B X ℤ).prop_of_iso
          ((etaleModulesToSmallEtaleIntRestrictIso B X Λ).app _).symm (hcons i))
      (fun i hi => (ρ.map_isZero (hvan i hi)).of_iso (eH i))
      (fun Y₂ ⟨eY₂⟩ hY₂ hfin s => by
        let Y := (σ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y₂
        let eρY : (ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj Y ≅ Y₂ :=
          HomologicalComplex.Hom.isoOfComponents (fun i => ε.unitIso.symm.app (Y₂.X i))
            (fun i j _ => (ε.unitIso.inv.naturality (Y₂.d i j)).symm)
        have hst : ∀ (n : ℤ) (t : GeometricPoint X.obj),
            (etaleModuleStalk.{u, 0} B X Λ t).obj (Y.X n) ≅
              (etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).obj (Y₂.X n) := fun n t =>
          (etaleModuleStalkIsoTransport.{u, 0} B X Λ t).app (Y.X n) ≪≫
            (etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ t).mapIso
              ((HomologicalComplex.eval _ _ n).mapIso eρY)
        let C₀ := DerivedCategory.Q.objPreimage K
        let e₀ : DerivedCategory.Q.obj C₀ ≅ K := DerivedCategory.Q.objObjPreimageIso K
        let eC₀ : (σ.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((ρ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C₀) ≅ C₀ :=
          HomologicalComplex.Hom.isoOfComponents (fun i => ε.counitIso.app (C₀.X i))
            (fun i j _ => (ε.counitIso.hom.naturality (C₀.d i j)).symm)
        have eY : DerivedCategory.Q.obj Y ≅ K :=
          (σ.mapDerivedCategoryFactors.app Y₂).symm ≪≫ σ.mapDerivedCategory.mapIso eY₂ ≪≫
            σ.mapDerivedCategory.mapIso (ρ.mapDerivedCategory.mapIso e₀.symm ≪≫
              ρ.mapDerivedCategoryFactors.app C₀) ≪≫
            σ.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso eC₀ ≪≫ e₀
        have hYb : CochainComplex.IsStrictlyLE Y b := (CochainComplex.isStrictlyLE_iff _ _).2
          fun i hi => σ.map_isZero (Y₂.isZero_of_isStrictlyLE b i hi)
        have hP := hproj Y ⟨eY⟩ hYb (fun n t => by
          obtain ⟨h1, h2⟩ := hfin n t
          exact ⟨Module.Finite.equiv (hst n t).toLinearEquiv.symm,
            Module.Projective.of_equiv' (hst n t).toLinearEquiv.symm⟩) s
        let eCok : ρ.obj (cokernel (Y.d (a - 1) a)) ≅ cokernel (Y₂.d (a - 1) a) :=
          PreservesCokernel.iso ρ (Y.d (a - 1) a) ≪≫
            cokernel.mapIso _ _ ((HomologicalComplex.eval _ _ (a - 1)).mapIso eρY)
              ((HomologicalComplex.eval _ _ a).mapIso eρY) (eρY.hom.comm (a - 1) a).symm
        let eS : (etaleModuleStalk.{u, 0} B X Λ s).obj (cokernel (Y.d (a - 1) a)) ≅
            (etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj (cokernel (Y₂.d (a - 1) a)) :=
          (etaleModuleStalkIsoTransport.{u, 0} B X Λ s).app _ ≪≫
            (etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).mapIso eCok
        exact Module.Projective.of_equiv' eS.toLinearEquiv)
  exact ⟨F, a, b, hFa, hFb, hF, ⟨eF⟩⟩

end Stacks.EtaleCohomology

end
