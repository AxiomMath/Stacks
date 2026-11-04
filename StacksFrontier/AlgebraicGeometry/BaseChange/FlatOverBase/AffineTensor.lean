module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.AffineComparison
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.ComparisonDatum
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorDatum
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom

/-!
# The base-change composition at a tensor product with a complex flat over the base, on a
square of spectra

Let `R → A`, `R → R'`, `A → A'`, `R' → A'` be a pushout square of rings. For a K-flat complex
`P` of `𝒪_{Spec A}`-modules with quasi-coherent cohomology and a complex `G` of quasi-coherent
`𝒪_{Spec A}`-modules whose global sections form a complex of `A`-modules which is K-flat over
`R`, the composition `Lg^*Rf_*Tot(P ⊗ G) ⟶ Rf'_*(g')^*Tot(P ⊗ G)` over the square of spectra is
an isomorphism.

## Main results

* `AlgebraicGeometry.isIso_derivedBaseChangeComp_specMap_tensor`: the composition at
  `Tot(P ⊗ G)` over the square of spectra is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

variable {R A R' A' : CommRingCat.{u}} {a : R ⟶ A} {b : R ⟶ R'} {c : A ⟶ A'} {d : R' ⟶ A'}
  (h : IsPushout a b c d)

/-- The composition at `T̃`, with the comparison of the derived with the degreewise pullback, for
a complex `T` of `A`-modules which is K-flat over `R`. -/
theorem isIso_derivedBaseChangeComp_specMap_tilde (T : CochainComplex (ModuleCat.{u} A) ℤ)
    (hT : CochainComplex.KFlat.{u, u} (((ModuleCat.restrictScalars a.hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj T)) :
    IsIso (derivedBaseChangeComp (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c)
      (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w
      (DerivedCategory.Q.obj (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj T))
      _ ((derivedPullbackNatTrans (Spec.map c).toLRSHom.toShHom).app
        (((tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj T))) :=
  (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff _ _ _ _ _ _).2
    (Stacks.Cohomology.DerivedBaseChange.isIso_derivedBaseChangeMap_comp_comparison_specMap h T hT)

/-- The composition at `Tot(M̃ ⊗ Ñ)` for a K-flat complex `M` of `A`-modules and a complex `N` of
`A`-modules which is K-flat over `R`. -/
theorem isIso_derivedBaseChangeComp_specMap_tilde_tensor (M N : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : M.KFlat)
    (hN : ((CochainComplex.restrictScalars a.hom).obj N).KFlat) :
    IsIso (derivedBaseChangeComp (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c)
      (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w
      (DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex (specCommRingSheaf A)).obj
          (tildeComplexMod M)).obj (tildeComplexMod N)))
      _ ((derivedPullbackNatTrans (Spec.map c).toLRSHom.toShHom).app
        (((Stacks.SheafOfModules.Tensor.tensorComplex (specCommRingSheaf A)).obj
          (tildeComplexMod M)).obj (tildeComplexMod N)))) :=
  (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso _ _ _ _ _
    (affineTensorComplexIso A M N).1).1
    (isIso_derivedBaseChangeComp_specMap_tilde h (M ⊗ N)
      (CochainComplex.kFlat_restrictScalars_tensorObj a.hom hM hN))

/-- The complex of global sections of a complex of modules on `Spec A`. -/
abbrev sectionsComplex (G : CochainComplex (Spec A).Modules ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ :=
  ((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (ComplexShape.up ℤ)).obj G

/-- The composition at `Tot(M̃ ⊗ G)` for a K-flat complex `M` of `A`-modules and a complex `G` of
quasi-coherent modules whose complex of global sections is K-flat over `R`. -/
theorem isIso_derivedBaseChangeComp_specMap_tilde_tensor_of_isQuasicoherent
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (hM : M.KFlat)
    (G : CochainComplex (Spec A).Modules ℤ) (hG : ∀ n, (G.X n).IsQuasicoherent)
    (hN : ((CochainComplex.restrictScalars a.hom).obj (sectionsComplex G)).KFlat) :
    IsIso (derivedBaseChangeComp (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c)
      (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w
      (DerivedCategory.Q.obj
        (((Stacks.SheafOfModules.Tensor.tensorComplex (specCommRingSheaf A)).obj
          (tildeComplexMod M)).obj (show CochainComplex (SpecModules A) ℤ from G)))
      _ ((derivedPullbackNatTrans (Spec.map c).toLRSHom.toShHom).app
        (((Stacks.SheafOfModules.Tensor.tensorComplex (specCommRingSheaf A)).obj
          (tildeComplexMod M)).obj (show CochainComplex (SpecModules A) ℤ from G)))) :=
  (Stacks.Cohomology.BaseChangeCover.isIso_bc_derivedPullbackNatTrans_iff_of_iso _ _ _ _ _
    (((Stacks.SheafOfModules.Tensor.tensorComplex (specCommRingSheaf A)).obj
      (tildeComplexMod M)).mapIso (tildeΓComplexIso A G fun n ↦ by
        have := hG n; infer_instance))).1
    (isIso_derivedBaseChangeComp_specMap_tilde_tensor h M (sectionsComplex G) hM hN)

/-- **The composition at `Tot(P ⊗ G)` over a square of spectra** for a K-flat complex `P` with
quasi-coherent cohomology and a complex `G` of quasi-coherent modules whose complex of global
sections is K-flat over `R`. -/
theorem isIso_derivedBaseChangeComp_specMap_tensor
    (P G : CochainComplex
      (RingedSpace.KFlatDerivedPullback.Modules (Spec A).toRingedSpace) ℤ)
    (hP : RingedSpace.KFlatDerivedPullback.KFlat (Spec A).toRingedSpace P)
    (hPq : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec A).Modules n).obj
      (DerivedCategory.Q.obj (show CochainComplex (Spec A).Modules ℤ from P))).IsQuasicoherent)
    (hG : ∀ n, ((show CochainComplex (Spec A).Modules ℤ from G).X n).IsQuasicoherent)
    (hN : ((CochainComplex.restrictScalars a.hom).obj
      (sectionsComplex (show CochainComplex (Spec A).Modules ℤ from G))).KFlat) :
    IsIso (derivedBaseChangeComp (Spec.map a) (Spec.map b) (Spec.map d) (Spec.map c)
      (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w
      (DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor P G
        (Stacks.SheafOfModules.Tensor.sheafTensor (Spec A).toRingedSpace.sheaf)
        (ComplexShape.up ℤ)))
      _ ((derivedPullbackNatTrans (Spec.map c).toLRSHom.toShHom).app
        (HomologicalComplex.mapBifunctor P G
          (Stacks.SheafOfModules.Tensor.sheafTensor (Spec A).toRingedSpace.sheaf)
          (ComplexShape.up ℤ)))) := by
  obtain ⟨M₀, ⟨e₀⟩⟩ := StandardModel.exists_iso_mapDerivedCategory A _ hPq
  obtain ⟨M, hM, ⟨e₁⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u} M₀
  have e : DerivedCategory.Q.obj ((tildeCx A).obj M) ≅
      DerivedCategory.Q.obj (show CochainComplex (Spec A).Modules ℤ from P) :=
    ((tilde.functor A).mapDerivedCategoryFactors.app M).symm ≪≫
      (tilde.functor A).mapDerivedCategory.mapIso e₁ ≪≫ e₀
  have hMt : RingedSpace.KFlatDerivedPullback.KFlat (Spec A).toRingedSpace
      (show CochainComplex (RingedSpace.KFlatDerivedPullback.Modules (Spec A).toRingedSpace) ℤ
        from tildeComplexMod M) :=
    Stacks.TildeStalk.kFlatComplex_tilde A M hM
  refine (isIso_derivedBaseChangeComp_tensor_iff_of_kFlat _ _ _ _
    (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w P G hP).1 ?_
  refine (isIso_derivedBaseChangeComp_tensor_iff_of_iso _ _ _ _
    (comp_toShHom_of_comm (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w)
      e _ _ _).1 ?_
  exact (isIso_derivedBaseChangeComp_tensor_iff_of_kFlat _ _ _ _
    (Stacks.Cohomology.DerivedBaseChange.isPullback_specMap h).w _ G hMt).2
    (isIso_derivedBaseChangeComp_specMap_tilde_tensor_of_isQuasicoherent h M hM _ hG hN)

end AlgebraicGeometry
