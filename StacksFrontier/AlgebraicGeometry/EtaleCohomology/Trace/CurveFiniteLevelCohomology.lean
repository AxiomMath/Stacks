module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportPerfectCurveFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicUpperVanishing

/-!
# Finiteness of the finite levels of `Hⁱ_c(X_k̄, F)` on a curve

For an ℓ-adic sheaf `F` on a separated scheme of finite type and dimension at most one over a
finite field `k`, each `Hⁱ_c(X_k̄, Fₙ)` is finite: it is the compactly supported cohomology over
the algebraically closed `k̄` of the constructible torsion sheaf `Fₙ|_{X_k̄}` (Tag 0GKR), read as a
`ℤ_ℓ`-module.

## Main results

* `finite_geometricCompactSupportPadicCohomology_padicLevel_of_topologicalKrullDim_le_one`
  (in `Stacks.EtaleCohomology.LAdicSheaf`): on a curve, `Hⁱ_c(X_k̄, Fₙ)` is finite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale
open Stacks.Frobenius

universe u

attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
  ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

variable {k : Type u} [Field k] [Fintype k] (f : X.1 ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar]

namespace LAdicSheaf

omit [Fintype k] in
/-- **`Hⁱ_c(X_k̄, Fₙ)` is finite on a curve**: for an ℓ-adic sheaf `F` on `X` with
`dim X ≤ 1`, the `ℤ_ℓ`-module `Hⁱ_c(X_k̄, Fₙ)` is finite. -/
theorem finite_geometricCompactSupportPadicCohomology_padicLevel_of_topologicalKrullDim_le_one
    (hdim : topologicalKrullDim X.1 ≤ 1) (F : LAdicSheaf.{u, u + 1} B X ℓ) (i : ℤ) (n : ℕ) :
    Finite ((geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n)) := by
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated f
  have : CompactSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f (specAlgebraMap k kbar))
  have : QuasiSeparatedSpace ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd f (specAlgebraMap k kbar))
  let Λ := ZMod (ℓ ^ (n + 1))
  let G := LAdicSheaf.etaleLevel B X ℓ F n
  let gX := pullback.fst f (specAlgebraMap k kbar)
  let e₀ : (geometricCompactSupportPadicCohomology B X ℓ f j kbar i).obj
      (LAdicSheaf.padicLevel B X ℓ F n) ≅
      (ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj
        (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
          (LAdicSheaf.levelComplex B X ℓ F n) i) :=
    (compactSupportFrobeniusFunctor.{u, 0} ℤ_[ℓ] f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).mapIso
        (LAdicSheaf.padicCoefficientComplexLevelIso B X ℓ F n) ≪≫
      (compactSupportFrobeniusCohomologyGroupRestrictScalarsIso (PadicInt.toZModPow (n + 1)) f j
        kbar (LAdicSheaf.levelComplex B X ℓ F n) i).symm
  obtain ⟨B', hY, hc⟩ := exists_isConstructibleEtaleModule_inverseImage Λ B X gX G
    (LAdicSheaf.isConstructibleEtaleModule_etaleLevel B X ℓ F n)
  have hdimk : topologicalKrullDim ↥(pullback f (specAlgebraMap k kbar) : Scheme.{u}) ≤ 1 := by
    exact_mod_cast topologicalKrullDim_pullback_le_of_fiber f 1
      (fun y ↦ (topologicalKrullDim_fiber_of_spec_field k f y).le.trans (by exact_mod_cast hdim))
      (specAlgebraMap k kbar)
  have h0 := TorsionModules.module_finite_compactlySupportedCohomologyGroup B' (B'.obj _ hY)
    (pullback.snd f (specAlgebraMap k kbar)) hdimk (compactificationFieldBaseChange f j kbar) Λ
    ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) hc (isTorsionEtaleModule_zmod _ _) i
  let e₁ : (etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ (compactificationFieldBaseChangeImmersion f j kbar)).obj
        ((etaleModuleInverseImage.{u, 0} Λ gX).obj G) :=
    ((compactificationFieldBaseChangeExtensionByZeroIso.{u, 0} Λ f j kbar).app G).symm
  let e₂ : compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i ≅
      (compactlySupportedCohomologyGroup.{u, 0} kbar (pullback.snd f (specAlgebraMap k kbar))
        (compactificationFieldBaseChange f j kbar) Λ i).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ gX).obj G)) :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
      (compactSupportFrobeniusCohomologySingleIso f j kbar G ≪≫
        DerivedCategory.Plus.ι.mapIso ((etaleModuleDerivedGlobalSections.{u, 0} Λ
          (Spec (.of kbar))).mapIso ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd j.toBase (specAlgebraMap k kbar))).mapIso
              ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e₁))) ≪≫
        derivedDirectImageSectionsExtensionByZeroIso f j kbar Λ _)
  have : Module.Finite Λ (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i) := Module.Finite.equiv e₂.symm.toLinearEquiv
  have : NeZero (ℓ ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have hfin : Finite (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
      (LAdicSheaf.levelComplex B X ℓ F n) i) := Module.finite_of_finite Λ
  have : Finite ((ModuleCat.restrictScalars.{u + 1} (PadicInt.toZModPow (n + 1))).obj
      (compactSupportFrobeniusCohomologyGroup.{u, 0} Λ f j kbar
        (LAdicSheaf.levelComplex B X ℓ F n) i)) := hfin
  exact Finite.of_equiv _ e₀.symm.toLinearEquiv.toEquiv

end LAdicSheaf

end Stacks.EtaleCohomology

end
