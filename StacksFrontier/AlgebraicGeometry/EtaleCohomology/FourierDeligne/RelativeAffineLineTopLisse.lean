module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierInversionDegree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.ConstructibleLocallyFreeTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LocallyFreeProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibilityUnconditional
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleGlobalSectionsUnit

/-!
# `R^i pr_!(pr⁻¹ M)` on a relative affine line is lisse for `M` lisse

Let `k` be a finite field, `Λ` a finite commutative ring, `W` a `k`-scheme and `pr : P ⟶ W` the
affine line over `W` (a base change of `𝔸¹_k ⟶ Spec k`). For a sheaf `M` of `Λ`-modules on `W`
which is étale-locally free of finite rank, every `Hⁱ(R pr_!(pr⁻¹ M))` is locally constant of
finite type:

* the projection formula (`Stacks.EtaleCohomology.derivedLowerShriekProjectionIso`) gives
  `R pr_!(Λ ⊗ pr⁻¹ M) ≅ R pr_! Λ ⊗ M`, and `- ⊗ M` is exact, so
  `Hⁱ(R pr_!(pr⁻¹ M)) ≅ Hⁱ(R pr_! Λ) ⊗ M`;
* proper base change (Tag 0F7L) gives `Hⁱ(R pr_! Λ) ≅ π_W⁻¹ Hⁱ(Rf_! Λ)`, `f : 𝔸¹_k ⟶ Spec k`;
* `Hⁱ(Rf_! Λ)` is a constructible sheaf on `Spec k` (Tag 0GL0), hence locally constant of finite
  type, `Spec k` having a single point;
* inverse images and tensor products with locally free sheaves keep local constancy.

Applied to the antidiagonal `Q_Δ ⟶ 𝔸¹_u` this shows that `F' = H²(Φ(Φ(F[0])))` is locally
constant of finite type for `F` étale-locally free of finite rank
(`Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp`), the
lisseness of `F'` used in step (a) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

All in the namespace `Stacks.EtaleCohomology`:

* `isLocallyFreeEtaleModule_tensorUnit`.
* `isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_specField`.
* `isFiniteTypeLocallyConstant_homology_derivedLowerShriek_tensorUnit_affineLine`.
* `isFiniteTypeLocallyConstant_homology_derivedLowerShriek_inverseImage_affineLine`.
* `isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp`.

## Implementation notes

`Rf_!` and the Fourier transform live in the standard model `HasDerivedCategory.standard`, and so
do the statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [CommRing Λ]

/-- **The tensor unit `Λ_X` is étale-locally free of rank one**: it is the constant sheaf on
`ULift Λ`. -/
theorem isLocallyFreeEtaleModule_tensorUnit (X : Scheme.{u}) :
    IsLocallyFreeEtaleModule Λ (𝟙_ (EtaleModules.{u, 0} Λ X)) := by
  intro U
  refine ⟨PUnit.{u + 2}, fun _ => U, fun _ => 𝟙 U, ?_, fun _ => ?_⟩
  · have h : Sieve.ofArrows (fun _ : PUnit.{u + 2} => U) (fun _ => 𝟙 U) = ⊤ :=
      Sieve.id_mem_iff_eq_top.mp (Sieve.ofArrows_mk _ _ PUnit.unit)
    rw [h]
    exact X.smallEtaleTopology.top_mem U
  · refine ⟨ModuleCat.of Λ (ULift.{u + 1} Λ),
      ⟨Module.Free.of_equiv ULift.moduleEquiv.symm, Module.Finite.equiv ULift.moduleEquiv.symm⟩,
      ⟨(Stacks.ConstantSheaf.overPullbackConstantSheafIso X.smallEtaleTopology
          (ModuleCat.{u + 1} Λ) U).app _ ≪≫
        (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} Λ) U).mapIso
          (Stacks.Cohomology.GlobalSections.tensorUnitIsoConstantModuleSheaf Λ
            X.smallEtaleTopology).symm⟩⟩

variable [Finite Λ]

/-- **A constructible sheaf on the spectrum of a field is locally constant of finite type**: it is
so on an open neighbourhood of the generic point, which is the whole spectrum. -/
theorem isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_specField (K : Type u)
    [Field K] {F : EtaleModules.{u, 0} Λ (Spec (.of K))} (hF : IsConstructibleEtaleModule Λ F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (Spec (.of K)).smallEtaleTopology F := by
  have : IsNoetherianRing Λ := inferInstance
  let B := BigEtaleSite.containing (Spec (.of K))
  have hKB : B.Contains (Spec (.of K)) := BigEtaleSite.contains_containing _
  have hc : IsBigSiteConstructibleEtaleModule B (B.obj _ hKB) Λ F :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hKB _).1 hF
  have : IsReduced (B.obj _ hKB).obj := inferInstanceAs (IsReduced (Spec (.of K)))
  obtain ⟨η, hη⟩ : (genericPoints (Spec (.of K))).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun he => Set.empty_ne_univ <| by
      simpa only [he, closure_empty] using genericPoints.closure (α := Spec (.of K))
  obtain ⟨O, o, ho, ⟨z, -⟩, hFO⟩ :=
    exists_isOpenImmersion_isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule B
      (B.obj _ hKB) _ hc hη
  let o' : O.obj ⟶ Spec (.of K) := B.inclusion.map o
  have : IsOpenImmersion o' := ho
  have : Surjective o' := ⟨fun x => ⟨z, Subsingleton.elim _ _⟩⟩
  have : IsIso o' := (isIso_iff_isOpenImmersion_and_surjective o').2 ⟨inferInstance, inferInstance⟩
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ ?_
    (isLocallyConstantWith_inverseImage Λ (ModuleCat.isFG Λ) (inv o') hFO)
  exact (etaleModuleInverseImageCompObjIso Λ (inv o') o' F).symm ≪≫
    eqToIso (congrArg (fun m => (etaleModuleInverseImage.{u, 0} Λ m).obj F)
      (IsIso.inv_hom_id o')) ≪≫
    (etaleModuleInverseImageIdIso.{u, 0} Λ (Spec (.of K))).app F

variable (k : Type u) [Field k] [Fintype k]

local notation "𝔸f" => affineLineStructureMap k

omit [Fintype k] in
/-- **`Hⁱ(Rf_! Λ)` is locally constant of finite type on `Spec k`**, `f : 𝔸¹_k ⟶ Spec k`: it is
constructible (Tag 0GL0). -/
theorem isFiniteTypeLocallyConstant_homology_derivedLowerShriek_tensorUnit_affineLine
    (j : CompactificationOf (Over.mk 𝔸f)) (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (Spec (.of k)).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ i).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) := by
  have : IsNoetherianRing Λ := inferInstance
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFinitePresentation 𝔸f :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 ‹_›
  let B' := BigEtaleSite.ofSet ({Spec (.of (Polynomial k)), Spec (.of k)} : Set Scheme.{u})
  have hX : B'.Contains (Spec (.of (Polynomial k))) := BigEtaleSite.contains_ofSet _ (by simp)
  have hY : B'.Contains (Spec (.of k)) := BigEtaleSite.contains_ofSet _ (by simp)
  have : CompactSpace (B'.obj _ hY).obj := inferInstanceAs (CompactSpace (Spec (.of k)))
  have : QuasiSeparatedSpace (B'.obj _ hY).obj :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (.of k)))
  have hG : IsBigSiteConstructibleEtaleModule B' (B'.obj _ hX) Λ
      (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))) :=
    (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B' hX _).1
      (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ
        (isLocallyFreeEtaleModule_tensorUnit Λ _))
  have h := (isConstructibleEtaleModule_homology_derivedLowerShriek_of_isConstructible B'
    (X := B'.obj _ hX) (Y := B'.obj _ hY) 𝔸f j Λ).1
      ((DerivedCategory.Plus.singleFunctor _ 0).obj _)
    (fun q => ⟨isConstructibleEtaleModule_homology_singleFunctor hG q,
      isTorsionEtaleModule_of_finite Λ _ _⟩) i
  exact isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_specField Λ k
    ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B' hY _).2 h)

omit [Fintype k] in
attribute [local instance] etaleModuleInverseImageSheafPullbackMonoidal
  hasSheafify_etaleModules_fourierKernel in
/-- **`Hⁱ(R pr_!(pr⁻¹ M))` is locally constant of finite type** on the affine line
`pr : P ⟶ W` over a `k`-scheme `W`, for `M` étale-locally free of finite rank on `W`:
`Hⁱ(R pr_!(pr⁻¹ M)) ≅ π_W⁻¹ Hⁱ(Rf_! Λ) ⊗ M` (projection formula and proper base change). -/
theorem isFiniteTypeLocallyConstant_homology_derivedLowerShriek_inverseImage_affineLine
    (j : CompactificationOf (Over.mk 𝔸f)) {W P : Scheme.{u}}
    (πW : W ⟶ Spec (.of k)) {T : P ⟶ Spec (.of (Polynomial k))} {pr : P ⟶ W}
    (sq : IsPullback T pr 𝔸f πW) (M : EtaleModules.{u, 0} Λ W)
    (hM : IsLocallyFreeEtaleModule Λ M) (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ W.smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} Λ pr).obj M)))) := by
  have : IsNoetherianRing Λ := inferInstance
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : LocallyOfFiniteType pr :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq inferInstance
  have : IsSeparated pr := MorphismProperty.of_isPullback (P := @IsSeparated) sq inferInstance
  have : QuasiCompact pr := MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  let H := DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} Λ W) i
  let S := DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ P) 0
  let I := fun {X Y : Scheme.{u}} (a : X ⟶ Y) => etaleModuleInverseImage.{u, 0} Λ a
  -- `Hⁱ(R pr_! Λ_P)` is pulled back from `Spec k`
  let K₀ := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ
    (Spec (.of (Polynomial k)))) 0).obj (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))
  have := isIso_derivedLowerShriekBaseChange_app Λ sq j K₀ (isTorsionPlus_of_finite Λ _ K₀)
  let eU : (etaleModuleDerivedInverseImagePlus.{u, 0} Λ T).obj K₀ ≅ S.obj (𝟙_ _) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle (I T) 0).app _ ≪≫
      S.mapIso (Functor.Monoidal.εIso (etaleModuleInverseImage.{u, 0} Λ T)).symm
  let e₀ : H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ≅
      (I πW).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj K₀)) :=
    H.mapIso ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).mapIso eU.symm ≪≫
      (asIso ((derivedLowerShriekBaseChange.{u, 0} Λ sq j).app K₀)).symm) ≪≫
      (etaleModuleInverseImageHomologyIso Λ πW _ i).symm
  have h₀ : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ W.smallEtaleTopology
      (H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _)))) :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ e₀.symm
      (isLocallyConstantWith_inverseImage Λ (ModuleCat.isFG Λ) πW
        (isFiniteTypeLocallyConstant_homology_derivedLowerShriek_tensorUnit_affineLine Λ k j i))
  -- the projection formula
  have hf := additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_inverseImage
    pr M hM
  have hg :=
    additive_preservesFiniteLimits_preservesFiniteColimits_tensorRight_of_isLocallyConstantWith
      M hM
  have := hf.1; have := hf.2.1; have := hf.2.2
  have := hg.1; have := hg.2.1; have := hg.2.2
  let eP := (derivedLowerShriekProjectionIso pr (j.baseChange sq) M hM).app (S.obj (𝟙_ _))
  let eL : S.obj ((I pr).obj M) ≅
      (MonoidalCategory.tensorRight ((I pr).obj M)).mapDerivedCategoryPlus.obj (S.obj (𝟙_ _)) :=
    S.mapIso (λ_ _).symm ≪≫
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (MonoidalCategory.tensorRight ((I pr).obj M)) 0).app _).symm
  let eH : H.obj ((MonoidalCategory.tensorRight M).mapDerivedCategoryPlus.obj
        ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _)))) ≅
      H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ⊗ M :=
    H.mapIso ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso
        (MonoidalCategory.tensorRight M)).app _) ≪≫
      (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
        (MonoidalCategory.tensorRight M) i).app _
  let e : H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj ((I pr).obj M))) ≅
      H.obj ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).obj (S.obj (𝟙_ _))) ⊗ M :=
    H.mapIso ((derivedLowerShriek.{u, 0} pr (j.baseChange sq) Λ).mapIso eL ≪≫ eP) ≪≫ eH
  refine Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ e.symm fun U' => ?_
  obtain ⟨I', V, f, hcov, ht⟩ := isLocallyConstantWith_tensor Λ (fun E => ModuleCat.isFG Λ E)
    (fun E => Module.Free Λ E ∧ Module.Finite Λ E) h₀ hM U'
  refine ⟨I', V, f, hcov, fun i' => ?_⟩
  obtain ⟨E, ⟨E₁, E₂, hE₁, hE₂, rfl⟩, e'⟩ := ht i'
  refine ⟨E₁ ⊗ E₂, (ModuleCat.isFG_iff _).2 ?_, e'⟩
  have := (ModuleCat.isFG_iff E₁).1 hE₁
  have := hE₂.2
  exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))

variable (ψ : AddChar k Λ) (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- **`F' = H²(Φ(Φ(F[0])))` is locally constant of finite type** for `F` étale-locally free of
finite rank on `𝔸¹_k`: `Φ(Φ(F[0])) ≅ R pr_!(pr⁻¹(ν⁻¹ F))` on the antidiagonal, an affine line over
`𝔸¹_u` (Fourier inversion), and `ν⁻¹ F` is locally free. -/
theorem isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    (i : ℤ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := by
  have : IsNoetherianRing Λ := inferInstance
  have hFf := finite_globalSections_inverseImage_of_isConstructible Λ
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF)
  obtain ⟨e₁⟩ := nonempty_fourierTransform_comp_iso k Λ ψ B p₀ hψ hq j jQ F hFf
  obtain ⟨e₂⟩ := nonempty_fourierAntidiagonalTransform_iso k Λ j jQ F
  have h := isFiniteTypeLocallyConstant_homology_derivedLowerShriek_inverseImage_affineLine Λ k j
    𝔸f (isPullback_fourierAntidiagonal k) _
    (isLocallyFreeEtaleModule_inverseImage Λ (affineLineNeg k) hF) i
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso (e₁ ≪≫ e₂).symm) h

end Stacks.EtaleCohomology

end
