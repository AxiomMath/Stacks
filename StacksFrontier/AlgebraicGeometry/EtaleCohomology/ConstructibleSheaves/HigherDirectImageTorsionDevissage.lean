module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ConstructibleHomology
public import StacksFrontier.AlgebraicGeometry.CoherentTwoOutOfThree.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules

/-!
# Higher direct images of constant sheaves: reduction to prime torsion

Let `f : X ⟶ S` be a morphism of schemes of a big étale site and `Λ` a Noetherian ring. This
file proves the first step of the proof of Stacks 0GKW: if `R^q f_* \underline{M}` is a
constructible sheaf of `Λ`-modules for every finite `Λ`-module `M` annihilated by a prime number,
then the same holds for every finite `Λ`-module annihilated by a positive integer. Writing
`n = ℓ n'` with `ℓ` prime, the short exact sequence `0 ⟶ M[ℓ] ⟶ M ⟶ M/M[ℓ] ⟶ 0` of finite
`Λ`-modules, with `M/M[ℓ]` annihilated by `n'`, gives a short exact sequence of constant sheaves;
its long exact sequence of higher direct images and the weak Serre property of constructible
sheaves (Stacks 03RZ (3)) give the induction step.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_rightDerived_constantSheaf_of_nsmul_eq_zero`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

variable (B : BigEtaleSite.{u}) {X S : B.Scheme} (f : X.obj ⟶ S.obj) (Λ : Type r) [CommRing Λ]
  [IsNoetherianRing Λ]

omit [IsNoetherianRing Λ] in
/-- The constant sheaf functor on Mathlib's small étale site with module coefficients is exact. -/
theorem shortExact_map_constantSheaf_etaleModules (T : ShortComplex (ModuleCat.{max (u + 1) r} Λ))
    (hT : T.ShortExact) :
    (T.map (constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ))).ShortExact := by
  have : (constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).IsLeftAdjoint :=
    (constantSheafAdj X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)
      terminalIsTerminal).isLeftAdjoint
  exact hT.map_of_exact _

/-- **Reduction of Stacks 0GKW to prime torsion.** If `R^q f_* \underline{M}` is constructible
for all `q` and every finite `Λ`-module `M` annihilated by some prime number, then it is
constructible for all `q` and every finite `Λ`-module annihilated by a positive integer. -/
theorem isConstructibleEtaleModule_rightDerived_constantSheaf_of_nsmul_eq_zero
    (hprime : ∀ (ℓ : ℕ), ℓ.Prime → ∀ (M : ModuleCat.{max (u + 1) r} Λ), Module.Finite Λ M →
      (∀ m : M, ℓ • m = 0) → ∀ q : ℕ, IsBigSiteConstructibleEtaleModule B S Λ
        (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj
          ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)))
    (n : ℕ) (hn : 0 < n) (M : ModuleCat.{max (u + 1) r} Λ) (hM : Module.Finite Λ M)
    (hnM : ∀ m : M, n • m = 0) (q : ℕ) :
    IsBigSiteConstructibleEtaleModule B S Λ
      (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj
        ((constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj M)) := by
  have := isWeakSerreClass_isBigSiteConstructibleEtaleModule B S Λ
  let E := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (etaleModuleDirectImage.{u, r} Λ f)
  induction n using Nat.strong_induction_on generalizing M q with
  | _ n ih =>
  obtain rfl | h1 := eq_or_ne n 1
  · have : ((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).Additive := E.additive q
    have hz : IsZero M := by
      rw [ModuleCat.isZero_iff_subsingleton]
      exact ⟨fun a b => by simpa using (hnM a).trans (hnM b).symm⟩
    exact (IsBigSiteConstructibleEtaleModule B S Λ).prop_of_isZero
      ((((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).map_isZero
        ((constantSheaf _ _).map_isZero hz)))
  obtain ⟨ℓ, hℓ, n', rfl⟩ : ∃ ℓ, ℓ.Prime ∧ ∃ n', n = ℓ * n' :=
    ⟨n.minFac, Nat.minFac_prime h1, n / n.minFac, (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm⟩
  let φ : M ⟶ M := ModuleCat.ofHom (ℓ • LinearMap.id)
  have : IsNoetherian Λ M := isNoetherian_of_isNoetherianRing_of_finite Λ M
  let T : ShortComplex (ModuleCat.{max (u + 1) r} Λ) := ShortComplex.mk (kernel.ι φ)
    (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _
    (cokernelIsCokernel _)) inferInstance inferInstance
  have h₁ : ∀ p : ℕ, IsBigSiteConstructibleEtaleModule B S Λ ((E.functor p).obj
      (constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) |>.obj T.X₁)) := by
    intro p
    refine hprime ℓ hℓ T.X₁ (Module.Finite.of_injective (kernel.ι φ).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)) (fun m => ?_) p
    apply (ModuleCat.mono_iff_injective (kernel.ι φ)).1 inferInstance
    rw [map_nsmul, map_zero]
    exact (congrArg (fun g => g.hom m) (kernel.condition φ) : _)
  have h₃ : ∀ p : ℕ, IsBigSiteConstructibleEtaleModule B S Λ ((E.functor p).obj
      (constantSheaf X.obj.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ) |>.obj T.X₃)) := by
    intro p
    have hπ := (ModuleCat.epi_iff_surjective (cokernel.π (kernel.ι φ))).1 inferInstance
    refine ih n' (by nlinarith [hℓ.two_le]) (Nat.pos_of_mul_pos_left hn) T.X₃
      (Module.Finite.of_surjective _ hπ) (fun m => ?_) p
    obtain ⟨m, rfl⟩ := hπ m
    have hker : n' • m ∈ LinearMap.ker φ.hom := by
      show ℓ • (n' • m) = 0
      rw [smul_smul]
      exact hnM m
    obtain ⟨k, hk⟩ := (ShortComplex.moduleCat_exact_iff_ker_sub_range
      (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ))).1
      (ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ)) hker
    rw [← map_nsmul, ← hk]
    exact (congrArg (fun g => g.hom k) (cokernel.condition (kernel.ι φ)) : _)
  exact E.prop_obj_X₂ (IsBigSiteConstructibleEtaleModule B S Λ)
    (shortExact_map_constantSheaf_etaleModules B Λ T hT) h₁ h₃ q

end Stacks.EtaleCohomology

end
