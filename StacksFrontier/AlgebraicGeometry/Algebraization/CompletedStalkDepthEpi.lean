module

public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModulesStalkSequenceColimit
public import Mathlib.RingTheory.AdicCompletion.Exactness
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic

/-!
# Completed stalks along an epimorphism with power-torsion kernel

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent sheaf of ideals and `φ : (ℱ_n) ⟶ (𝒢_n)` an
epimorphism of `Coh(X, ℐ)` whose kernel (in `Coh(X, ℐ)`) is annihilated by a fixed power `ℐ^c`.
At a point `y` the induced map of completed stalks `ℱ_y^∧ ⟶ 𝒢_y^∧` is surjective with kernel
killed by `ℐ_y^c`; so it becomes an isomorphism after localizing at any prime `𝔭` of the
completed local ring not containing `ℐ𝒪_{X,y}^∧`, and the depths
`depth((ℱ_y^∧)_𝔭)` and `depth((𝒢_y^∧)_𝔭)` agree.

The argument is levelwise. Cokernels in `Coh(X, ℐ)` are computed levelwise, so the epimorphism
`φ` is the levelwise cokernel of the inclusion of its kernel `(𝒦_n)`; the stalk functor is a left
adjoint, so `𝒦_{n,y} ⟶ ℱ_{n,y} ⟶ 𝒢_{n,y} ⟶ 0` is exact, and the image of `𝒦_{n,y}` is killed by
`ℐ_y^c` because `𝒦_n` is. The formal stalk `ℱ_y^∧ = lim ℱ_{n,y}` has `ℱ_{n,y}` as its reduction
modulo `ℐ_y^{n+1}` (`Stacks.Coherent.moduleLimit_projection_ker`), so an element of the kernel
of `ℱ_y^∧ ⟶ 𝒢_y^∧` is, after multiplication by `ℐ_y^c`, zero modulo every power of `ℐ_y`, hence
zero; and surjectivity reduces to level zero
(`AdicCompletion.map_surjective_of_mkQ_comp_surjective`).

## Main results

* `Stacks.Algebraization.exact_stalk_kernel_ι_app` — the levelwise stalks of `ker φ ⟶ ℱ ⟶ 𝒢`
  are exact with `ℱ_{n,y} ⟶ 𝒢_{n,y}` surjective.
* `Stacks.Algebraization.surjective_completedStalkMap` and
  `Stacks.Algebraization.smul_eq_zero_of_completedStalkMap_eq_zero` — the map of completed stalks
  is surjective, with kernel killed by `ℐ_y^c`.
* `Stacks.Algebraization.completedStalkDepth_eq_of_epi` — the completed-stalk depths at primes
  off `V(ℐ𝒪_{X,y}^∧)` agree.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.ModuleSkyscraper

universe u

namespace Stacks.Algebraization

/-! ### Localization of a surjection with power-torsion kernel -/

/-- A surjective linear map whose kernel is killed by an element of a submonoid `S` becomes
bijective after localizing at `S`. -/
theorem bijective_localizedModuleMap_of_surjective {R : Type*} [CommRing R] (S : Submonoid R)
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (h : M →ₗ[R] N)
    (hs : Function.Surjective h) (t : R) (ht : t ∈ S) (hker : ∀ x, h x = 0 → t • x = 0) :
    Function.Bijective (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) h) := by
  refine ⟨?_, IsLocalizedModule.map_surjective S _ _ h hs⟩
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro z hz
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S (LocalizedModule.mkLinearMap S M) z
  rw [LinearMap.mem_ker, Function.uncurry_apply_pair, IsLocalizedModule.map_mk',
    IsLocalizedModule.mk'_eq_zero'] at hz
  obtain ⟨c, hc⟩ := hz
  have hcx : h ((c : R) • x) = 0 := by rwa [map_smul]
  rw [Submodule.mem_bot, Function.uncurry_apply_pair, IsLocalizedModule.mk'_eq_zero']
  refine ⟨⟨t, ht⟩ * c, ?_⟩
  show (t * (c : R)) • x = 0
  rw [mul_smul]
  exact hker _ hcx

variable {X : Scheme.{u}}

/-! ### Exactness on stalks -/

/-- The stalk of a module annihilated by `ℐ^c` is annihilated by `ℐ_y^c`. -/
theorem smul_stalk_eq_zero_of_idealPowerMultiple_eq_bot (I : X.IdealSheafData) {c : ℕ}
    (M : X.Modules) [M.IsQuasicoherent] (hM : idealPowerMultiple I c M = ⊥) (y : X)
    {a : X.presheaf.stalk y} (ha : a ∈ IdealSheafData.stalk I y ^ c)
    (m : (modulesStalkFunctor X y).obj M) : a • m = 0 := by
  have hmem : a • m ∈ IdealSheafData.stalk I y ^ c •
      (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj M)) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rw [← stalk_idealPowerMultiple I c M y] at hmem
  have hle := range_stalk_submodule_ι_le_of_affine (idealPowerMultiple I c M) y ⊥
    (fun U hx s hs => by
      rw [hM, bot_submodule_obj_eq_bot] at hs
      obtain rfl : s = 0 := hs
      rw [map_zero]
      exact Submodule.zero_mem _)
  exact (Submodule.mem_bot _).mp (hle hmem)

variable [IsNoetherian X] {I : X.IdealSheafData}
  {F G : Stacks.Coherent.CoherentAdicSystems I} (φ : F ⟶ G) [Epi φ]

/-- **The stalks of `ker φ ⟶ ℱ ⟶ 𝒢` are exact at every level, and `ℱ_{n,y} ⟶ 𝒢_{n,y}` is
surjective.** The epimorphism `φ` is the cokernel of its kernel in `Coh(X, ℐ)`, cokernels there
are levelwise, and evaluation and the stalk functor preserve cokernels. -/
theorem exact_stalk_kernel_ι_app (y : X) (n : ℕ) :
    Function.Exact ((modulesStalkFunctor X y).map ((kernel.ι φ).hom.app (op n))).hom
        ((modulesStalkFunctor X y).map (φ.hom.app (op n))).hom ∧
      Function.Surjective ((modulesStalkFunctor X y).map (φ.hom.app (op n))).hom := by
  let P : Stacks.Coherent.CoherentAdicSystems I ⥤ ModuleCat.{u} (X.presheaf.stalk y) :=
    ObjectProperty.ι _ ⋙ (evaluation ℕᵒᵖ X.Modules).obj (op n) ⋙ modulesStalkFunctor X y
  have : PreservesColimitsOfShape WalkingParallelPair (modulesStalkFunctor X y) :=
    have := ModuleSkyscraper.modulesStalkFunctor_preservesColimits X y
    inferInstance
  have hc : IsColimit (CokernelCofork.ofπ φ (kernel.condition φ)) :=
    Abelian.epiIsCokernelOfKernel
      (Fork.ofι (kernel.ι φ) ((kernel.condition φ).trans comp_zero.symm)) (kernelIsKernel φ)
  have hc' := CokernelCofork.mapIsColimit _ hc P
  let S : ShortComplex (ModuleCat.{u} (X.presheaf.stalk y)) :=
    ShortComplex.mk (P.map (kernel.ι φ)) (P.map φ)
      (by rw [← P.map_comp, kernel.condition, P.map_zero])
  exact ⟨LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker S).mp
      (S.exact_of_g_is_cokernel hc')).symm,
    (ModuleCat.epi_iff_surjective S.g).mp (epi_of_isColimit_cofork hc')⟩

/-! ### The map of completed stalks -/

/-- An element of the formal stalk whose image in the level-`n` stalk vanishes lies in
`ℐ_y^{n+1}` times the formal stalk. -/
private theorem mem_smul_top_of_limit_π_eq_zero (H : Stacks.Coherent.CoherentAdicSystems I)
    (y : X) (n : ℕ) {m : formalStalk H y}
    (hm : (limit.π (H.obj ⋙ modulesStalkFunctor X y) (op n)).hom
      (formalStalkEquivModuleStalkLimit H y m) = 0) :
    m ∈ IdealSheafData.stalk I y ^ (n + 1) •
      (⊤ : Submodule (X.presheaf.stalk y) (formalStalk H y)) := by
  have hker := Stacks.Coherent.moduleLimit_projection_ker (I := IdealSheafData.stalk I y)
    (H.obj ⋙ modulesStalkFunctor X y) (fun k => surjective_stalk_coherentAdicTransition H y k)
    (fun k => ker_stalk_coherentAdicTransition H y k) (Ideal.fg_of_isNoetherianRing _) n
  rw [← map_smul_top_linearEquiv (formalStalkEquivModuleStalkLimit H y).symm, ← hker]
  exact ⟨_, hm, LinearEquiv.symm_apply_apply _ _⟩

variable (y : X)

/-- The map `ℱ_y^∧ ⟶ 𝒢_y^∧` of formal stalks induced by `φ`, read through the limits of the stalk
towers. -/
def formalStalkMap : formalStalk F y →ₗ[X.presheaf.stalk y] formalStalk G y :=
  (formalStalkEquivModuleStalkLimit G y).symm.toLinearMap ∘ₗ
    (limMap (Functor.whiskerRight φ.hom (modulesStalkFunctor X y))).hom ∘ₗ
      (formalStalkEquivModuleStalkLimit F y).toLinearMap

omit [AlgebraicGeometry.IsNoetherian X] [Epi φ] in
/-- The map of formal stalks lies over the levelwise stalk maps. -/
theorem limit_π_formalStalkMap (n : ℕ) (m : formalStalk F y) :
    (limit.π (G.obj ⋙ modulesStalkFunctor X y) (op n)).hom
        (formalStalkEquivModuleStalkLimit G y (formalStalkMap φ y m)) =
      ((modulesStalkFunctor X y).map (φ.hom.app (op n))).hom
        ((limit.π (F.obj ⋙ modulesStalkFunctor X y) (op n)).hom
          (formalStalkEquivModuleStalkLimit F y m)) := by
  simp only [formalStalkMap, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  exact congrArg (fun g => g.hom (formalStalkEquivModuleStalkLimit F y m))
    (limMap_π (Functor.whiskerRight φ.hom (modulesStalkFunctor X y)) (op n))

/-- The map of completed stalks `ℱ_y^∧ ⟶ 𝒢_y^∧` over the completed local ring. -/
def completedStalkMap : completedStalk I F y →ₗ[completedLocalRing I y] completedStalk I G y :=
  AdicCompletion.map (IdealSheafData.stalk I y) (formalStalkMap φ y)

/-- **The map of completed stalks is surjective.** Surjectivity is checked modulo `ℐ_y`, where
it is the surjectivity of `ℱ_{0,y} ⟶ 𝒢_{0,y}`. -/
theorem surjective_completedStalkMap : Function.Surjective (completedStalkMap φ y) := by
  refine AdicCompletion.map_surjective_of_mkQ_comp_surjective (fun z => ?_)
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ z
  set J := IdealSheafData.stalk I y
  set eF := formalStalkEquivModuleStalkLimit F y
  set eG := formalStalkEquivModuleStalkLimit G y
  obtain ⟨w, hw⟩ := (exact_stalk_kernel_ι_app φ y 0).2
    ((limit.π (G.obj ⋙ modulesStalkFunctor X y) (op 0)).hom (eG z))
  obtain ⟨x', rfl⟩ := Stacks.Coherent.moduleLimit_projection_surjective
    (F.obj ⋙ modulesStalkFunctor X y) (fun k => surjective_stalk_coherentAdicTransition F y k) 0 w
  refine ⟨eF.symm x', ?_⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
  rw [Submodule.Quotient.eq]
  have := mem_smul_top_of_limit_π_eq_zero G y 0 (m := formalStalkMap φ y (eF.symm x') - z) (by
    rw [map_sub, map_sub, limit_π_formalStalkMap, LinearEquiv.apply_symm_apply, hw, sub_self])
  rwa [zero_add, pow_one] at this

variable {φ} in
/-- **The kernel of the map of completed stalks is killed by `ℐ_y^c`** when the kernel of `φ` in
`Coh(X, ℐ)` is killed by `ℐ^c`. -/
theorem smul_eq_zero_of_completedStalkMap_eq_zero {c : ℕ}
    (hc : ∀ n : ℕ, idealPowerMultiple I c ((kernel φ).obj.obj (op n)) = ⊥)
    {a : X.presheaf.stalk y} (ha : a ∈ IdealSheafData.stalk I y ^ c)
    (x : completedStalk I F y) (hx : completedStalkMap φ y x = 0) : a • x = 0 := by
  set J := IdealSheafData.stalk I y
  set eF := formalStalkEquivModuleStalkLimit F y
  set eG := formalStalkEquivModuleStalkLimit G y
  have := isAdicComplete_formalStalk F y
  have := isAdicComplete_formalStalk G y
  obtain ⟨m, rfl⟩ := (AdicCompletion.of_bijective J (formalStalk F y)).2 x
  have hfm : formalStalkMap φ y m = 0 := by
    apply (AdicCompletion.of_bijective J (formalStalk G y)).1
    rw [map_zero, ← hx]
    exact (AdicCompletion.map_of J _ m).symm
  suffices h : a • m = 0 by rw [← map_smul, h, map_zero]
  refine IsHausdorff.haus (inferInstance : IsHausdorff J (formalStalk F y)) _ fun k => ?_
  rw [SModEq.zero]
  rcases k with _ | n
  · simp
  have hπ : ((modulesStalkFunctor X y).map (φ.hom.app (op n))).hom
      ((limit.π (F.obj ⋙ modulesStalkFunctor X y) (op n)).hom (eF m)) = 0 := by
    rw [← limit_π_formalStalkMap, hfm, map_zero, map_zero]
  obtain ⟨z, hz⟩ := ((exact_stalk_kernel_ι_app φ y n).1 _).mp hπ
  have : _root_.SheafOfModules.IsCoherent.{u} ((kernel φ).obj.obj (op n)) := (kernel φ).property.1 n
  have := (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((kernel φ).obj.obj (op n))).1
  exact mem_smul_top_of_limit_π_eq_zero F y n (by
    rw [map_smul, map_smul, ← hz, ← map_smul,
      smul_stalk_eq_zero_of_idealPowerMultiple_eq_bot I _ (hc n) y ha z, map_zero])

/-- **An epimorphism of `Coh(X, ℐ)` with power-torsion kernel does not change completed-stalk
depths off `V(ℐ)`.** Let `φ : ℱ ⟶ 𝒢` be an epimorphism of `Coh(X, ℐ)` on a Noetherian scheme
whose kernel is annihilated by `ℐ^c`. Then for every point `y` and every prime `𝔭` of
`𝒪_{X,y}^∧` not containing `ℐ𝒪_{X,y}^∧`, `depth((𝒢_y^∧)_𝔭) = depth((ℱ_y^∧)_𝔭)`.

The map `ℱ_y^∧ ⟶ 𝒢_y^∧` is surjective with kernel killed by `ℐ_y^c`, and some element of
`ℐ_y^c` maps outside `𝔭`, so the map becomes an isomorphism after localizing at `𝔭`. -/
theorem completedStalkDepth_eq_of_epi
    (hker : ∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((kernel φ).obj.obj (op n)) = ⊥)
    (p : PrimeSpectrum (completedLocalRing I y))
    (hp : ¬ completedLocalIdeal I y ≤ p.asIdeal) :
    completedStalkDepth I G y p = completedStalkDepth I F y p := by
  obtain ⟨c, hc⟩ := hker
  set J := IdealSheafData.stalk I y
  obtain ⟨b, hbJ, hbp⟩ : ∃ b ∈ J, algebraMap (X.presheaf.stalk y) (completedLocalRing I y) b ∉
      p.asIdeal := by
    by_contra! h
    exact hp (Ideal.map_le_iff_le_comap.mpr fun b hb => h b hb)
  set t := algebraMap (X.presheaf.stalk y) (completedLocalRing I y) b ^ c
  have ht : t ∈ p.asIdeal.primeCompl := fun h => hbp (p.isPrime.mem_of_pow_mem c h)
  have hkerΨ : ∀ x, completedStalkMap φ y x = 0 → t • x = 0 := fun x hx => by
    show algebraMap (X.presheaf.stalk y) (completedLocalRing I y) b ^ c • x = 0
    rw [← map_pow, algebraMap_smul]
    exact smul_eq_zero_of_completedStalkMap_eq_zero y hc (Ideal.pow_mem_pow hbJ c) x hx
  have hbij := bijective_localizedModuleMap_of_surjective p.asIdeal.primeCompl
    (completedStalkMap φ y) (surjective_completedStalkMap φ y) t ht hkerΨ
  let e := LinearEquiv.ofBijective
    ((IsLocalizedModule.map p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk I F y))
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (completedStalk I G y))
      (completedStalkMap φ y)).extendScalarsOfIsLocalization p.asIdeal.primeCompl
        (Localization.AtPrime p.asIdeal)) hbij
  exact (Module.depth_eq_depth_of_linearEquiv _ e).symm

end Stacks.Algebraization

end
