module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesStabilization
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.AffineSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.QuotientColumn
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.TwoIdealAdicQuotient
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# Improving coherent formal modules: the object of `Coh(X, ℐ)`

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf, `T ⊆ V(ℐ)` stable under
specialization and `(ℱ_n)` an object of `Coh(X, ℐ)` satisfying the depth condition of Stacks,
Tag 0EJE on its completed stalks at the points of `T`. Let `ℱ_n → ℱ'_n` be the depth-one quotients
along `T` (`Stacks.Algebraization.toImprovedSystem`).

This file builds the object `(𝒢_n)` of `Coh(X, ℐ)` of Stacks, Tag 0EJE (2) and the morphisms
around it. It is a diagonal of the completions of the depth-one quotients:
`𝒢_n = ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}` for the stabilization levels `μ(n)` of
`Stacks.Algebraization.exists_stalk_range_supportedImageMap_eq`. Past `μ(n)` the quotient
`ℱ'_m / ℐ^{n+1} ℱ'_m` no longer depends on `m` (`Stacks.Algebraization.isIso_improvedQuotientMap`),
which is checked on stalks: there it is `ℱ_{n,y}` modulo the image of the sections supported in
`T`, and that image has stabilized. This makes `(𝒢_n)` a coherent adic system
(`Stacks.Algebraization.isCoherentAdicSystem_diagonalSystem`). The projections
`ℱ'_{μ(m)} → 𝒢_m` and the maps `𝒢_n → ℱ'_n` invert each other up to transition maps, and the
morphism `(ℱ_n) → (𝒢_n)` is an epimorphism of `Coh(X, ℐ)` whose kernel is annihilated by the
power of `ℐ` annihilating the stalks of the images of the supported sections.

## Main definitions

* `Stacks.Algebraization.improvedCompletionSystem` — the completions of the depth-one quotients.
* `Stacks.Algebraization.diagonalSystem` — the system `n ↦ ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}`.

## Main results

* `Stacks.Algebraization.isIso_improvedQuotientMap` — the stabilization of `ℱ'_m / ℐ^{n+1} ℱ'_m`.
* `Stacks.Algebraization.isCoherentAdicSystem_diagonalSystem` — the diagonal system is an object
  of `Coh(X, ℐ)`.
* `Stacks.Algebraization.exists_coherentAdicSystem_improvement` — the object `(𝒢_n)` with the
  morphisms `(ℱ_n) → (𝒢_n) → (ℱ'_n)` and their properties.

## References

* [Stacks Project, Tag 0EJE](https://stacks.math.columbia.edu/tag/0EJE)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing
open Stacks.ModuleSkyscraper

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}} [IsNoetherian X] {I : X.IdealSheafData}
  (F : Stacks.Coherent.CoherentAdicSystems I) (T : Set X) (hT : StableUnderSpecialization T)

/-! ### Stalks -/

section Stalks

variable (y : X)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- An epimorphism of `𝒪_X`-modules is surjective on stalks. -/
theorem surjective_stalk_of_epi {M N : X.Modules} (g : M ⟶ N) [Epi g] :
    Function.Surjective ((modulesStalkFunctor X y).map g).hom :=
  (ModuleCat.epi_iff_surjective _).mp (Functor.map_epi _ _)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The stalk of the kernel of a morphism is the kernel of the stalk map. -/
theorem range_stalk_kernel_ι {M N : X.Modules} (g : M ⟶ N) :
    LinearMap.range ((modulesStalkFunctor X y).map (kernel.ι g)).hom =
      LinearMap.ker ((modulesStalkFunctor X y).map g).hom :=
  Stacks.Coherent.range_map_kernel_ι (modulesStalkFunctor X y) g

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The kernel of the stalk of the projection onto `M / ℐ^r M`. -/
theorem ker_stalk_cokernel_π_idealPowerMultiple (r : ℕ) (M : X.Modules) [M.IsQuasicoherent] :
    LinearMap.ker ((modulesStalkFunctor X y).map
        (cokernel.π (C := X.Modules) (idealPowerMultiple I r M).ι)).hom =
      IdealSheafData.stalk I y ^ r •
        (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj M)) := by
  rw [← range_stalk_submodule_ι_eq_ker_stalk_cokernel_π, stalk_idealPowerMultiple]

/-- The stalk of `ℱ_n` is annihilated by the `(n+1)`-st power of the stalk of `ℐ`. -/
theorem pow_smul_top_stalk_eq_bot (n : ℕ) :
    IdealSheafData.stalk I y ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk y) ((modulesStalkFunctor X y).obj (F.obj.obj (op n)))) =
      ⊥ := by
  have hr : LinearMap.range (completedStalkProj F y n) = ⊤ :=
    LinearMap.range_eq_top.mpr (completedStalkProj_surjective F y n)
  rw [← hr, LinearMap.range_eq_map, ← Submodule.map_smul'', ← completedStalkProj_ker,
    eq_bot_iff]
  rintro _ ⟨w, hw, rfl⟩
  exact (Submodule.mem_bot _).mpr hw

/-- The kernel of a transition map of a coherent adic system on stalks. -/
theorem ker_stalk_map {n k : ℕ} (h : n ≤ k) :
    LinearMap.ker ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom =
      IdealSheafData.stalk I y ^ (n + 1) •
        (⊤ : Submodule (X.presheaf.stalk y)
          ((modulesStalkFunctor X y).obj (F.obj.obj (op k)))) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨p, rfl⟩ := completedStalkProj_surjective F y k v
    rw [LinearMap.mem_ker, completedStalkProj_transition F y h p, ← LinearMap.mem_ker,
      completedStalkProj_ker] at hv
    exact Submodule.smul_top_le_comap_smul_top _ (completedStalkProj F y k) hv
  · intro v hv
    have h0 := Submodule.smul_top_le_comap_smul_top _
      ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom hv
    rwa [Submodule.mem_comap, pow_smul_top_stalk_eq_bot F y n] at h0

omit [AlgebraicGeometry.IsNoetherian X] in
/-- The transition maps of a coherent adic system are surjective on stalks. -/
theorem surjective_stalk_map {n k : ℕ} (h : n ≤ k) :
    Function.Surjective ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom :=
  have := F.property.epi_map h
  surjective_stalk_of_epi y _

/-- The stalk of the image of the supported subsheaf of `ℱ_k` in `ℱ_n` is the image of the kernel
of the stalk of the depth-one quotient map. -/
theorem range_stalk_supportedImageMap_eq_map {n k : ℕ} (h : n ≤ k) :
    LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom =
      (LinearMap.ker ((modulesStalkFunctor X y).map
        (toDepthOneQuotient X T hT (F.obj.obj (op k)))).hom).map
          ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom := by
  rw [← range_stalk_kernel_ι, supportedImageMap, Functor.map_comp, ModuleCat.hom_comp,
    LinearMap.range_comp]

end Stalks

/-! ### The completions of the depth-one quotients -/

/-- The depth-one quotients, as an inverse system of coherent modules. -/
def improvedCoherentSystem :
    ℕᵒᵖ ⥤ AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf :=
  ObjectProperty.lift _ (improvedSystem T hT F.obj)
    (fun n => (depthOneQuotient_spec X T hT (F.obj.obj n)).1)

/-- The completions of the depth-one quotients, an inverse system of objects of `Coh(X, ℐ)`. -/
abbrev improvedCompletionSystem : ℕᵒᵖ ⥤ Stacks.Coherent.CoherentAdicSystems I :=
  improvedCoherentSystem F T hT ⋙ completionFunctor X I

/-- The term `ℱ'_m / ℐ^{n+1} ℱ'_m`. -/
abbrev improvedQuotient (n m : ℕ) : X.Modules :=
  ((improvedCompletionSystem F T hT).obj (op m)).obj.obj (op n)

/-- The projection `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m`. -/
abbrev improvedQuotientProj (n m : ℕ) :
    depthOneQuotient X T hT (F.obj.obj (op m)) ⟶ improvedQuotient F T hT n m :=
  completionProjection X I ((improvedCoherentSystem F T hT).obj (op m)) n

/-- The map `ℱ'_{m'} / ℐ^{n+1} ℱ'_{m'} → ℱ'_m / ℐ^{n+1} ℱ'_m` for `m ≤ m'`. -/
abbrev improvedQuotientMap (n : ℕ) {m m' : ℕ} (h : m ≤ m') :
    improvedQuotient F T hT n m' ⟶ improvedQuotient F T hT n m :=
  ((improvedCompletionSystem F T hT).map (homOfLE h).op).hom.app (op n)

/-- The projections `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m` commute with the maps induced by `m ≤ m'`. -/
theorem improvedQuotientProj_comp_map (n : ℕ) {m m' : ℕ} (h : m ≤ m') :
    improvedQuotientProj F T hT n m' ≫ improvedQuotientMap F T hT n h =
      improvedMap T hT F.obj (homOfLE h).op ≫ improvedQuotientProj F T hT n m :=
  completionFunctor_map_quotient X I ((improvedCoherentSystem F T hT).map (homOfLE h).op) n

/-- Up to the identification of `ℱ'_m / ℐ^{n+1} ℱ'_m` with the cokernel of `ℐ^{n+1} ℱ'_m → ℱ'_m`,
the projection is the cokernel projection. -/
theorem improvedQuotientProj_comp_eqToHom (n m : ℕ) :
    improvedQuotientProj F T hT n m ≫ eqToHom (completionFunctor_obj X I
        ((improvedCoherentSystem F T hT).obj (op m)) n) =
      cokernel.π (C := X.Modules) (idealPowerMultiple I (n + 1)
        (depthOneQuotient X T hT (F.obj.obj (op m)))).ι :=
  Stacks.Coherent.completionProjection_comp_eqToHom X I _ n

/-- The projection `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m` is an epimorphism. -/
instance (n m : ℕ) : Epi (improvedQuotientProj F T hT n m) :=
  epi_completionProjection X I _ n

/-- The kernel of the stalk of the projection `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m` is
`ℐ_y^{n+1} ℱ'_{m,y}`. -/
theorem ker_stalk_improvedQuotientProj (y : X) (n m : ℕ) :
    LinearMap.ker ((modulesStalkFunctor X y).map (improvedQuotientProj F T hT n m)).hom =
      IdealSheafData.stalk I y ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y)
        ((modulesStalkFunctor X y).obj (depthOneQuotient X T hT (F.obj.obj (op m))))) := by
  have : (depthOneQuotient X T hT (F.obj.obj (op m))).IsCoherent :=
    (depthOneQuotient_spec X T hT (F.obj.obj (op m))).1
  have : (depthOneQuotient X T hT (F.obj.obj (op m))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  rw [← ker_stalk_cokernel_π_idealPowerMultiple y (n + 1)]
  have hinj : Function.Injective ((modulesStalkFunctor X y).map (eqToHom (completionFunctor_obj X I
      ((improvedCoherentSystem F T hT).obj (op m)) n))).hom := by
    rw [eqToHom_map]
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  ext v
  have hv := congrArg (fun g => g.hom v) ((modulesStalkFunctor X y).map_comp
    (improvedQuotientProj F T hT n m) (eqToHom (completionFunctor_obj X I
      ((improvedCoherentSystem F T hT).obj (op m)) n)))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hv
  rw [improvedQuotientProj_comp_eqToHom] at hv
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  exact ⟨fun h => hv.trans (by rw [h, map_zero]; rfl),
    fun h => hinj ((hv.symm.trans h).trans (map_zero _).symm)⟩

/-- The depth-one quotient map `ℱ_k → ℱ'_k` is surjective on stalks. -/
private theorem surjective_stalk_toDepthOneQuotient (y : X) (k : ℕ) :
    Function.Surjective ((modulesStalkFunctor X y).map
      (toDepthOneQuotient X T hT (F.obj.obj (op k)))).hom :=
  have := (depthOneQuotient_spec X T hT (F.obj.obj (op k))).2.1
  surjective_stalk_of_epi y _

/-- On stalks, the projections `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m` commute with the maps induced by
`m ≤ m'`. -/
private theorem stalk_improvedQuotientMap_improvedQuotientProj_apply (y : X) (n : ℕ) {m m' : ℕ}
    (h : m ≤ m') :
    ∀ z, ((modulesStalkFunctor X y).map (improvedQuotientMap F T hT n h)).hom
      (((modulesStalkFunctor X y).map (improvedQuotientProj F T hT n m')).hom z) =
        ((modulesStalkFunctor X y).map (improvedQuotientProj F T hT n m)).hom
          (((modulesStalkFunctor X y).map (improvedMap T hT F.obj (homOfLE h).op)).hom z) := by
  intro z
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, improvedQuotientProj_comp_map,
    Functor.map_comp, ModuleCat.comp_apply]

/-- On stalks, the depth-one quotient maps `ℱ_m → ℱ'_m` commute with the transition maps. -/
private theorem stalk_improvedMap_toDepthOneQuotient_apply (y : X) {m m' : ℕ} (h : m ≤ m') :
    ∀ w, ((modulesStalkFunctor X y).map (improvedMap T hT F.obj (homOfLE h).op)).hom
      (((modulesStalkFunctor X y).map (toDepthOneQuotient X T hT (F.obj.obj (op m')))).hom w) =
        ((modulesStalkFunctor X y).map (toDepthOneQuotient X T hT (F.obj.obj (op m)))).hom
          (((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom w) := by
  intro w
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, toDepthOneQuotient_comp_improvedMap,
    Functor.map_comp, ModuleCat.comp_apply]

/-- An element of the stalk of `ℱ_k` vanishing in `ℱ'_k / ℐ^{n+1} ℱ'_k` maps into the image of
the sections of `ℱ_n` supported in `T`. -/
private theorem map_mem_range_stalk_supportedImageMap_of_proj_eq_zero (y : X) {n k : ℕ} (h : n ≤ k)
    (w : (modulesStalkFunctor X y).obj (F.obj.obj (op k)))
    (hw : ((modulesStalkFunctor X y).map (improvedQuotientProj F T hT n k)).hom
      (((modulesStalkFunctor X y).map (toDepthOneQuotient X T hT (F.obj.obj (op k)))).hom w) = 0) :
    ((modulesStalkFunctor X y).map (F.obj.map (homOfLE h).op)).hom w ∈
      LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom := by
  let S := modulesStalkFunctor X y
  let τ := toDepthOneQuotient X T hT (F.obj.obj (op k))
  rw [← LinearMap.mem_ker, ker_stalk_improvedQuotientProj] at hw
  have hmap : IdealSheafData.stalk I y ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y)
      ((modulesStalkFunctor X y).obj (depthOneQuotient X T hT (F.obj.obj (op k))))) =
      (IdealSheafData.stalk I y ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y)
        ((modulesStalkFunctor X y).obj (F.obj.obj (op k))))).map (S.map τ).hom := by
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (surjective_stalk_toDepthOneQuotient F T hT y k)]
  rw [hmap] at hw
  obtain ⟨i, hi, hiw⟩ := hw
  rw [range_stalk_supportedImageMap_eq_map]
  have hi0 : (S.map (F.obj.map (homOfLE h).op)).hom i = 0 := by
    rw [← LinearMap.mem_ker, ker_stalk_map F y h]
    exact hi
  refine ⟨w - i, ?_, ?_⟩
  · show (S.map τ).hom (w - i) = 0
    rw [map_sub, hiw, sub_self]
  · rw [map_sub, hi0, sub_zero]

/-- **Past the stabilization level, `ℱ'_m / ℐ^{n+1} ℱ'_m` does not depend on `m`.** -/
theorem isIso_improvedQuotientMap (n : ℕ) {m m' : ℕ} (hnm : n ≤ m) (h : m ≤ m')
    (hstab : ∀ y : X,
      LinearMap.range ((modulesStalkFunctor X y).map
          (supportedImageMap F T hT (hnm.trans h))).hom =
        LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT hnm)).hom) :
    IsIso (improvedQuotientMap F T hT n h) := by
  apply Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk
  intro y
  rw [ConcreteCategory.isIso_iff_bijective]
  let S := modulesStalkFunctor X y
  let τ := fun k => toDepthOneQuotient X T hT (F.obj.obj (op k))
  have hpsurj : ∀ k, Function.Surjective (S.map (improvedQuotientProj F T hT n k)).hom :=
    fun k => surjective_stalk_of_epi y _
  show Function.Bijective (S.map (improvedQuotientMap F T hT n h)).hom
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    obtain ⟨v, rfl⟩ := hpsurj m' z
    obtain ⟨w, rfl⟩ := surjective_stalk_toDepthOneQuotient F T hT y m' v
    rw [stalk_improvedQuotientMap_improvedQuotientProj_apply F T hT y n h,
      stalk_improvedMap_toDepthOneQuotient_apply F T hT y h] at hz
    have hmem : (S.map (F.obj.map (homOfLE (hnm.trans h)).op)).hom w ∈
        LinearMap.range (S.map (supportedImageMap F T hT hnm)).hom := by
      have := map_mem_range_stalk_supportedImageMap_of_proj_eq_zero F T hT y hnm _ hz
      rwa [← ModuleCat.comp_apply, ← Functor.map_comp, ← F.obj.map_comp] at this
    rw [← hstab y, range_stalk_supportedImageMap_eq_map] at hmem
    obtain ⟨k', hk', hk'w⟩ := hmem
    have hdiff : w - k' ∈ IdealSheafData.stalk I y ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y)
        ((modulesStalkFunctor X y).obj (F.obj.obj (op m')))) := by
      rw [← ker_stalk_map F y (hnm.trans h), LinearMap.mem_ker, map_sub, hk'w, sub_self]
    have hτdiff : (S.map (τ m')).hom (w - k') ∈
        LinearMap.ker (S.map (improvedQuotientProj F T hT n m')).hom := by
      rw [ker_stalk_improvedQuotientProj]
      exact Submodule.smul_top_le_comap_smul_top _ (S.map (τ m')).hom hdiff
    rw [LinearMap.mem_ker, map_sub, (LinearMap.mem_ker.mp hk'), sub_zero] at hτdiff
    rw [hτdiff]
    exact Submodule.zero_mem _
  · intro z
    obtain ⟨v, rfl⟩ := hpsurj m z
    obtain ⟨w, rfl⟩ := surjective_stalk_toDepthOneQuotient F T hT y m v
    obtain ⟨w', rfl⟩ := surjective_stalk_map F y h w
    exact ⟨(S.map (improvedQuotientProj F T hT n m')).hom ((S.map (τ m')).hom w'), by
      rw [stalk_improvedQuotientMap_improvedQuotientProj_apply F T hT y n h,
        stalk_improvedMap_toDepthOneQuotient_apply F T hT y h]⟩

/-- The projections onto the terms of a completion are compatible with all transition maps. -/
theorem completionProjection_comp_map
    (M : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) {n n' : ℕ}
    (h : n ≤ n') :
    completionProjection X I M n' ≫ ((completionFunctor X I).obj M).obj.map (homOfLE h).op =
      completionProjection X I M n := by
  induction n', h using Nat.le_induction with
  | base =>
    rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  | succ n' h ih =>
    have hsplit : ((completionFunctor X I).obj M).obj.map (homOfLE (h.trans (Nat.le_succ n'))).op =
        ((completionFunctor X I).obj M).obj.map (homOfLE (Nat.le_succ n')).op ≫
          ((completionFunctor X I).obj M).obj.map (homOfLE h).op := by
      rw [← CategoryTheory.Functor.map_comp]
      rfl
    rw [hsplit]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun g => g ≫ ((completionFunctor X I).obj M).obj.map (homOfLE h).op)
        (completionProjection_transition X I M n')).trans ih)

/-- The projections `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m` commute with the transition maps of the completion
of `ℱ'_m`. -/
theorem improvedQuotientProj_comp_completionMap {n n' : ℕ} (h : n ≤ n') (m : ℕ) :
    improvedQuotientProj F T hT n' m ≫
        ((improvedCompletionSystem F T hT).obj (op m)).obj.map (homOfLE h).op =
      improvedQuotientProj F T hT n m :=
  completionProjection_comp_map _ h

/-- The transition map of the depth-one quotients along an identity is the identity. -/
theorem improvedMap_id (m : ℕ) : improvedMap T hT F.obj (𝟙 (op m)) = 𝟙 _ :=
  (improvedSystem T hT F.obj).map_id _

/-- The transition maps of the depth-one quotients are compatible with composition. -/
theorem improvedMap_comp {a b c : ℕᵒᵖ} (f : a ⟶ b) (g : b ⟶ c) :
    improvedMap T hT F.obj (f ≫ g) = improvedMap T hT F.obj f ≫ improvedMap T hT F.obj g :=
  (improvedSystem T hT F.obj).map_comp _ _

section Diagonal

variable {μ : ℕ → ℕ} (hμmono : Monotone μ)

/-- The transition map of the diagonal system `n ↦ ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}`. -/
def diagonalMap {n n' : ℕ} (h : n ≤ n') :
    improvedQuotient F T hT n' (μ n') ⟶ improvedQuotient F T hT n (μ n) :=
  ((improvedCompletionSystem F T hT).obj (op (μ n'))).obj.map (homOfLE h).op ≫
    improvedQuotientMap F T hT n (hμmono h)

/-- The projections `ℱ'_{μ(n)} → ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}` intertwine the transition maps of
the depth-one quotients and of the diagonal system. -/
theorem improvedQuotientProj_comp_diagonalMap {n n' : ℕ} (h : n ≤ n') :
    improvedQuotientProj F T hT n' (μ n') ≫ diagonalMap F T hT hμmono h =
      improvedMap T hT F.obj (homOfLE (hμmono h)).op ≫ improvedQuotientProj F T hT n (μ n) := by
  rw [diagonalMap, ← Category.assoc, improvedQuotientProj_comp_completionMap,
    improvedQuotientProj_comp_map]

/-- The diagonal system `n ↦ ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}`. -/
def diagonalSystem : ℕᵒᵖ ⥤ X.Modules where
  obj n := improvedQuotient F T hT n.unop (μ n.unop)
  map f := diagonalMap F T hT hμmono (leOfHom f.unop)
  map_id n := by
    apply (cancel_epi (improvedQuotientProj F T hT n.unop (μ n.unop))).mp
    rw [improvedQuotientProj_comp_diagonalMap,
      show (homOfLE (hμmono (leOfHom (𝟙 n).unop))).op = 𝟙 (op (μ n.unop)) from
        Subsingleton.elim _ _, improvedMap_id, Category.id_comp, Category.comp_id]
  map_comp {a b c} f g := by
    apply (cancel_epi (improvedQuotientProj F T hT a.unop (μ a.unop))).mp
    rw [improvedQuotientProj_comp_diagonalMap,
      show (homOfLE (hμmono (leOfHom (f ≫ g).unop))).op =
        (homOfLE (hμmono (leOfHom f.unop))).op ≫ (homOfLE (hμmono (leOfHom g.unop))).op from
          Subsingleton.elim _ _, improvedMap_comp]
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun k => improvedMap T hT F.obj (homOfLE (hμmono (leOfHom f.unop))).op ≫ k)
      (improvedQuotientProj_comp_diagonalMap F T hT hμmono (leOfHom g.unop)).symm).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ diagonalMap F T hT hμmono (leOfHom g.unop))
      (improvedQuotientProj_comp_diagonalMap F T hT hμmono (leOfHom f.unop)).symm).trans ?_
    exact Category.assoc _ _ _

/-- The transition maps of the diagonal system are the maps `diagonalMap`. -/
theorem diagonalSystem_map {n n' : ℕ} (h : n ≤ n') :
    (diagonalSystem F T hT hμmono).map (homOfLE h).op = diagonalMap F T hT hμmono h := rfl

variable {hμmono} in
/-- **The diagonal system is a coherent adic system** as soon as the quotient maps between the
completions of the depth-one quotients at the levels `μ(n) ≤ μ(n+1)` are isomorphisms. -/
theorem isCoherentAdicSystem_diagonalSystem
    (hiso : ∀ n, IsIso (improvedQuotientMap F T hT n (hμmono (Nat.le_succ n)))) :
    Stacks.Coherent.IsCoherentAdicSystem I (diagonalSystem F T hT hμmono) := by
  refine ⟨fun n => ((improvedCompletionSystem F T hT).obj (op (μ n))).property.isCoherent n,
    fun n => ((improvedCompletionSystem F T hT).obj (op (μ n))).property.idealPowerMultiple_eq_bot
      n, fun n => ?_⟩
  refine ⟨((improvedCompletionSystem F T hT).obj (op (μ (n + 1)))).property.quotientIso n ≪≫
    @asIso _ _ _ _ (improvedQuotientMap F T hT n (hμmono (Nat.le_succ n))) (hiso n), ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ improvedQuotientMap F T hT n (hμmono (Nat.le_succ n)))
      (((improvedCompletionSystem F T hT).obj (op (μ (n + 1)))).property.cokernel_π_comp_quotientIso
        n))

end Diagonal

/-! ### The pro-isomorphism -/

/-- An element of the stalk of `ℱ_n` killed by the stalk of a map `ℱ_n → ℱ'_{μ}/ℐ^{n+1}ℱ'_{μ}`
factoring the depth-one quotient comes from the sections supported in `T`. -/
theorem mem_range_stalk_supportedImageMap_of_comp_eq_zero (y : X) {n k : ℕ} (h : n ≤ k)
    (g : F.obj.obj (op n) ⟶ improvedQuotient F T hT n k)
    (hg : F.obj.map (homOfLE h).op ≫ g =
      toDepthOneQuotient X T hT (F.obj.obj (op k)) ≫ improvedQuotientProj F T hT n k)
    (v : (modulesStalkFunctor X y).obj (F.obj.obj (op n)))
    (hv : ((modulesStalkFunctor X y).map g).hom v = 0) :
    v ∈ LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom := by
  obtain ⟨w, rfl⟩ := surjective_stalk_map F y h v
  refine map_mem_range_stalk_supportedImageMap_of_proj_eq_zero F T hT y h w ?_
  have := congrArg (fun f => ((modulesStalkFunctor X y).map f).hom w) hg
  simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp,
    Function.comp_apply] at this
  exact this.symm.trans hv

/-- The `n`-th depth-one quotient is annihilated by `ℐ^{n+1}`. -/
private theorem idealPowerMultiple_depthOneQuotient_eq_bot (n : ℕ) :
    idealPowerMultiple I (n + 1) (depthOneQuotient X T hT (F.obj.obj (op n))) = ⊥ := by
  have : (F.obj.obj (op n)).IsQuasicoherent := F.property.isQuasicoherent n
  have : (depthOneQuotient X T hT (F.obj.obj (op n))).IsCoherent :=
    (depthOneQuotient_spec X T hT (F.obj.obj (op n))).1
  have : (depthOneQuotient X T hT (F.obj.obj (op n))).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1
  have := (depthOneQuotient_spec X T hT (F.obj.obj (op n))).2.1
  exact idealPowerMultiple_eq_bot_of_epi I (n + 1) (toDepthOneQuotient X T hT (F.obj.obj (op n)))
    (F.property.idealPowerMultiple_eq_bot n)

/-- The map `ℱ'_m / ℐ^{n+1} ℱ'_m → ℱ'_n` induced by the transition map, for `n ≤ m`. -/
private def improvedQuotientToDepthOne {n m : ℕ} (h : n ≤ m) :
    improvedQuotient F T hT n m ⟶ depthOneQuotient X T hT (F.obj.obj (op n)) :=
  eqToHom (completionFunctor_obj X I ((improvedCoherentSystem F T hT).obj (op m)) n) ≫
    cokernel.desc (C := X.Modules) _ (improvedMap T hT F.obj (homOfLE h).op)
      (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) _
        (idealPowerMultiple_depthOneQuotient_eq_bot F T hT n))

/-- The composite `ℱ'_m → ℱ'_m / ℐ^{n+1} ℱ'_m → ℱ'_n` is the transition map of the depth-one
quotients. -/
private theorem improvedQuotientProj_comp_improvedQuotientToDepthOne {n m : ℕ} (h : n ≤ m) :
    improvedQuotientProj F T hT n m ≫ improvedQuotientToDepthOne F T hT h =
      improvedMap T hT F.obj (homOfLE h).op := by
  rw [improvedQuotientToDepthOne]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ cokernel.desc (C := X.Modules) _
        (improvedMap T hT F.obj (homOfLE h).op)
        (comp_eq_zero_of_idealPowerMultiple_eq_bot I (n + 1) _
          (idealPowerMultiple_depthOneQuotient_eq_bot F T hT n)))
      (improvedQuotientProj_comp_eqToHom F T hT n m)).trans (cokernel.π_desc _ _ _))

/-- Lifts `ℱ_n → ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}` of the depth-one quotients are compatible with
the transition maps of the diagonal system. -/
private theorem map_comp_eq_comp_diagonalMap {μ : ℕ → ℕ} (hμ : ∀ n, n ≤ μ n) (hμmono : Monotone μ)
    (φc : ∀ n, F.obj.obj (op n) ⟶ improvedQuotient F T hT n (μ n))
    (hφc : ∀ n, F.obj.map (homOfLE (hμ n)).op ≫ φc n =
      toDepthOneQuotient X T hT (F.obj.obj (op (μ n))) ≫ improvedQuotientProj F T hT n (μ n))
    {n n' : ℕ} (h : n ≤ n') :
    F.obj.map (homOfLE h).op ≫ φc n = φc n' ≫ diagonalMap F T hT hμmono h := by
  have := F.property.epi_map (hμ n')
  apply (cancel_epi (F.obj.map (homOfLE (hμ n')).op)).mp
  have e₁ : F.obj.map (homOfLE (hμ n')).op ≫ F.obj.map (homOfLE h).op =
      F.obj.map (homOfLE (hμmono h)).op ≫ F.obj.map (homOfLE (hμ n)).op := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    rfl
  rw [reassoc_of% e₁, hφc n,
    ← reassoc_of% (toDepthOneQuotient_comp_improvedMap T hT F.obj (homOfLE (hμmono h)).op),
    ← improvedQuotientProj_comp_diagonalMap F T hT hμmono h, reassoc_of% (hφc n')]

/-- The maps `ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)} → ℱ'_n` intertwine the transition maps of the diagonal
system and of the depth-one quotients. -/
private theorem diagonalMap_comp_improvedQuotientToDepthOne {μ : ℕ → ℕ} (hμ : ∀ n, n ≤ μ n)
    (hμmono : Monotone μ) {n n' : ℕ} (h : n ≤ n') :
    diagonalMap F T hT hμmono h ≫ improvedQuotientToDepthOne F T hT (hμ n) =
      improvedQuotientToDepthOne F T hT (hμ n') ≫ improvedMap T hT F.obj (homOfLE h).op := by
  apply (cancel_epi (improvedQuotientProj F T hT n' (μ n'))).mp
  have e₂ : improvedMap T hT F.obj (homOfLE (hμmono h)).op ≫
      improvedMap T hT F.obj (homOfLE (hμ n)).op =
      improvedMap T hT F.obj (homOfLE (hμ n')).op ≫ improvedMap T hT F.obj (homOfLE h).op := by
    rw [← improvedMap_comp, ← improvedMap_comp]
    rfl
  rw [reassoc_of% (improvedQuotientProj_comp_diagonalMap F T hT hμmono h),
    improvedQuotientProj_comp_improvedQuotientToDepthOne F T hT (hμ n),
    reassoc_of% (improvedQuotientProj_comp_improvedQuotientToDepthOne F T hT (hμ n')), e₂]

/-- A lift `ℱ_n → ℱ'_{μ(n)} / ℐ^{n+1} ℱ'_{μ(n)}` of the depth-one quotient, followed by the map to
`ℱ'_n`, is the depth-one quotient map `ℱ_n → ℱ'_n`. -/
private theorem comp_improvedQuotientToDepthOne_eq_toDepthOneQuotient {μ : ℕ → ℕ}
    (hμ : ∀ n, n ≤ μ n)
    (φc : ∀ n, F.obj.obj (op n) ⟶ improvedQuotient F T hT n (μ n))
    (hφc : ∀ n, F.obj.map (homOfLE (hμ n)).op ≫ φc n =
      toDepthOneQuotient X T hT (F.obj.obj (op (μ n))) ≫ improvedQuotientProj F T hT n (μ n))
    (n : ℕ) :
    φc n ≫ improvedQuotientToDepthOne F T hT (hμ n) =
      toDepthOneQuotient X T hT (F.obj.obj (op n)) := by
  have := F.property.epi_map (hμ n)
  apply (cancel_epi (F.obj.map (homOfLE (hμ n)).op)).mp
  rw [reassoc_of% (hφc n), improvedQuotientProj_comp_improvedQuotientToDepthOne,
    toDepthOneQuotient_comp_improvedMap]

/-- A map `ℱ_n → ℱ'_k / ℐ^{n+1} ℱ'_k` factoring the depth-one quotient has kernel annihilated by
`ℐ^c` as soon as `ℐ^c` annihilates the stalks of the image of the sections supported in `T`. -/
private theorem idealPowerMultiple_kernel_eq_bot_of_fac {n k : ℕ} (h : n ≤ k)
    (g : F.obj.obj (op n) ⟶ improvedQuotient F T hT n k)
    (hg : F.obj.map (homOfLE h).op ≫ g =
      toDepthOneQuotient X T hT (F.obj.obj (op k)) ≫ improvedQuotientProj F T hT n k) (c : ℕ)
    (hann : ∀ y : X, ∀ a ∈ IdealSheafData.stalk I y ^ c,
      ∀ v ∈ LinearMap.range ((modulesStalkFunctor X y).map (supportedImageMap F T hT h)).hom,
        a • v = 0) :
    idealPowerMultiple I c (kernel g) = ⊥ := by
  apply idealPowerMultiple_eq_bot_of_affine_sections_annihilated
  intro U r hr x
  let K := kernel g
  refine TopCat.Presheaf.section_ext ⟨K.presheaf, K.isSheaf⟩ U.1 _ 0 fun y hy => ?_
  show (K.presheaf.germ U.1 y hy).hom (r • x) = (K.presheaf.germ U.1 y hy).hom 0
  rw [map_zero, germ_smul y U.1 hy r x]
  let S := modulesStalkFunctor X y
  have hinj : Function.Injective (S.map (kernel.ι g)).hom :=
    (ModuleCat.mono_iff_injective _).mp (Functor.map_mono _ _)
  let v : S.obj K := (K.presheaf.germ U.1 y hy).hom x
  have hv : (S.map g).hom ((S.map (kernel.ι g)).hom v) = 0 := by
    simpa only [CategoryTheory.Functor.map_comp, ModuleCat.hom_comp, LinearMap.coe_comp,
      Function.comp_apply, CategoryTheory.Functor.map_zero, ModuleCat.hom_zero,
      LinearMap.zero_apply] using congrArg (fun f => (S.map f).hom v) (kernel.condition g)
  refine hinj ?_
  rw [map_smul]
  exact (hann y _ (germ_mem_stalk_pow I c U hy hr) _
    (mem_range_stalk_supportedImageMap_of_comp_eq_zero F T hT y h g hg _ hv)).trans
      (map_zero _).symm

/-- **The improvement of a coherent formal module, as data in `Coh(X, ℐ)`.** Under the depth
condition of Stacks 0EJE there are a monotone `μ` with `n ≤ μ n`, an object `(𝒢_n)` of `Coh(X, ℐ)`,
a morphism `φ : (ℱ_n) → (𝒢_n)` and a morphism `ψ : (𝒢_n) → (ℱ'_n)` with `φ ≫ ψ` the canonical map
onto the depth-one quotients, and maps `π_m : ℱ'_{μ(m)} → 𝒢_m` inverting `ψ` up to the transition
maps, such that `φ` is an epimorphism of `Coh(X, ℐ)` whose kernel is annihilated by a power of
`ℐ`. -/
theorem exists_coherentAdicSystem_improvement (hTY : T ⊆ I.support)
    (h6 : ∀ y ∈ T, ∀ p : PrimeSpectrum (completedLocalRing I y),
      p.asIdeal ≠ completedMaximalIdeal I y →
      adicClosedFibreThrough I y p = {completedMaximalIdeal I y} →
      0 < completedStalkDepth I F y p) :
    ∃ (μ : ℕ → ℕ) (hμ : ∀ n, n ≤ μ n) (hμmono : Monotone μ)
      (G : Stacks.Coherent.CoherentAdicSystems I) (φ : F ⟶ G)
      (ψ : G.obj ⟶ improvedSystem T hT F.obj)
      (π : ∀ m, depthOneQuotient X T hT (F.obj.obj (op (μ m))) ⟶ G.obj.obj (op m)),
      φ.hom ≫ ψ = toImprovedSystem T hT F.obj ∧
      (∀ m, π m ≫ ψ.app (op m) = improvedMap T hT F.obj (homOfLE (hμ m)).op) ∧
      (∀ {m m' : ℕ} (h : m ≤ m'), improvedMap T hT F.obj (homOfLE (hμmono h)).op ≫ π m =
        π m' ≫ G.obj.map (homOfLE h).op) ∧
      (∀ m, ψ.app (op (μ m)) ≫ π m = G.obj.map (homOfLE (hμ m)).op) ∧
      Epi φ ∧
      ∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((kernel φ).obj.obj (op n)) = ⊥ := by
  obtain ⟨μ, hμ, c, hμmono, hstab, hann⟩ := exists_stalk_range_supportedImageMap_eq F T hT hTY h6
  have hiso : ∀ n, IsIso (improvedQuotientMap F T hT n (hμmono (Nat.le_succ n))) := fun n =>
    isIso_improvedQuotientMap F T hT n (hμ n) (hμmono (Nat.le_succ n))
      (fun y => hstab n _ _ (hμmono (Nat.le_succ n)) y)
  let G : Stacks.Coherent.CoherentAdicSystems I :=
    ⟨diagonalSystem F T hT hμmono, isCoherentAdicSystem_diagonalSystem F T hT hiso⟩
  let τ := fun k => toDepthOneQuotient X T hT (F.obj.obj (op k))
  have hτepi : ∀ k, Epi (τ k) := fun k => (depthOneQuotient_spec X T hT (F.obj.obj (op k))).2.1
  have hφex : ∀ n, ∃ g : F.obj.obj (op n) ⟶ G.obj.obj (op n),
      F.obj.map (homOfLE (hμ n)).op ≫ g = τ (μ n) ≫ improvedQuotientProj F T hT n (μ n) :=
    fun n => Stacks.Coherent.exists_coherentAdicSystemDesc I F n (μ n) (hμ n)
      (G.property.idealPowerMultiple_eq_bot n) _
  choose φc hφc using hφex
  let φ : F ⟶ G := ObjectProperty.homMk
    { app := fun n => φc n.unop
      naturality := fun a b f => by
        rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
        exact map_comp_eq_comp_diagonalMap F T hT hμ hμmono φc hφc (leOfHom f.unop) }
  let ψ : G.obj ⟶ improvedSystem T hT F.obj :=
    { app := fun n => improvedQuotientToDepthOne F T hT (hμ n.unop)
      naturality := fun a b f => by
        rw [show f = (homOfLE (leOfHom f.unop)).op from Subsingleton.elim _ _]
        exact diagonalMap_comp_improvedQuotientToDepthOne F T hT hμ hμmono (leOfHom f.unop) }
  have hφψ : φ.hom ≫ ψ = toImprovedSystem T hT F.obj := by
    refine NatTrans.ext (funext fun n => ?_)
    obtain ⟨n⟩ := n
    exact comp_improvedQuotientToDepthOne_eq_toDepthOneQuotient F T hT hμ φc hφc n
  refine ⟨μ, hμ, hμmono, G, φ, ψ, fun m => improvedQuotientProj F T hT m (μ m), hφψ,
    fun m => improvedQuotientProj_comp_improvedQuotientToDepthOne F T hT (hμ m),
    fun h => (improvedQuotientProj_comp_diagonalMap F T hT hμmono h).symm, fun m => ?_, ?_, c,
    fun n => ?_⟩
  · apply (cancel_epi (improvedQuotientProj F T hT (μ m) (μ (μ m)))).mp
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (fun k => k ≫ improvedQuotientProj F T hT m (μ m))
      (improvedQuotientProj_comp_improvedQuotientToDepthOne F T hT (hμ (μ m)))).trans ?_
    exact (improvedQuotientProj_comp_diagonalMap F T hT hμmono (hμ m)).symm
  · rw [Stacks.Coherent.epi_iff_epi_app_zero]
    have := hτepi (μ 0)
    have := epi_completionProjection X I ((improvedCoherentSystem F T hT).obj (op (μ 0))) 0
    have hepi := epi_comp (τ (μ 0)) (improvedQuotientProj F T hT 0 (μ 0))
    exact @epi_of_epi_fac _ _ _ _ _ _ _ _ hepi (hφc 0)
  · refine Stacks.Coherent.idealPowerMultiple_kernel_obj_eq_bot_of_termwise I I φ c (fun n => ?_) n
    exact idealPowerMultiple_kernel_eq_bot_of_fac F T hT (hμ n) (φc n) (hφc n) c (hann n)

end Stacks.Algebraization

end
