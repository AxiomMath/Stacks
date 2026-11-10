module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CompletedStalkDepthEpi
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.KernelCokernelAnnihilation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalk

/-!
# Levelwise annihilation from annihilation of the kernel and cokernel in `Coh(X, ℐ)`

Let `X` be a Noetherian scheme, `ℐ` a quasi-coherent ideal sheaf and `σ : (ℱₙ) → (𝒢ₙ)` a
morphism of `Coh(X, ℐ)`. The kernel and the cokernel of `σ` in the abelian category `Coh(X, ℐ)`
are not the levelwise ones in general: the cokernel is, but the kernel is the system of stable
kernel images. This file proves that if the terms of the kernel and of the cokernel of `σ` in
`Coh(X, ℐ)` are annihilated by `ℐ^a` and `ℐ^b`, then the levelwise kernels and cokernels of the
maps `σₙ : ℱₙ → 𝒢ₙ` are annihilated by `ℐ^{a+b}`, that is, `σ` has kernel and cokernel
annihilated by a power of `ℐ` in the levelwise sense of [Stacks, Tag 0888].

## Main results

* `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_hom_of_kernel_cokernel` — the transfer.

## Proof outline

The cokernel of `σ` in `Coh(X, ℐ)` is computed levelwise, which gives the cokernels. For the
kernels everything is checked on stalks at a point `y`, where the stalk functor is exact and
`ℐ_y` is an ideal of the local ring `𝒪_{X,y}`. Let `w ∈ ℱ_{n,y}` with `σₙ(w) = 0`, `q ∈ ℐ_y^b` and
`p ∈ ℐ_y^a`. Let `𝒦ₙ` be the `n`-th term of the kernel of `σ`; it is `𝒮ₘ/ℐ^{n+1}𝒮ₘ` for the stable
kernel image `𝒮ₘ = Im(Ker(σ_l) → ℱₘ)` at a level `m ≥ n` computed from a level `l ≥ m`.

Lift `w` to `w' ∈ ℱ_{l,y}`. Then `σ_l(w')` maps to zero in `𝒢_{n,y}`, so it lies in
`ℐ_y^{n+1}𝒢_{l,y}`; multiplying by `q`, which carries `𝒢_{l,y}` into the image of `σ_l` because the
cokernel of `σ_l` is killed by `ℐ^b`, gives `q σ_l(w') = σ_l(f)` with `f ∈ ℐ_y^{n+1}ℱ_{l,y}`. So
`q w' - f` lies in the kernel of `σ_l`, and its image `q w` in `ℱ_{n,y}` comes from `𝒮ₘ`, hence
from `𝒦ₙ`, which `p` kills. So `ℐ_y^a ℐ_y^b` kills the stalks of `Ker(σₙ)`, and the germ argument
turns this into `ℐ^{a+b} Ker(σₙ) = 0`.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Algebraization Stacks.ModuleSkyscraper

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

variable {X : Scheme.{u}}

/-- A sheaf of modules whose stalks are all annihilated by the `t`-th power of the stalk of `ℐ`
is annihilated by `ℐ^t`: an affine-local section `r • x` vanishes because all its germs do. -/
private theorem idealPowerMultiple_eq_bot_of_stalks (I : X.IdealSheafData) (t : ℕ)
    (M : X.Modules)
    (h : ∀ (y : X), ∀ a ∈ IdealSheafData.stalk I y ^ t,
      ∀ v : (modulesStalkFunctor X y).obj M, a • v = 0) :
    idealPowerMultiple I t M = ⊥ := by
  apply idealPowerMultiple_eq_bot_of_affine_sections_annihilated
  intro U r hr x
  refine TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ U.1 _ 0 fun y hy => ?_
  change (M.presheaf.germ U.1 y hy).hom (r • x) = (M.presheaf.germ U.1 y hy).hom 0
  rw [map_zero, germ_smul y U.1 hy r x]
  exact h y _ (germ_mem_stalk_pow I t U hy hr) _

section Stalk

variable [IsLocallyNoetherian X] {I : X.IdealSheafData}

omit [IsLocallyNoetherian X] in
/-- The transition maps of a coherent adic system are surjective on stalks, with kernel inside
`ℐ_y^{n+1}` times the stalk. -/
private theorem stalk_transition_surjective_and_ker_le (H : CoherentAdicSystems I) (y : X)
    {n m : ℕ} (h : n ≤ m) :
    Function.Surjective ((modulesStalkFunctor X y).map (H.obj.map (homOfLE h).op)).hom ∧
      LinearMap.ker ((modulesStalkFunctor X y).map (H.obj.map (homOfLE h).op)).hom ≤
        IdealSheafData.stalk I y ^ (n + 1) •
          (⊤ : Submodule (X.presheaf.stalk y)
            ((modulesStalkFunctor X y).obj (H.obj.obj (op m)))) := by
  induction m, h using Nat.le_induction with
  | base =>
    have h1 : H.obj.map (homOfLE (le_refl n)).op = 𝟙 _ := by
      rw [show (homOfLE (le_refl n)).op = 𝟙 (op n) from Subsingleton.elim _ _, H.obj.map_id]
    rw [h1, CategoryTheory.Functor.map_id, ModuleCat.hom_id]
    refine ⟨fun x => ⟨x, rfl⟩, fun x hx => ?_⟩
    have hx0 : x = 0 := hx
    rw [hx0]
    exact Submodule.zero_mem _
  | succ m hnm ih =>
    have hsplit : H.obj.map (homOfLE (hnm.trans (Nat.le_succ m))).op =
        H.obj.map (homOfLE (Nat.le_succ m)).op ≫ H.obj.map (homOfLE hnm).op := by
      rw [← H.obj.map_comp]
      rfl
    have ht1 := surjective_stalk_coherentAdicTransition H y m
    have hk1 := ker_stalk_coherentAdicTransition H y m
    rw [hsplit, Functor.map_comp, ModuleCat.hom_comp]
    refine ⟨ih.1.comp ht1, fun x hx => ?_⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
    have hx' := ih.2 hx
    rw [← map_smul_top_local _ _ ht1] at hx'
    obtain ⟨x0, hx0, hx0e⟩ := hx'
    have hdiff : x - x0 ∈ IdealSheafData.stalk I y ^ (m + 1) •
        (⊤ : Submodule (X.presheaf.stalk y)
          ((modulesStalkFunctor X y).obj (H.obj.obj (op (m + 1))))) := by
      rw [← hk1, LinearMap.mem_ker, map_sub, hx0e, sub_self]
    have hle : IdealSheafData.stalk I y ^ (m + 1) • (⊤ : Submodule (X.presheaf.stalk y)
        ((modulesStalkFunctor X y).obj (H.obj.obj (op (m + 1))))) ≤
        IdealSheafData.stalk I y ^ (n + 1) • ⊤ :=
      Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
    have := Submodule.add_mem _ (hle hdiff) hx0
    rwa [sub_add_cancel] at this

end Stalk

variable [IsNoetherian X] {I : X.IdealSheafData}

/-- **Levelwise annihilation of kernels and cokernels from annihilation in `Coh(X, ℐ)`.** Let
`σ : (ℱₙ) → (𝒢ₙ)` be a morphism of `Coh(X, ℐ)` on a Noetherian scheme. If the terms of the
kernel of `σ` in `Coh(X, ℐ)` are annihilated by a power of `ℐ`, and so are the terms of its
cokernel, then the levelwise kernels and cokernels of the maps `σₙ : ℱₙ → 𝒢ₙ` are all
annihilated by one positive power of `ℐ`. -/
public theorem isKernelCokernelAnnihilatedByPower_hom_of_kernel_cokernel
    {F G : CoherentAdicSystems I} (σ : F ⟶ G)
    (hker : ∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((kernel σ).obj.obj (op n)) = ⊥)
    (hcok : ∃ c : ℕ, ∀ n : ℕ, idealPowerMultiple I c ((cokernel σ).obj.obj (op n)) = ⊥) :
    IsKernelCokernelAnnihilatedByPower I σ.hom := by
  obtain ⟨a, ha⟩ := hker
  obtain ⟨b, hb⟩ := hcok
  have hqc : ∀ M : X.Modules, M.IsCoherent → M.IsQuasicoherent := fun M hM =>
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent M).1
  -- the levelwise cokernels
  have hcokn : ∀ n, idealPowerMultiple I b (cokernel (σ.hom.app (op n))) = ⊥ := fun n =>
    idealPowerMultiple_eq_bot_of_iso I
      ((((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
        (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel σ)
          (coherentAdicCokernelIsColimit I σ))).app (op n)).trans
        (cokernelObjIso σ.hom (op n))).symm b (hb n)
  -- the terms of the kernel, as the system of stable kernel images
  have hKn : ∀ n, idealPowerMultiple I a ((coherentAdicKernel I σ).obj.obj (op n)) = ⊥ :=
    fun n => idealPowerMultiple_eq_bot_of_iso I
      (((ObjectProperty.ι (IsCoherentAdicSystem I)).mapIso
        (IsLimit.conePointUniqueUpToIso (kernelIsKernel σ)
          (coherentAdicKernelIsLimit I σ))).app (op n)).symm a (ha n)
  refine IsKernelCokernelAnnihilatedByPower.of_exists_kernel_cokernel
    ⟨a + b + 1, by omega, fun n => ?_⟩
    ⟨b + 1, by omega, fun n => idealPowerMultiple_eq_bot_of_le (hcokn n) (by omega)⟩
  refine idealPowerMultiple_eq_bot_of_le (n := a + b) ?_ (by omega)
  refine idealPowerMultiple_eq_bot_of_stalks I (a + b) _ fun y s hs v => ?_
  let S := modulesStalkFunctor X y
  let J := IdealSheafData.stalk I y
  have : (F.obj.obj (op n)).IsCoherent := F.property.1 n
  have : (G.obj.obj (op n)).IsCoherent := G.property.1 n
  have hinj : Function.Injective (S.map (kernel.ι (σ.hom.app (op n)))).hom :=
    (ModuleCat.mono_iff_injective _).mp (S.map_mono _)
  refine hinj ?_
  rw [map_smul, map_zero]
  -- the key claim on `w = ι(v)`
  set w := (S.map (kernel.ι (σ.hom.app (op n)))).hom v with hw
  have hσw : (S.map (σ.hom.app (op n))).hom w = 0 := by
    have := congrArg (fun g => (S.map g).hom v) (kernel.condition (σ.hom.app (op n)))
    simpa only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, Functor.map_zero,
      ModuleCat.hom_zero, LinearMap.zero_apply] using this
  -- the levels
  obtain ⟨c, hc⟩ := kernelImageQuotients_eventuallyConstant I σ n
  set m := n + c with hm
  obtain ⟨e, he⟩ := hc m le_rfl
  set l := kernelStableLevel I σ m with hl
  have hml : m ≤ l := le_kernelStableLevel I σ m
  have hnl : n ≤ l := (Nat.le_add_right n c).trans hml
  have : (F.obj.obj (op l)).IsCoherent := F.property.1 l
  have : (G.obj.obj (op l)).IsCoherent := G.property.1 l
  -- exactness of the stalks at the level `l`
  have hex : ∀ T : ShortComplex X.Modules, T.Exact →
      LinearMap.range (S.map T.f).hom = LinearMap.ker (S.map T.g).hom := fun T hT =>
    (ShortComplex.moduleCat_exact_iff_range_eq_ker (T.map S)).mp (hT.map S)
  have hexK := hex _ (ShortComplex.exact_kernel (σ.hom.app (op l)))
  have hexC := hex _ (ShortComplex.exact_cokernel (σ.hom.app (op l)))
  have : (cokernel (σ.hom.app (op l))).IsCoherent :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel _
  have := hqc _ (inferInstance : (cokernel (σ.hom.app (op l))).IsCoherent)
  -- `ℐ_y^b` carries the stalk of `𝒢_l` into the image of `σ_l`
  have hJb : ∀ q ∈ J ^ b, ∀ g : S.obj (G.obj.obj (op l)),
      q • g ∈ LinearMap.range (S.map (σ.hom.app (op l))).hom := by
    intro q hq g
    rw [hexC, LinearMap.mem_ker, map_smul]
    exact smul_stalk_eq_zero_of_idealPowerMultiple_eq_bot I _ (hcokn l) y hq _
  -- the stalks of `ℱ_n` are killed by `ℐ_y^{n+1}`
  have := hqc _ (inferInstance : (F.obj.obj (op n)).IsCoherent)
  have hFn : ∀ x : S.obj (F.obj.obj (op n)), ∀ r ∈ J ^ (n + 1), r • x = 0 := fun x r hr =>
    smul_stalk_eq_zero_of_idealPowerMultiple_eq_bot I _ (F.property.2.1 n) y hr x
  -- the stalks of the kernel term are killed by `ℐ_y^a`
  have : ((coherentAdicKernel I σ).obj.obj (op n)).IsCoherent :=
    (coherentAdicKernel I σ).property.1 n
  have := hqc _ (inferInstance : ((coherentAdicKernel I σ).obj.obj (op n)).IsCoherent)
  -- the composite through the stable kernel image
  have hcomp : kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hnl).op =
      ((factorThruImage (kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op) ≫
        cokernel.π (idealPowerMultiple I (n + 1) (stableKernelImage I σ m)).ι) ≫ e.hom) ≫
          (coherentAdicKernelι I σ).hom.app (op n) := by
    calc kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hnl).op
        = (kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op) ≫
            F.obj.map (homOfLE (Nat.le_add_right n c)).op := by
          rw [Category.assoc, ← F.obj.map_comp]
          rfl
      _ = (factorThruImage (kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op) ≫
            stableKernelImageIncl I σ m) ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op :=
          congrArg (· ≫ F.obj.map (homOfLE (Nat.le_add_right n c)).op)
            (image.fac (kernel.ι (σ.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op)).symm
      _ = _ := (Category.assoc _ _ _).trans
          ((congrArg (factorThruImage (kernel.ι (σ.hom.app (op l)) ≫
            F.obj.map (homOfLE hml).op) ≫ ·) he.symm).trans
            ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).symm)
  -- reduce to products `p * q`
  have hann : ∀ p ∈ J ^ a, ∀ q ∈ J ^ b, (p * q) • w = 0 := by
    intro p hp q hq
    -- lift `w` to level `l`
    obtain ⟨w', hw'⟩ := (stalk_transition_surjective_and_ker_le F y hnl).1 w
    have hσw' : (S.map (σ.hom.app (op l))).hom w' ∈
        J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y) (S.obj (G.obj.obj (op l)))) := by
      refine (stalk_transition_surjective_and_ker_le G y hnl).2 ?_
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← S.map_comp,
        ← σ.hom.naturality, S.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply, hw', hσw]
    -- `q σ_l(w') = σ_l(f)` with `f ∈ ℐ_y^{n+1} ℱ_{l,y}`
    have hq' : J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk y) (S.obj (G.obj.obj (op l)))) ≤
        (Submodule.map (S.map (σ.hom.app (op l))).hom (J ^ (n + 1) • ⊤)).comap
          (LinearMap.lsmul (X.presheaf.stalk y) _ q) := by
      rw [Submodule.smul_le]
      intro r hr g _
      obtain ⟨f0, hf0⟩ := hJb q hq g
      refine ⟨r • f0, Submodule.smul_mem_smul hr Submodule.mem_top, ?_⟩
      rw [map_smul, hf0, LinearMap.lsmul_apply, smul_comm]
    obtain ⟨f, hf, hfe⟩ := hq' hσw'
    rw [LinearMap.lsmul_apply] at hfe
    -- `q w' - f` lies in the kernel of `σ_l`
    have hz : q • w' - f ∈ LinearMap.ker (S.map (σ.hom.app (op l))).hom := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hfe, sub_self]
    rw [← hexK] at hz
    obtain ⟨u', hu'⟩ := hz
    -- the image of `f` in `ℱ_{n,y}` vanishes
    have hf0 : (S.map (F.obj.map (homOfLE hnl).op)).hom f = 0 := by
      have hmap := Submodule.mem_map_of_mem (f := (S.map (F.obj.map (homOfLE hnl).op)).hom) hf
      rw [Submodule.map_smul''] at hmap
      have hbot : J ^ (n + 1) • Submodule.map (S.map (F.obj.map (homOfLE hnl).op)).hom
          (⊤ : Submodule (X.presheaf.stalk y) (S.obj (F.obj.obj (op l)))) = ⊥ := by
        rw [eq_bot_iff, Submodule.smul_le]
        intro r hr x _
        rw [Submodule.mem_bot]
        exact hFn x r hr
      rw [hbot] at hmap
      exact hmap
    -- so `q w` comes from the kernel term
    have hev := congrArg (fun g => (S.map g).hom u') hcomp
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hev
    have hqw : q • w = (S.map (F.obj.map (homOfLE hnl).op)).hom
        ((S.map (kernel.ι (σ.hom.app (op l)))).hom u') := by
      rw [hu', map_sub, map_smul, hw', hf0, sub_zero]
    rw [mul_smul, hqw, hev, ← map_smul,
      smul_stalk_eq_zero_of_idealPowerMultiple_eq_bot I _ (hKn n) y hp _, map_zero]
  -- conclude for `s ∈ ℐ_y^{a+b} = ℐ_y^a ℐ_y^b`
  have hle : J ^ (a + b) ≤ LinearMap.ker (LinearMap.toSpanSingleton (X.presheaf.stalk y) _ w) := by
    rw [pow_add, Submodule.mul_le]
    intro p hp q hq
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact hann p hp q hq
  have := hle hs
  rwa [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply] at this

end Stacks.Coherent

end
