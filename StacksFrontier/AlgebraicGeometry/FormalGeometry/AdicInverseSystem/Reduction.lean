module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.Sections
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.RingTheory.AdicCompletion.InverseLimit
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksCore.Tactic.StacksAttribute

/-!
# Reduction of the limit of an adic inverse system modulo powers of the ideal

Let `X` be a scheme, `I` a quasi-coherent ideal sheaf of finite type on `X` and `(F_n)` an adic
inverse system of quasi-coherent modules, so that `F_n = F_{n+1} / I^{n+1} F_{n+1}`. This file
shows that the inverse limit `F = lim F_n` recovers the system: the limit projection
`F ⟶ F_n` is surjective with kernel `I^{n+1} F`, so that `F / I^{n+1} F ≅ F_n`.

## Main results

* `Stacks.Algebraization.AdicInverseSystem.surjective_limitProjection_app` — the limit projection
  is surjective on the sections over an affine open.
* `Stacks.Algebraization.AdicInverseSystem.epi_limitProjection` — the limit projection is an
  epimorphism.
* `Stacks.Algebraization.AdicInverseSystem.pow_smul_sections_eq_bot` — `I^(k+1)` annihilates
  the sections of `F_k` over an affine open.
* `Stacks.Algebraization.AdicInverseSystem.idealPowerMultiple_limitModule_eq_kernel` — the
  subsheaf `I^{n+1} F` of the limit is the kernel of the `n`-th limit projection.
* `Stacks.Algebraization.AdicInverseSystem.exists_idealPowerQuotientIso` — reduction of the limit
  modulo `I^{n+1}` is the `n`-th term of the system, compatibly with the limit projection.

## References

* [Stacks Project, Tag 0EI8](https://stacks.math.columbia.edu/tag/0EI8)
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### The scalar action on sections -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf
  sectionsModuleRingCatSheaf

namespace AdicInverseSystem

variable (S : AdicInverseSystem.{u})

/-! ### The tower of affine sections -/

/-- The tower of `Γ(X, U)`-modules attached to an adic inverse system over an affine open `U`:
the zero module in degree `0`, and the sections of `F_k` in degree `k + 1`. -/
private noncomputable def sectionTower (U : S.X.affineOpens) : ℕ → Type u :=
  Nat.rec (Fin 0 → Γ(S.X, U.1)) (fun k _ => Γ(S.system.obj (op k), U.1))

private instance sectionTowerAddCommGroup (U : S.X.affineOpens) (k : ℕ) :
    AddCommGroup (S.sectionTower U k) := by
  cases k with
  | zero => change AddCommGroup (Fin 0 → Γ(S.X, U.1)); infer_instance
  | succ k => change AddCommGroup Γ(S.system.obj (op k), U.1); infer_instance

private instance sectionTowerModule (U : S.X.affineOpens) (k : ℕ) :
    Module Γ(S.X, U.1) (S.sectionTower U k) := by
  cases k with
  | zero => change Module Γ(S.X, U.1) (Fin 0 → Γ(S.X, U.1)); infer_instance
  | succ k => change Module Γ(S.X, U.1) Γ(S.system.obj (op k), U.1); infer_instance

/-- The transition maps of the tower of affine sections: the quotient map by the corresponding
power of the ideal, transported along `sectionsQuotientEquiv`. -/
private noncomputable def sectionTransition (U : S.X.affineOpens) (k : ℕ) :
    S.sectionTower U (k + 1) →ₗ[Γ(S.X, U.1)] S.sectionTower U k :=
  match k with
  | 0 => 0
  | k + 1 =>
      (Classical.choose (S.sectionsQuotientEquiv U k)).toLinearMap.comp
        (Submodule.mkQ (S.I.ideal U ^ (k + 1) •
          (⊤ : Submodule Γ(S.X, U.1) Γ(S.system.obj (op (k + 1)), U.1))))

/-- The tower of affine sections of an adic inverse system, as an inverse system of modules in
the sense of Stacks 09B8: the transitions are surjective with kernel the ideal power. -/
private noncomputable def sectionInverseSystem (U : S.X.affineOpens) :
    Stacks.AdicCompletion.InverseLimit.InverseSystem (S.I.ideal U) where
  M := S.sectionTower U
  π := S.sectionTransition U
  surjective := by
    intro k
    cases k with
    | zero =>
      intro x
      exact ⟨0, funext fun i => Fin.elim0 i⟩
    | succ k =>
      intro y
      obtain ⟨q, hq⟩ := (Classical.choose (S.sectionsQuotientEquiv U k)).surjective y
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ q
      exact ⟨x, show Classical.choose (S.sectionsQuotientEquiv U k)
        (Submodule.Quotient.mk x) = y from hx ▸ hq⟩
  ker_π := by
    intro k
    cases k with
    | zero =>
      apply Submodule.ext
      intro x
      simp [sectionTransition]
    | succ k =>
      let e := Classical.choose (S.sectionsQuotientEquiv U k)
      apply Submodule.ext
      intro x
      change Γ(S.system.obj (op (k + 1)), U.1) at x
      constructor
      · intro hx
        change e (Submodule.Quotient.mk x) = 0 at hx
        exact (Submodule.Quotient.mk_eq_zero _).mp (e.map_eq_zero_iff.mp hx)
      · intro hx
        change e (Submodule.Quotient.mk x) = 0
        exact e.map_eq_zero_iff.mpr ((Submodule.Quotient.mk_eq_zero _).2 hx)

/-- The transition maps of the tower of affine sections are the restriction maps of the system. -/
private theorem sectionTransition_succ_apply (U : S.X.affineOpens) (n : ℕ)
    (y : Γ(S.system.obj (op (n + 1)), U.1)) :
    S.sectionTransition U (n + 1) y =
      ((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom y :=
  Classical.choose_spec (S.sectionsQuotientEquiv U n) y

/-- A compatible family in the limit of the tower of affine sections is compatible with the
transition maps of the system itself. -/
private theorem sectionTower_transition_apply (U : S.X.affineOpens)
    (x : (S.sectionInverseSystem U).limit) {m n : ℕ} (h : m ≤ n) :
    ((S.system.map (homOfLE h).op).app U.1).hom (x.1 (n + 1)) = x.1 (m + 1) := by
  induction n, h using Nat.le_induction with
  | base => simp; rfl
  | succ n h ih =>
      have hfactor : (homOfLE (h.trans n.le_succ)).op =
          (homOfLE (Nat.le_succ n)).op ≫ (homOfLE h).op := Subsingleton.elim _ _
      have hstep : ((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom
          (x.1 (n + 2)) = x.1 (n + 1) := by
        exact (S.sectionTransition_succ_apply U n _).symm.trans (x.2 (n + 1))
      rw [hfactor, Functor.map_comp, Scheme.Modules.Hom.comp_app]
      change ((S.system.map (homOfLE h).op).app U.1).hom
        (((S.system.map (homOfLE (Nat.le_succ n)).op).app U.1).hom (x.1 (n + 2))) = _
      rwa [hstep]

/-- Evaluation of a sheaf of modules at an affine open, valued in `Γ(X, U)`-modules. -/
private noncomputable def sectionFunctor (U : S.X.affineOpens) :
    S.X.Modules ⥤ ModuleCat Γ(S.X, U.1) :=
  SheafOfModules.evaluation S.X.ringCatSheaf (op U.1) ⋙
    ModuleCat.restrictScalars (RingHom.id Γ(S.X, U.1))

private theorem sectionFunctor_preservesLimit (U : S.X.affineOpens) :
    PreservesLimit S.system (S.sectionFunctor U) := by
  have hEval : PreservesLimit S.system
      (SheafOfModules.evaluation S.X.ringCatSheaf (op U.1)) :=
    SheafOfModules.evaluationPreservesLimit S.system (op U.1)
  refine (preservesLimit_iff_of_natIso S.system ?_).mp hEval
  exact Functor.isoWhiskerLeft (SheafOfModules.evaluation S.X.ringCatSheaf (op U.1))
    (ModuleCat.restrictScalarsId (Γ(S.X, U.1))).symm

/-- The limit of the tower of affine sections, as a cone over the sections of the system. -/
private noncomputable def sectionLimitCone (U : S.X.affineOpens) :
    Cone (S.system ⋙ S.sectionFunctor U) where
  pt := ModuleCat.of Γ(S.X, U.1) (S.sectionInverseSystem U).limit
  π :=
    { app := fun j => by
        letI : Module Γ(S.X, U.1)
            ((SheafOfModules.evaluation S.X.ringCatSheaf (op U.1)).obj (S.system.obj j)) := by
          change Module Γ(S.X, U.1) Γ(S.system.obj j, U.1)
          exact S.sectionTowerModule U (j.unop + 1)
        exact ModuleCat.ofHom ((S.sectionInverseSystem U).proj (j.unop + 1))
      naturality := by
        intro i j g
        ext x
        cases i with
        | op i =>
          cases j with
          | op j =>
            have h : j ≤ i := leOfHom g.unop
            rw [show g = (homOfLE h).op from Subsingleton.elim _ _]
            change (S.sectionInverseSystem U).proj (j + 1) x =
              ((S.system.map (homOfLE h).op).app U.1).hom
                ((S.sectionInverseSystem U).proj (i + 1) x)
            exact (S.sectionTower_transition_apply U x h).symm }

private noncomputable def sectionLimitCone_isLimit (U : S.X.affineOpens) :
    IsLimit (S.sectionLimitCone U) := by
  refine IsLimit.mk (fun c => ?_) ?_ ?_
  · let F := S.sectionInverseSystem U
    have hmem : ∀ x : c.pt, (fun k => Nat.casesOn k (0 : F.M 0)
        (fun m => (c.π.app (op m)).hom x)) ∈ F.limit := by
      intro x k
      cases k with
      | zero => rfl
      | succ m =>
        have h := congrArg (fun q => q.hom x) (c.w (homOfLE (Nat.le_succ m)).op)
        simp only [ModuleCat.comp_apply] at h
        change ((S.system.map (homOfLE (Nat.le_succ m)).op).app U.1).hom
            ((c.π.app (op (m + 1))).hom x) = (c.π.app (op m)).hom x at h
        exact (S.sectionTransition_succ_apply U m _).trans h
    exact ModuleCat.ofHom
      { toFun := fun x => ⟨_, hmem x⟩
        map_add' := fun x y => Subtype.ext (funext fun k => by
          simp only [Submodule.coe_add, Pi.add_apply]
          cases k with
          | zero => exact funext fun i => Fin.elim0 i
          | succ m => exact map_add ((c.π.app (op m)).hom) x y)
        map_smul' := fun a x => Subtype.ext (funext fun k => by
          simp only [Submodule.coe_smul, Pi.smul_apply]
          cases k with
          | zero => exact funext fun i => Fin.elim0 i
          | succ m => exact map_smul ((c.π.app (op m)).hom) a x) }
  · intro c j
    ext x
    cases j with
    | op j => rfl
  · intro c m hm
    ext x
    refine Subtype.ext (funext fun k => ?_)
    cases k with
    | zero => exact funext fun i => Fin.elim0 i
    | succ n => exact congrArg (fun q => q.hom x) (hm (op n))

/-- The limit of the tower of affine sections is the sections of the limit. -/
private noncomputable def sectionLimitIso (U : S.X.affineOpens) :
    ModuleCat.of Γ(S.X, U.1) (S.sectionInverseSystem U).limit ≅
      (S.sectionFunctor U).obj S.limitModule := by
  have : PreservesLimit S.system (S.sectionFunctor U) := S.sectionFunctor_preservesLimit U
  exact (IsLimit.conePointUniqueUpToIso (S.sectionLimitCone_isLimit U)
    (limit.isLimit (S.system ⋙ S.sectionFunctor U))).trans
      (preservesLimitIso (S.sectionFunctor U) S.system).symm

private theorem sectionLimitIso_hom_proj (U : S.X.affineOpens) (n : ℕ) :
    (S.sectionLimitIso U).hom ≫ (S.sectionFunctor U).map (limit.π S.system (op n)) =
      (S.sectionLimitCone U).π.app (op n) := by
  have : PreservesLimit S.system (S.sectionFunctor U) := S.sectionFunctor_preservesLimit U
  set D := S.system ⋙ S.sectionFunctor U with hD
  set p := preservesLimitIso (S.sectionFunctor U) S.system with hp
  set i := IsLimit.conePointUniqueUpToIso (S.sectionLimitCone_isLimit U) (limit.isLimit D)
    with hi
  change (i.hom ≫ p.symm.hom) ≫ (S.sectionFunctor U).map (limit.π S.system (op n)) = _
  have hpπ : p.hom ≫ limit.π D (op n) =
      (S.sectionFunctor U).map (limit.π S.system (op n)) :=
    preservesLimitIso_hom_π (S.sectionFunctor U) S.system (op n)
  rw [← hpπ, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ _

private theorem sectionLimitIso_hom_proj_apply (U : S.X.affineOpens) (n : ℕ)
    (z : (S.sectionInverseSystem U).limit) :
    ((limit.π S.system (op n)).app U.1).hom ((S.sectionLimitIso U).hom.hom z) =
      (S.sectionInverseSystem U).proj (n + 1) z :=
  congrArg (fun q => q.hom z) (S.sectionLimitIso_hom_proj U n)

/-! ### Surjectivity of the limit projections -/

/-- The `n`-th limit projection of an adic inverse system is surjective on the sections over an
affine open. -/
public theorem surjective_limitProjection_app (U : S.X.affineOpens) (n : ℕ) :
    Function.Surjective (((limit.π S.system (op n)).app U.1).hom) := by
  intro y
  obtain ⟨z, hz⟩ := (S.sectionInverseSystem U).proj_surjective (n + 1) y
  exact ⟨(S.sectionLimitIso U).hom.hom z,
    (S.sectionLimitIso_hom_proj_apply U n z).trans hz⟩

/-- The `n`-th limit projection of an adic inverse system is an epimorphism. -/
public theorem epi_limitProjection (n : ℕ) : Epi (limit.π S.system (op n)) := by
  set F := SheafOfModules.toSheaf S.X.ringCatSheaf with hF
  set φ := F.map (limit.π S.system (op n)) with hφ
  have : Sheaf.IsLocallySurjective φ := by
    constructor
    intro W s
    set R : Presieve W := fun V _ => ∃ A : S.X.affineOpens,
      V = (A : S.X.Opens) ∧ (A : S.X.Opens) ≤ W with hR
    have hcov : Sieve.generate R ∈ Opens.grothendieckTopology S.X W := by
      intro x hx
      obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAW⟩ :=
        S.X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
      exact ⟨(A : S.X.Opens), homOfLE hAW,
        ⟨(A : S.X.Opens), 𝟙 _, homOfLE hAW, ⟨⟨A, hA⟩, rfl, hAW⟩, by simp⟩, hxA⟩
    refine (Opens.grothendieckTopology S.X).superset_covering
      ((Sieve.generate_le_iff R (Presheaf.imageSieve φ.hom s)).2 ?_) hcov
    rintro V i ⟨A, rfl, hAW⟩
    obtain ⟨x, hx⟩ := S.surjective_limitProjection_app A n
      ((S.system.obj (op n)).val.presheaf.map (homOfLE hAW).op s)
    rw [show i = homOfLE hAW from Subsingleton.elim _ _]
    exact ⟨x, hx⟩
  have hEpi : Epi φ := Sheaf.epi_of_isLocallySurjective φ
  refine ⟨fun {T} g₁ g₂ hgh => ?_⟩
  have hgh' : F.map g₁ = F.map g₂ := by
    refine (cancel_epi φ).1 ?_
    have hmap : F.map (limit.π S.system (op n)) ≫ F.map g₁ =
        F.map (limit.π S.system (op n)) ≫ F.map g₂ :=
      (F.map_comp _ _).symm.trans ((congrArg F.map hgh).trans (F.map_comp _ _))
    simpa [hφ] using hmap
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  have hpoint := congrArg (fun q => q.hom.app U) hgh'
  exact ConcreteCategory.congr_hom hpoint x

/-! ### The kernel of the limit projection -/

/-- The ideal power `I^(k+1)` annihilates the sections of `F_k` over an affine open. -/
public theorem pow_smul_sections_eq_bot (U : S.X.affineOpens) (k : ℕ) :
    (S.I.ideal U) ^ (k + 1) •
      (⊤ : Submodule Γ(S.X, U.1) Γ(S.system.obj (op k), U.1)) = ⊥ := by
  obtain ⟨e, -⟩ := S.sectionsQuotientEquiv U k
  refine le_antisymm (Submodule.smul_le.2 fun a ha x _ => ?_) bot_le
  obtain ⟨q, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hmk : (Submodule.Quotient.mk (a • y) : _ ⧸ (S.I.ideal U ^ (k + 1) •
      (⊤ : Submodule Γ(S.X, U.1) Γ(S.system.obj (op (k + 1)), U.1)))) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
  refine (Submodule.mem_bot _).2 ?_
  rw [← map_smul, ← Submodule.Quotient.mk_smul, hmk, map_zero]

/-- A linear map sends `I • ⊤` into `I • ⊤`. -/
private theorem map_mem_ideal_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (I : Ideal R) (g : M →ₗ[R] N) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : g x ∈ I • (⊤ : Submodule R N) :=
  Submodule.smul_top_le_comap_smul_top I g hx

/-- The subsheaf `I^{n+1} F` of the limit of an adic inverse system is the kernel of the `n`-th
limit projection. -/
public theorem idealPowerMultiple_limitModule_eq_kernel
    (hI : Scheme.IdealSheafData.IsFiniteType S.I) (n : ℕ) :
    idealPowerMultiple S.I (n + 1) S.limitModule =
      kernelSubmodule (limit.π S.system (op n)) := by
  refine le_antisymm ((idealPowerMultiple_le_iff S.I (n + 1) S.limitModule _).2 fun U => ?_)
    (submodule_le_of_affine _ _ fun U => ?_)
  · let g := ((S.sectionFunctor U).map (limit.π S.system (op n))).hom
    intro x hx
    rw [kernelSubmodule_toSubmodule_obj]
    have hpres : g x ∈ (S.I.ideal U) ^ (n + 1) •
        (⊤ : Submodule Γ(S.X, U.1) Γ(S.system.obj (op n), U.1)) :=
      map_mem_ideal_smul_top _ g hx
    rw [S.pow_smul_sections_eq_bot U n] at hpres
    exact hpres
  · intro x hx
    rw [kernelSubmodule_toSubmodule_obj] at hx
    set z : (S.sectionInverseSystem U).limit := (S.sectionLimitIso U).inv.hom x with hz
    have hzx : (S.sectionLimitIso U).hom.hom z = x :=
      ConcreteCategory.congr_hom (S.sectionLimitIso U).inv_hom_id x
    have hzproj : (S.sectionInverseSystem U).proj (n + 1) z = 0 := by
      rwa [← S.sectionLimitIso_hom_proj_apply U n z, hzx]
    have hzmem : z ∈ (S.I.ideal U) ^ (n + 1) •
        (⊤ : Submodule Γ(S.X, U.1) (S.sectionInverseSystem U).limit) := by
      rwa [← (S.sectionInverseSystem U).ker_proj (hI U) (n + 1)]
    have hpres := map_mem_ideal_smul_top _ (S.sectionLimitIso U).hom.hom hzmem
    rw [hzx] at hpres
    exact (idealPowerMultiple_le_iff S.I (n + 1) S.limitModule
      (idealPowerMultiple S.I (n + 1) S.limitModule)).mp le_rfl U hpres

/-- Reduction of the limit of an adic inverse system modulo `I^{n+1}` recovers its `n`-th
(zero-indexed) term, compatibly with the canonical limit projection. -/
@[stacks 0EI8 "reduction"]
public theorem exists_idealPowerQuotientIso
    (hI : Scheme.IdealSheafData.IsFiniteType S.I) (n : ℕ) :
    ∃ e : idealPowerQuotient S.I (n + 1) S.limitModule ≅ S.system.obj (op n),
      cokernel.π ((idealPowerMultiple S.I (n + 1) S.limitModule).ι) ≫ e.hom =
        limit.π S.system (op n) := by
  suffices h : ∀ (P : S.limitModule.Submodule) (f : S.limitModule ⟶ S.system.obj (op n)),
      Epi f → P = kernelSubmodule f →
      ∃ e : cokernel (C := S.X.Modules) P.ι ≅ S.system.obj (op n),
        cokernel.π (C := S.X.Modules) P.ι ≫ e.hom = f from
    h _ (limit.π S.system (op n)) (S.epi_limitProjection n)
      (S.idealPowerMultiple_limitModule_eq_kernel hI n)
  rintro P f hepi rfl
  let Kmod : S.X.Modules := (kernelSubmodule f).toSheafOfModules
  let Kι : Kmod ⟶ S.limitModule := (kernelSubmodule f).ι
  have hlift : (kernelSubmoduleIso f).hom ≫ kernel.ι (C := S.X.Modules) f = Kι :=
    (congrArg (fun g => (kernelSubmoduleIso f).hom ≫ g)
        (kernelSubmoduleCorestrict_comp_ι f).symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ Kι) (kernelSubmoduleIso f).hom_inv_id).trans
          (Category.id_comp _)))
  have hzero : Kι ≫ f = 0 :=
    (congrArg (fun g => g ≫ f) hlift.symm).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun g => (kernelSubmoduleIso f).hom ≫ g)
          (kernel.condition (C := S.X.Modules) f)).trans comp_zero))
  have hker : IsLimit (KernelFork.ofι (f := f) Kι hzero) :=
    IsLimit.ofIsoLimit (kernelIsKernel (C := S.X.Modules) f)
      (Fork.ext (kernelSubmoduleIso f).symm (kernelSubmoduleCorestrict_comp_ι f))
  let C : ShortComplex S.X.Modules := ShortComplex.mk Kι f hzero
  obtain ⟨hcolim⟩ := C.exact_and_epi_g_iff_g_is_cokernel.mp ⟨C.exact_of_f_is_kernel hker, hepi⟩
  exact ⟨IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (C := S.X.Modules) Kι) hcolim,
    IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel (C := S.X.Modules) Kι)
      hcolim WalkingParallelPair.one⟩

end AdicInverseSystem

end Stacks.Algebraization

end

end
