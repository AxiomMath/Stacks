module

public import StacksFrontier.RingTheory.Flat.DirectLimit

/-!
# The colimit of a semilinear system of modules, and its flatness

Let `{R_i, φ_{ii'}}` be a directed system of commutative rings with colimit `R = colim_i R_i`,
and let `{M_i, f_{ii'}}` be a directed system of abelian groups in which each `M_i` is an
`R_i`-module and each `f_{ii'}` is `φ_{ii'}`-semilinear. The colimit `M = colim_i M_i` of the
abelian groups (the quotient `_root_.DirectLimit M f` of `Σ i, M i`) carries a unique
`R`-module structure for which every canonical map `M_i → M` is semilinear along `R_i → R`.

We construct this `R`-module structure, identify `M` (as an `R`-module, compatibly with the
canonical maps) with the auxiliary module `ColimitModule M f = colim_i (R ⊗_{R_i} M_i)`, and
deduce Stacks 05UU: part (1), and part (2) for `M = colim_i M_i` itself.

## Main definitions

* `StacksColimitRingsFlat.moduleDirectLimit`: the `R`-module structure on `colim_i M_i`.
* `StacksColimitRingsFlat.directLimitOf`: the semilinear canonical map `M_i → colim_i M_i`.
* `StacksColimitRingsFlat.directLimitEquivColimitModule`: the `R`-linear isomorphism
  `colim_i M_i ≃ colim_i (R ⊗_{R_i} M_i)` sending `x ∈ M_i` to `1 ⊗ x`.

## Main results

* `StacksColimitRingsFlat.moduleDirectLimit_unique`: the `R`-module structure is unique.
* `StacksColimitRingsFlat.flat_directLimit_of_flat`: if each `M_i` is `R_i`-flat then
  `colim_i M_i` is `R`-flat.
* `StacksColimitRingsFlat.flat_colimit`: both parts of Stacks 05UU.
-/

@[expose] public section

namespace StacksColimitRingsFlat

open TensorProduct

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable {G : ι → Type*} [(i : ι) → CommRing (G i)]
variable {φ : (i j : ι) → i ≤ j → G i →+* G j}
variable [DirectedSystem G (fun i j h => (φ i j h : G i → G j))]
variable (M : ι → Type*) [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module (G i) (M i)]
variable (f : (i j : ι) → (h : i ≤ j) → M i →ₛₗ[φ i j h] M j)
variable [DirectedSystem M (fun i j h => (f i j h : M i → M j))]

/-- The scalar action of `R = colim_i R_i` on `colim_i M_i`: on representatives at a common
index `i`, `[a] • [x] = [a • x]`. -/
noncomputable instance smulDirectLimit :
    SMul (ColimitRing G φ) (_root_.DirectLimit M f) where
  smul r d := _root_.DirectLimit.map₂ φ f f (fun _ a x => a • x)
    (fun i j h a x => map_smulₛₗ (f i j h) a x) (Ring.DirectLimit.ringEquiv G φ r) d

/-- The defining formula of the action: `[a] • [x] = [a • x]` for `a ∈ R_i`, `x ∈ M_i`. -/
theorem structHom_smul_mk (i : ι) (a : G i) (x : M i) :
    structHom G φ i a • (⟦⟨i, x⟩⟧ : _root_.DirectLimit M f) = ⟦⟨i, a • x⟩⟧ := by
  change _root_.DirectLimit.map₂ φ f f (fun i a x => a • x) _
      (Ring.DirectLimit.ringEquiv G φ (Ring.DirectLimit.of _ _ i a)) _ = _
  rw [Ring.DirectLimit.ringEquiv_of, _root_.DirectLimit.map₂_def]

omit [DirectedSystem G (fun i j h => (φ i j h : G i → G j))] in
/-- Any two elements of `R` and two elements of `colim_i M_i` come from a common index. -/
theorem exists_common_index (r s : ColimitRing G φ) (d e : _root_.DirectLimit M f) :
    ∃ (i : ι) (a b : G i) (x y : M i), r = structHom G φ i a ∧ s = structHom G φ i b ∧
      d = ⟦⟨i, x⟩⟧ ∧ e = ⟦⟨i, y⟩⟧ := by
  obtain ⟨i₁, a, rfl⟩ := Ring.DirectLimit.exists_of r
  obtain ⟨i₂, b, rfl⟩ := Ring.DirectLimit.exists_of s
  obtain ⟨i₃, x, rfl⟩ := _root_.DirectLimit.exists_eq_mk _ d
  obtain ⟨i₄, y, rfl⟩ := _root_.DirectLimit.exists_eq_mk _ e
  obtain ⟨k₁, h₁, h₂⟩ := exists_ge_ge i₁ i₂
  obtain ⟨k₂, h₃, h₄⟩ := exists_ge_ge i₃ i₄
  obtain ⟨k, hk₁, hk₂⟩ := exists_ge_ge k₁ k₂
  refine ⟨k, φ i₁ k (h₁.trans hk₁) a, φ i₂ k (h₂.trans hk₁) b, f i₃ k (h₃.trans hk₂) x,
    f i₄ k (h₄.trans hk₂) y, (algebraMap_structHom_comp G φ _ _ _ a).symm,
    (algebraMap_structHom_comp G φ _ _ _ b).symm, ?_, ?_⟩
  · exact (_root_.DirectLimit.mk_apply (f := f) i₃ k x _).symm
  · exact (_root_.DirectLimit.mk_apply (f := f) i₄ k y _).symm

/-- The `R`-module structure on the abelian group `colim_i M_i`, for which every canonical map
`M_i → colim_i M_i` is semilinear along `R_i → R` (`structHom_smul_mk`). -/
noncomputable instance moduleDirectLimit :
    Module (ColimitRing G φ) (_root_.DirectLimit M f) where
  one_smul d := by
    obtain ⟨i, _, _, x, _, -, -, rfl, -⟩ := exists_common_index M f 1 1 d d
    rw [← map_one (structHom G φ i), structHom_smul_mk, one_smul]
  mul_smul r s d := by
    obtain ⟨i, a, b, x, _, rfl, rfl, rfl, -⟩ := exists_common_index M f r s d d
    rw [← map_mul, structHom_smul_mk, structHom_smul_mk, structHom_smul_mk, mul_smul]
  smul_zero r := by
    obtain ⟨i, a, _, _, _, rfl, -, -, -⟩ := exists_common_index M f r r 0 0
    rw [_root_.DirectLimit.zero_def i, structHom_smul_mk, smul_zero]
  smul_add r d e := by
    obtain ⟨i, a, _, x, y, rfl, -, rfl, rfl⟩ := exists_common_index M f r r d e
    rw [_root_.DirectLimit.add_def, structHom_smul_mk, structHom_smul_mk, structHom_smul_mk,
      _root_.DirectLimit.add_def, smul_add]
  add_smul r s d := by
    obtain ⟨i, a, b, x, _, rfl, rfl, rfl, -⟩ := exists_common_index M f r s d d
    rw [← map_add, structHom_smul_mk, structHom_smul_mk, structHom_smul_mk,
      _root_.DirectLimit.add_def, add_smul]
  zero_smul d := by
    obtain ⟨i, _, _, x, _, -, -, rfl, -⟩ := exists_common_index M f 0 0 d d
    rw [← map_zero (structHom G φ i), structHom_smul_mk, zero_smul]
    exact (_root_.DirectLimit.zero_def i).symm

/-- The `R`-module structure `moduleDirectLimit` is the only one on `colim_i M_i` for which
the canonical maps `M_i → colim_i M_i` are semilinear along `R_i → R`. -/
theorem moduleDirectLimit_unique (inst : Module (ColimitRing G φ) (_root_.DirectLimit M f))
    (h : ∀ (i : ι) (a : G i) (x : M i),
      inst.smul (structHom G φ i a) (⟦⟨i, x⟩⟧ : _root_.DirectLimit M f) = ⟦⟨i, a • x⟩⟧) :
    inst = moduleDirectLimit M f := by
  ext r d
  obtain ⟨i, a, _, x, _, rfl, -, rfl, -⟩ := exists_common_index M f r r d d
  exact (h i a x).trans (structHom_smul_mk M f i a x).symm

/-- The canonical map `M_i → colim_i M_i`, semilinear along the structure map `R_i → R`. -/
noncomputable def directLimitOf (i : ι) :
    M i →ₛₗ[structHom G φ i] _root_.DirectLimit M f where
  toFun x := ⟦⟨i, x⟩⟧
  map_add' _ _ := (_root_.DirectLimit.add_def _ _ _).symm
  map_smul' a x := (structHom_smul_mk M f i a x).symm

/-- The canonical maps `M_i → colim_i M_i` are compatible with the transition maps. -/
theorem directLimitOf_comp (i j : ι) (h : i ≤ j) (x : M i) :
    directLimitOf M f j (f i j h x) = directLimitOf M f i x :=
  _root_.DirectLimit.mk_apply (f := f) i j x h

/-- The biadditive map `R × M_i → colim_i M_i`, `(r, x) ↦ r • [x]`. -/
noncomputable def smulOfAddHom (i : ι) :
    ColimitRing G φ →+ M i →+ _root_.DirectLimit M f :=
  AddMonoidHom.mk' (fun r => (DistribSMul.toAddMonoidHom _ r).comp
      (directLimitOf M f i).toAddMonoidHom)
    (fun r s => by ext x; simp [add_smul])

theorem smulOfAddHom_balanced (i : ι) (a : G i) (r : ColimitRing G φ) (x : M i) :
    smulOfAddHom M f i (a • r) x = smulOfAddHom M f i r (a • x) := by
  change (a • r) • directLimitOf M f i x = r • directLimitOf M f i (a • x)
  rw [map_smulₛₗ, Algebra.smul_def, mul_comm, mul_smul]
  rfl

/-- The `R`-linear map `R ⊗_{R_i} M_i → colim_i M_i`, `r ⊗ x ↦ r • [x]`. -/
noncomputable def baseChangeToDirectLimit (i : ι) :
    TensorProduct (G i) (ColimitRing G φ) (M i) →ₗ[ColimitRing G φ] _root_.DirectLimit M f where
  toFun := TensorProduct.liftAddHom (smulOfAddHom M f i) (smulOfAddHom_balanced M f i)
  map_add' := map_add _
  map_smul' s t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [TensorProduct.smul_tmul', TensorProduct.liftAddHom_tmul,
        TensorProduct.liftAddHom_tmul, RingHom.id_apply]
      change (s • r) • directLimitOf M f i x = s • r • directLimitOf M f i x
      rw [smul_eq_mul, mul_smul]
    | add t u ht hu => rw [smul_add, map_add, map_add, ht, hu, smul_add]

theorem baseChangeToDirectLimit_tmul (i : ι) (r : ColimitRing G φ) (x : M i) :
    baseChangeToDirectLimit M f i (r ⊗ₜ[G i] x) = r • directLimitOf M f i x := by
  change TensorProduct.liftAddHom (smulOfAddHom M f i) (smulOfAddHom_balanced M f i)
    (r ⊗ₜ[G i] x) = _
  rw [TensorProduct.liftAddHom_tmul]
  rfl

section Equiv

variable [DecidableEq ι]

/-- The comparison map `colim_i M_i → ColimitModule M f`, induced by the cocone maps
`colimitStructMap`. -/
noncomputable def directLimitToColimitModule :
    _root_.DirectLimit M f →ₗ[ColimitRing G φ] ColimitModule M f where
  toFun := _root_.DirectLimit.lift _ (fun i x => colimitStructMap M f i x)
    (fun i j h x => (colimitStructMap_comp M f i j h x).symm)
  map_add' d e := by
    induction d, e using _root_.DirectLimit.induction₂ with
    | ih i x y =>
      rw [_root_.DirectLimit.add_def, _root_.DirectLimit.lift_def, _root_.DirectLimit.lift_def,
        _root_.DirectLimit.lift_def, map_add]
  map_smul' r d := by
    obtain ⟨i, a, _, x, _, rfl, -, rfl, -⟩ := exists_common_index M f r r d d
    rw [structHom_smul_mk, _root_.DirectLimit.lift_def, _root_.DirectLimit.lift_def,
      RingHom.id_apply]
    exact map_smulₛₗ (colimitStructMap M f i) a x

/-- The inverse comparison map `ColimitModule M f → colim_i M_i`. -/
noncomputable def colimitModuleToDirectLimit :
    ColimitModule M f →ₗ[ColimitRing G φ] _root_.DirectLimit M f :=
  Module.DirectLimit.lift (ColimitRing G φ) ι (baseChangedModule M) (baseChangeMap M f)
    (baseChangeToDirectLimit M f) (fun i j h t => by
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul r x =>
        have hrx : r ⊗ₜ[G i] x = r • (1 : ColimitRing G φ) ⊗ₜ[G i] x := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [hrx, map_smul, map_smul, baseChangeMap_one_tmul, map_smul,
          baseChangeToDirectLimit_tmul, baseChangeToDirectLimit_tmul, one_smul, one_smul,
          directLimitOf_comp]
      | add t u ht hu => rw [map_add, map_add, ht, hu, map_add])

theorem colimitModuleToDirectLimit_of (i : ι) (t : baseChangedModule M i) :
    colimitModuleToDirectLimit M f
        (Module.DirectLimit.of (ColimitRing G φ) ι (baseChangedModule M) (baseChangeMap M f) i t)
      = baseChangeToDirectLimit M f i t :=
  Module.DirectLimit.lift_of _ _ _

/-- **`ColimitModule M f` is the colimit of the `M_i`.** The `R`-linear isomorphism
`colim_i M_i ≃ colim_i (R ⊗_{R_i} M_i)` between the colimit of the abelian groups `M_i` (with
its `R`-module structure `moduleDirectLimit`) and `ColimitModule M f`; it sends the class of
`x ∈ M_i` to `colimitStructMap M f i x`, the class of `1 ⊗ x`. -/
noncomputable def directLimitEquivColimitModule :
    _root_.DirectLimit M f ≃ₗ[ColimitRing G φ] ColimitModule M f :=
  LinearEquiv.ofLinearMap (directLimitToColimitModule M f) (colimitModuleToDirectLimit M f)
    (by
      apply LinearMap.ext
      intro z
      induction z using Module.DirectLimit.induction_on with
      | ih i t =>
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul r x =>
          have hrx : r ⊗ₜ[G i] x = r • (1 : ColimitRing G φ) ⊗ₜ[G i] x := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [hrx, map_smul, LinearMap.comp_apply, map_smul, map_smul, LinearMap.id_apply,
            colimitModuleToDirectLimit_of, baseChangeToDirectLimit_tmul, one_smul]
          rfl
        | add t u ht hu =>
          rw [map_add, map_add, ht, hu, map_add])
    (by
      apply LinearMap.ext
      intro d
      induction d using _root_.DirectLimit.induction with
      | ih i x =>
        rw [LinearMap.comp_apply, LinearMap.id_apply]
        change colimitModuleToDirectLimit M f (Module.DirectLimit.of (ColimitRing G φ) ι
          (baseChangedModule M) (baseChangeMap M f) i ((1 : ColimitRing G φ) ⊗ₜ[G i] x)) = _
        rw [colimitModuleToDirectLimit_of, baseChangeToDirectLimit_tmul, one_smul]
        rfl)

theorem directLimitEquivColimitModule_apply (i : ι) (x : M i) :
    directLimitEquivColimitModule M f (directLimitOf M f i x) = colimitStructMap M f i x :=
  rfl

end Equiv

/-- Stacks 05UU (2): if each `M_i` is a flat `R_i`-module, then `M = colim_i M_i` is a flat
`R`-module. -/
theorem flat_directLimit_of_flat (hflat : ∀ i : ι, Module.Flat (G i) (M i)) :
    Module.Flat (ColimitRing G φ) (_root_.DirectLimit M f) := by
  classical
  have := colimitModule_flat G φ M hflat f
    (fun i x => DirectedSystem.map_self' f x)
    (fun i j k hij hjk x => DirectedSystem.map_map' f hij hjk x)
  exact Module.Flat.of_linearEquiv (directLimitEquivColimitModule M f)

/-- Let `{R_i, φ_{ii'}}` be a system of rings over the directed set `ι`, with colimit
`R = colim_i R_i`.

1. If `N` is an `R`-module which is flat as an `R_i`-module (via `R_i → R`) for all `i`, then
   `N` is flat as an `R`-module.
2. If each `M_i` is a flat `R_i`-module and the `f_{ii'} : M_i → M_{i'}` are
   `φ_{ii'}`-semilinear maps forming a system, then `M = colim_i M_i` (the colimit of the
   abelian groups, with its `R`-module structure `moduleDirectLimit`) is a flat `R`-module. -/
@[stacks 05UU]
theorem flat_colimit :
    (∀ (N : Type*) [AddCommGroup N] [Module (ColimitRing G φ) N],
      (∀ i : ι, @Module.Flat (G i) N _ _ (Module.compHom N (structHom G φ i))) →
        Module.Flat (ColimitRing G φ) N) ∧
    ((∀ i : ι, Module.Flat (G i) (M i)) →
      Module.Flat (ColimitRing G φ) (_root_.DirectLimit M f)) :=
  ⟨fun N _ _ hN => flat_of_forall_flat G φ N hN, flat_directLimit_of_flat M f⟩

end StacksColimitRingsFlat
