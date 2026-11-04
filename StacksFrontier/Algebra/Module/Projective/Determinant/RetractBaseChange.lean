module

public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.PicardGroup

/-!
# Base change of retracts, and of modules of linear maps with projective source

A retract of a base change is a base change of the corresponding retract. Two instances are
recorded: the kernel of a surjection onto a projective module, and the module of linear maps out
of a finite projective module, which is a retract of the module of linear maps out of a finite
free module, where Mathlib's `IsBaseChange.linearMapLeftRight` applies.

## Main results

* `IsBaseChange.of_retract`: a retract of a base change is a base change.
* `IsBaseChange.linearMapLeftRight_of_projective`: if `M` is finite projective, `P` the base
  change of `M` and `Q` the base change of `N`, then `P →ₗ[S] Q` is the base change of
  `M →ₗ[R] N`.
* `IsBaseChange.ker_restrict`: the kernel of the base change of a surjection onto a projective
  module is the base change of its kernel.
* `Module.Invertible.eq_zero_of_forall_tmul_eq_zero`: tensoring by an invertible module is
  faithful on elements.
-/

@[expose] public noncomputable section

universe u

open TensorProduct

namespace IsBaseChange

variable {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

section Retract

variable {M M' N N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- Evaluating a commuting square of linear maps (with one side `S`-linear) at a point. -/
private theorem apply_eq_of_restrictScalars_comp_eq {A B C D : Type u} [AddCommGroup A]
    [Module R A] [AddCommGroup B] [Module R B] [Module S B] [IsScalarTower R S B]
    [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D] [Module S D]
    [IsScalarTower R S D] {f' : B →ₗ[S] D} {σ : A →ₗ[R] B} {ν : C →ₗ[R] D} {f : A →ₗ[R] C}
    (hc : (f'.restrictScalars R).comp σ = ν.comp f) (x : A) : f' (σ x) = ν (f x) :=
  LinearMap.congr_fun hc x

/-- **A retract of a base change is a base change.** Let `φ : M → N` exhibit `N` as `S ⊗_R M`,
let `i : M' → M`, `p : M → M'` be `R`-linear with `p ∘ i = id`, and `i' : N' → N`,
`p' : N → N'` be `S`-linear with `p' ∘ i' = id`, compatibly with `φ` and `φ' : M' → N'`. Then
`φ'` exhibits `N'` as `S ⊗_R M'`. -/
theorem of_retract {φ : M →ₗ[R] N} (h : IsBaseChange S φ) (φ' : M' →ₗ[R] N')
    (i : M' →ₗ[R] M) (p : M →ₗ[R] M') (hpi : p.comp i = LinearMap.id)
    (i' : N' →ₗ[S] N) (p' : N →ₗ[S] N') (hpi' : p'.comp i' = LinearMap.id)
    (hi : φ.comp i = (i'.restrictScalars R).comp φ')
    (hp : (p'.restrictScalars R).comp φ = φ'.comp p) :
    IsBaseChange S φ' := by
  let L : S ⊗[R] M' →ₗ[S] N' := φ'.liftBaseChange S
  let Lφ : S ⊗[R] M →ₗ[S] N := φ.liftBaseChange S
  have hL : Lφ = h.equiv.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext m
    simp [Lφ, IsBaseChange.equiv_tmul]
  have hLφ : Function.Bijective Lφ := hL ▸ h.equiv.bijective
  have nat_i : i'.comp L = Lφ.comp (i.baseChange S) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext m
    simp [L, Lφ, (apply_eq_of_restrictScalars_comp_eq hi.symm m).symm]
  have nat_p : p'.comp Lφ = L.comp (p.baseChange S) := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext m
    simp [L, Lφ, apply_eq_of_restrictScalars_comp_eq hp m]
  have hpib : (p.baseChange S).comp (i.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hpi, LinearMap.baseChange_id]
  have hbij : Function.Bijective L := by
    constructor
    · intro x y hxy
      have h1 : Lφ (i.baseChange S x) = Lφ (i.baseChange S y) := by
        simpa only [← LinearMap.comp_apply, nat_i] using congrArg i' hxy
      simpa only [← LinearMap.comp_apply, hpib, LinearMap.id_apply]
        using congrArg (p.baseChange S) (hLφ.1 h1)
    · intro n
      obtain ⟨t, ht⟩ := hLφ.2 (i' n)
      refine ⟨p.baseChange S t, ?_⟩
      have h1 : p' (Lφ t) = L (p.baseChange S t) := by
        rw [← LinearMap.comp_apply, nat_p, LinearMap.comp_apply]
      rw [← h1, ht, ← LinearMap.comp_apply, hpi', LinearMap.id_apply]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective L hbij) fun m => ?_
  simp [L]

end Retract

section LinearMap

variable {M N P Q : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  [AddCommGroup Q] [Module R Q] [Module S Q] [IsScalarTower R S Q]

/-- **Base change of linear maps out of a finite projective module.** If `α : M → P` and
`β : N → Q` are base changes along `R → S` and `M` is finite projective, then
`P →ₗ[S] Q` is the base change of `M →ₗ[R] N`, through the map sending `f` to the unique
`S`-linear map `F` with `F ∘ α = β ∘ f`. -/
theorem linearMapLeftRight_of_projective [Module.Finite R M] [Module.Projective R M]
    {α : M →ₗ[R] P} (j : IsBaseChange S α) {β : N →ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let jF := TensorProduct.isBaseChange R (Fin n → R) S
  have hF := linearMapLeftRight jF k
  -- the maps `f_S : S ⊗ F → P` and `g_S : P → S ⊗ F`
  let fS : S ⊗[R] (Fin n → R) →ₗ[S] P := jF.lift (α.comp f)
  let gS : P →ₗ[S] S ⊗[R] (Fin n → R) := j.lift ((TensorProduct.mk R S (Fin n → R) 1).comp g)
  have hfgS : fS.comp gS = LinearMap.id := by
    refine j.algHom_ext _ _ fun m => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, gS, fS]
    rw [j.lift_eq, LinearMap.comp_apply, TensorProduct.mk_apply]
    have := jF.lift_eq (α.comp f) (g m)
    simp only [TensorProduct.mk_apply] at this
    rw [this, LinearMap.comp_apply, ← LinearMap.comp_apply f g, hfg, LinearMap.id_apply]
  refine hF.of_retract (linearMapLeftRightHom j β) (LinearMap.lcomp R N f)
    (LinearMap.lcomp R N g) ?_ (LinearMap.lcomp S Q fS) (LinearMap.lcomp S Q gS) ?_ ?_ ?_
  · ext φ x
    simp [← LinearMap.comp_apply f g, hfg]
  · ext φ x
    simp only [LinearMap.comp_apply, LinearMap.lcomp_apply, LinearMap.id_apply]
    rw [← LinearMap.comp_apply fS gS, hfgS, LinearMap.id_apply]
  · refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    refine jF.algHom_ext _ _ fun x => ?_
    have h1 : fS ((TensorProduct.mk R S (Fin n → R) 1) x) = α (f x) := jF.lift_eq (α.comp f) x
    simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, linearMapLeftRightHom_comp_apply, h1]
  · refine LinearMap.ext fun φ => ?_
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars]
    refine j.algHom_ext _ _ fun x => ?_
    have h1 : gS (α x) = (TensorProduct.mk R S (Fin n → R) 1) (g x) :=
      j.lift_eq ((TensorProduct.mk R S (Fin n → R) 1).comp g) x
    simp only [LinearMap.lcomp_apply, LinearMap.comp_apply, linearMapLeftRightHom_comp_apply, h1]

end LinearMap

section Kernel

variable {M N M' N' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [Module S M'] [IsScalarTower R S M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [IsScalarTower R S N']

/-- The restriction of a compatible pair of base changes to the kernels. -/
def kerRestrict (f : M →ₗ[R] N) (f' : M' →ₗ[S] N') (σ : M →ₗ[R] M') (ν : N →ₗ[R] N')
    (hc : (f'.restrictScalars R).comp σ = ν.comp f) :
    LinearMap.ker f →ₗ[R] LinearMap.ker f' :=
  (σ.comp (LinearMap.ker f).subtype).codRestrict ((LinearMap.ker f').restrictScalars R)
    fun x => by
      change f' (σ x) = 0
      have := LinearMap.congr_fun hc x
      simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars] at this
      rw [this, x.2, map_zero]

/-- The restriction to the kernels acts by `σ`. -/
@[simp]
theorem coe_kerRestrict (f : M →ₗ[R] N) (f' : M' →ₗ[S] N') (σ : M →ₗ[R] M') (ν : N →ₗ[R] N')
    (hc : (f'.restrictScalars R).comp σ = ν.comp f) (x : LinearMap.ker f) :
    (kerRestrict f f' σ ν hc x : M') = σ x := rfl

/-- A base change of a surjection is surjective. -/
theorem surjective_of_surjective {f : M →ₗ[R] N} (f' : M' →ₗ[S] N') {σ : M →ₗ[R] M'}
    {ν : N →ₗ[R] N'} (hν : IsBaseChange S ν) (hc : (f'.restrictScalars R).comp σ = ν.comp f)
    (hf : Function.Surjective f) : Function.Surjective f' := by
  intro y
  induction y using hν.inductionOn with
  | zero => exact ⟨0, map_zero _⟩
  | tmul n =>
      obtain ⟨m, rfl⟩ := hf n
      refine ⟨σ m, ?_⟩
      simpa using apply_eq_of_restrictScalars_comp_eq hc m
  | smul s y hy =>
      obtain ⟨x, rfl⟩ := hy
      exact ⟨s • x, map_smul _ _ _⟩
  | add a b ha hb =>
      obtain ⟨x, rfl⟩ := ha
      obtain ⟨y, rfl⟩ := hb
      exact ⟨x + y, map_add _ _ _⟩

/-- **The kernel of a base change of a surjection onto a projective module is the base change of
the kernel.** -/
theorem ker_restrict [Module.Projective R N] {f : M →ₗ[R] N} (f' : M' →ₗ[S] N')
    {σ : M →ₗ[R] M'} (hσ : IsBaseChange S σ) {ν : N →ₗ[R] N'} (hν : IsBaseChange S ν)
    (hc : (f'.restrictScalars R).comp σ = ν.comp f) (hf : Function.Surjective f) :
    IsBaseChange S (kerRestrict f f' σ ν hc) := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let s' : N' →ₗ[S] M' := hν.lift (σ.comp s)
  have hs' : f'.comp s' = LinearMap.id := by
    refine hν.algHom_ext _ _ fun n => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, s', hν.lift_eq]
    rw [apply_eq_of_restrictScalars_comp_eq hc, ← LinearMap.comp_apply f s, hs, LinearMap.id_apply]
  let p : M →ₗ[R] LinearMap.ker f :=
    (LinearMap.id - s.comp f).codRestrict (LinearMap.ker f) fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
        LinearMap.comp_apply, ← LinearMap.comp_apply f s, hs, LinearMap.id_apply, sub_self]
  let p' : M' →ₗ[S] LinearMap.ker f' :=
    (LinearMap.id - s'.comp f').codRestrict (LinearMap.ker f') fun x => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, map_sub, LinearMap.id_apply,
        LinearMap.comp_apply, ← LinearMap.comp_apply f' s', hs', LinearMap.id_apply, sub_self]
  refine hσ.of_retract (kerRestrict f f' σ ν hc) (LinearMap.ker f).subtype p ?_
    (LinearMap.ker f').subtype p' ?_ ?_ ?_
  · ext x
    simp [p, x.2]
  · ext x
    simp [p', x.2]
  · ext x
    rfl
  · ext m
    have h1 := apply_eq_of_restrictScalars_comp_eq hc m
    simp only [LinearMap.comp_apply, LinearMap.coe_restrictScalars, coe_kerRestrict, p, p',
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, h1, s',
      hν.lift_eq]

end Kernel

end IsBaseChange

namespace Module.Invertible

variable {R : Type u} [CommRing R] {Z W : Type u} [AddCommGroup Z] [Module R Z]
  [AddCommGroup W] [Module R W] [Module.Invertible R Z]

/-- **Tensoring by an invertible module is faithful on elements.** If `z ⊗ w = 0` for every `z`
in an invertible module `Z`, then `w = 0`. -/
theorem eq_zero_of_forall_tmul_eq_zero {w : W} (h : ∀ z : Z, z ⊗ₜ[R] w = 0) : w = 0 := by
  let e := linearEquiv R Z
  let T : Module.Dual R Z ⊗[R] Z →ₗ[R] Module.Dual R Z ⊗[R] (Z ⊗[R] W) :=
    (TensorProduct.assoc R (Module.Dual R Z) Z W).toLinearMap.comp
      ((TensorProduct.mk R (Module.Dual R Z ⊗[R] Z) W).flip w)
  have hT : ∀ u, T u = 0 := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [T]
    | tmul φ z => simp [T, h z]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]
  have hc : ∀ u, (leftCancelEquiv W e) (T u) = e u • w := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp [T]
    | tmul φ z => simp [T, leftCancelEquiv]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, add_smul]
  obtain ⟨u, hu⟩ := e.surjective 1
  have := hc u
  rw [hT u, map_zero, hu, one_smul] at this
  exact this.symm

end Module.Invertible

end
