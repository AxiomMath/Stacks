module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Algebra.Module.ZMod
public import StacksFrontier.Algebra.Module.Injective.ZModDuality

/-!
# `M ≅ Hom_{A[H]}(M^*, A[H])` for a finite group `H` and `A = ℤ/n`

Let `H` be a finite group, `A = ℤ/n`, and `M` a finite `ℤ/n`-module with an action
`ρ : H →* End_Λ(M)` commuting with a ring `Λ`. The dual `M^* = Hom_A(M, A)` is an `A[H]`-module
through the dual representation `(h φ)(m) = φ(h⁻¹ m)`, and a right `Λ`-module through
`(φ λ)(m) = φ(λ m)`, the two actions commuting. The map

`M → Hom_{A[H]}(M^*, A[H]), m ↦ (φ ↦ ∑_g φ(g m) g)`

is a bijection (Frobenius reciprocity `Hom_{A[H]}(N, A[H]) ≅ Hom_A(N, A)`, `ψ ↦ coeff₁ ∘ ψ`,
followed by the evaluation isomorphism `M ≅ M^{**}` of a finite `ℤ/n`-module), it is
`Λ`-linear, and it carries the action of `h` on `M` to right multiplication by `h⁻¹` on
`A[H]`. This is the module-theoretic content of Steps 4–6 of the proof of [Stacks, Tag 03UG]:
the sheaf `ℱ` with monodromy `M` is `Hom_{A[H]}(M^*, f_* A)`.

## Main definitions

* `Stacks.GroupAlgebraDual.Dual`: `M^*` as an `A[H]`-module with a commuting right `Λ`-action.
* `Stacks.GroupAlgebraDual.ofM`: the map `m ↦ (φ ↦ ∑_g φ(g m) g)`.

## Main results

* `Stacks.GroupAlgebraDual.ofM_bijective`.
* `Stacks.GroupAlgebraDual.ofM_rho`, `Stacks.GroupAlgebraDual.ofM_smul`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Steps 4–7.
-/

@[expose] public noncomputable section

open MonoidAlgebra

namespace Stacks.GroupAlgebraDual

variable (n : ℕ) {H : Type} [Group H] {Λ : Type*} [Ring Λ] {M : Type*} [AddCommGroup M]
  [Module Λ M] [Module (ZMod n) M] (ρ : H →* Module.End Λ M)

/-- The `ℤ/n`-linear representation underlying `ρ`. -/
def zmodRep : Representation (ZMod n) H M where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext m; simp
  map_mul' g h := by ext m; simp [Module.End.mul_apply]

/-- `zmodRep n ρ g` acts on `M` as `ρ g`. -/
@[simp]
lemma zmodRep_apply (g : H) (m : M) : zmodRep n ρ g m = ρ g m := rfl

/-- **The dual `M^* = Hom_{ℤ/n}(M, ℤ/n)`** with `H` acting by `(g φ)(m) = φ(g⁻¹ m)`, as a module
over the group algebra `(ℤ/n)[H]`. -/
abbrev Dual : Type _ := (zmodRep n ρ).dual.asModule

variable {n ρ}

/-- A dual element as a linear form. -/
abbrev toForm (φ : Dual n ρ) : Module.Dual (ZMod n) M := (zmodRep n ρ).dual.asModuleEquiv φ

/-- `toForm` is injective. -/
lemma toForm_injective : Function.Injective (toForm (n := n) (ρ := ρ)) :=
  ((zmodRep n ρ).dual.asModuleEquiv).injective

/-- Two elements of `M^*` with the same linear form are equal. -/
lemma ext_dual {φ ψ : Dual n ρ} (h : ∀ m, toForm φ m = toForm ψ m) : φ = ψ :=
  toForm_injective (LinearMap.ext h)

/-- `toForm` is additive. -/
@[simp]
lemma toForm_add (φ ψ : Dual n ρ) (m : M) : toForm (φ + ψ) m = toForm φ m + toForm ψ m := rfl

/-- The action of `a g ∈ (ℤ/n)[H]` on `M^*`: `(a g · φ)(m) = a φ(g⁻¹ m)`. -/
lemma toForm_single_smul (g : H) (a : ZMod n) (φ : Dual n ρ) (m : M) :
    toForm (single g a • φ) m = a * toForm φ (ρ g⁻¹ m) := by
  rw [toForm, Representation.single_smul]
  rfl

/-- A scalar `a ∈ ℤ/n ⊆ (ℤ/n)[H]` acts on `M^*` by multiplication by `a`. -/
lemma toForm_zmod_smul (a : ZMod n) (φ : Dual n ρ) (m : M) :
    toForm ((single (1 : H) a : MonoidAlgebra (ZMod n) H) • φ) m = a * toForm φ m := by
  rw [toForm_single_smul, inv_one, map_one, Module.End.one_apply]

/-- Multiplication by `λ` as a `ℤ/n`-linear map. -/
def smulZ (l : Λ) : M →ₗ[ZMod n] M := (DistribSMul.toAddMonoidHom M l).toZModLinearMap n

/-- The right action of `Λ` on `M^*`: `(φ λ)(m) = φ(λ m)`. -/
instance : SMul Λᵐᵒᵖ (Dual n ρ) where
  smul l φ := (zmodRep n ρ).dual.asModuleEquiv.symm ((toForm φ).comp (smulZ (n := n) l.unop))

/-- The right action of `λ` on `M^*` is `(φ λ)(m) = φ(λ m)`. -/
@[simp]
lemma toForm_op_smul (l : Λᵐᵒᵖ) (φ : Dual n ρ) (m : M) :
    toForm (l • φ) m = toForm φ (l.unop • m) := rfl

/-- `M^*` is a right `Λ`-module. -/
instance : Module Λᵐᵒᵖ (Dual n ρ) where
  one_smul φ := ext_dual fun m => by simp
  mul_smul l l' φ := ext_dual fun m => by simp [mul_smul]
  smul_zero l := ext_dual fun m => by simp
  smul_add l φ ψ := ext_dual fun m => by simp
  add_smul l l' φ := ext_dual fun m => by simp [add_smul]
  zero_smul φ := ext_dual fun m => by simp

/-- The right `Λ`-action on `M^*` commutes with the `(ℤ/n)[H]`-action. -/
instance : SMulCommClass Λᵐᵒᵖ (MonoidAlgebra (ZMod n) H) (Dual n ρ) where
  smul_comm l r φ := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul, zero_smul, smul_zero]
    | add r r' hr hr' => rw [add_smul, add_smul, smul_add, hr, hr']
    | single g a =>
      refine ext_dual fun m => ?_
      rw [toForm_op_smul, toForm_single_smul, toForm_single_smul, toForm_op_smul,
        (ρ g⁻¹).map_smul]

variable [Fintype H]

/-- The `A[H]`-linear map `φ ↦ ∑_g φ(g m) g` attached to `m ∈ M`. -/
def ofM (m : M) : Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H where
  toFun φ := ∑ g : H, single g (toForm φ (ρ g m))
  map_add' φ ψ := by simp [Finset.sum_add_distrib, single_add]
  map_smul' r φ := by
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r r' hr hr' =>
      simp only [RingHom.id_apply, smul_eq_mul] at hr hr' ⊢
      rw [add_smul, add_mul, ← hr, ← hr', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [toForm_add, single_add]
    | single k a =>
      simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum, single_mul_single]
      refine (Equiv.sum_comp (Equiv.mulLeft k)
        (fun y => single y (toForm (single k a • φ) (ρ y m)))).symm.trans
        (Finset.sum_congr rfl fun g _ => ?_)
      simp only [Equiv.coe_mulLeft]
      rw [toForm_single_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_left]

/-- `ofM m φ = ∑_g φ(g m) g`. -/
lemma ofM_apply (m : M) (φ : Dual n ρ) :
    ofM m φ = ∑ g : H, single g (toForm φ (ρ g m)) := rfl

/-- The coefficient of `g` in `ofM m φ` is `φ(g m)`. -/
lemma coeff_ofM (m : M) (φ : Dual n ρ) (g : H) : (ofM m φ).coeff g = toForm φ (ρ g m) := by
  classical
  rw [ofM_apply, coeff_sum, Finset.sum_apply', Finset.sum_eq_single g]
  · simp [coeff_single]
  · intro σ _ hσ
    simp [coeff_single, hσ]
  · simp

/-- `ofM` intertwines the action of `h` on `M` with right multiplication by `h⁻¹`. -/
lemma ofM_rho (h : H) (m : M) (φ : Dual n ρ) :
    ofM (ρ h m) φ = ofM m φ * single h⁻¹ 1 := by
  ext g
  rw [coeff_ofM, coeff_mul_single_apply, coeff_ofM, inv_inv, mul_one, map_mul,
    Module.End.mul_apply]

/-- `ofM` is `Λ`-linear for the right action of `Λ` on `M^*`. -/
lemma ofM_smul (l : Λ) (m : M) (φ : Dual n ρ) :
    ofM (l • m) φ = ofM m (MulOpposite.op l • φ) := by
  ext g
  rw [coeff_ofM, coeff_ofM, toForm_op_smul, MulOpposite.unop_op, (ρ g).map_smul]

/-- `ofM` is additive in `m`. -/
lemma ofM_add (m m' : M) : ofM (n := n) (ρ := ρ) (m + m') = ofM m + ofM m' := by
  ext φ g
  simp only [LinearMap.add_apply, coeff_add, Finsupp.add_apply, coeff_ofM, map_add]

variable [NeZero n] [Finite M]

/-- For a finite `ℤ/n`-module `M`, the map `ofM` is injective. -/
lemma ofM_injective : Function.Injective (ofM (n := n) (ρ := ρ)) := by
  intro m m' h
  refine (ZMod.evalEquiv n M).injective (LinearMap.ext fun φ₀ => ?_)
  let φ : Dual n ρ := (zmodRep n ρ).dual.asModuleEquiv.symm φ₀
  have := congrArg (fun ψ => (ψ φ).coeff 1) h
  simp only [coeff_ofM, map_one, Module.End.one_apply] at this
  exact this

/-- For a finite `ℤ/n`-module `M`, every `(ℤ/n)[H]`-linear map `M^* → (ℤ/n)[H]` is of the form
`ofM m`. -/
lemma ofM_surjective (ψ : Dual n ρ →ₗ[MonoidAlgebra (ZMod n) H] MonoidAlgebra (ZMod n) H) :
    ∃ m, ofM m = ψ := by
  let Φ : Module.Dual (ZMod n) (Module.Dual (ZMod n) M) :=
    { toFun := fun φ₀ => (ψ ((zmodRep n ρ).dual.asModuleEquiv.symm φ₀)).coeff 1
      map_add' := fun φ₀ φ₁ => by rw [map_add, map_add, coeff_add, Finsupp.add_apply]
      map_smul' := fun a φ₀ => by
        rw [RingHom.id_apply, smul_eq_mul]
        have hs : (zmodRep n ρ).dual.asModuleEquiv.symm (a • φ₀) =
            (single (1 : H) a : MonoidAlgebra (ZMod n) H) •
              (zmodRep n ρ).dual.asModuleEquiv.symm φ₀ :=
          ext_dual fun m => (toForm_zmod_smul a _ m).symm
        rw [hs, map_smul, smul_eq_mul, coeff_single_mul_apply, inv_one, one_mul] }
  set m := (ZMod.evalEquiv n M).symm Φ
  refine ⟨m, LinearMap.ext fun φ => ?_⟩
  ext g
  have hm : ∀ φ' : Dual n ρ, toForm φ' m = (ψ φ').coeff 1 := fun φ' =>
    (LinearMap.congr_fun ((ZMod.evalEquiv n M).apply_symm_apply Φ) (toForm φ')).trans (by simp [Φ])
  have h1 : toForm φ (ρ g m) = toForm (single g⁻¹ (1 : ZMod n) • φ) m := by
    rw [toForm_single_smul, inv_inv, one_mul]
  rw [coeff_ofM, h1, hm, map_smul, smul_eq_mul, coeff_single_mul_apply, inv_inv, mul_one, one_mul]

/-- For a finite `ℤ/n`-module `M`, the map `M → Hom_{(ℤ/n)[H]}(M^*, (ℤ/n)[H])` given by `ofM`
is bijective. -/
lemma ofM_bijective : Function.Bijective (ofM (n := n) (ρ := ρ)) :=
  ⟨ofM_injective, ofM_surjective⟩

end Stacks.GroupAlgebraDual

end
