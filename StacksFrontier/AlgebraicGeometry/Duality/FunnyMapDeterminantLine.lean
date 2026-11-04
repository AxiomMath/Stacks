module

public import StacksFrontier.AlgebraicGeometry.Duality.FunnyMap
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine

/-!
# The determinant line of a free two-term complex as a top-wedge tensor

For a two-term complex `dM : M⁻¹ → M⁰` of finite free modules of the same rank `n`, the
canonical maps of Stacks Tag 0FL8 take values in
`twoTermDeterminant R n M⁻¹ M⁰ = ⋀ⁿM⁰ ⊗ (⋀ⁿM⁻¹)^∨`, while the determinant line of
`TwoTermComplex.determinantLine` is `Hom(det M⁻¹, det M⁰)`, built from the determinant modules
`ProjectiveDeterminant.module` of finite projective modules. This file identifies the two.

The determinant module of a finite projective module of constant rank `m` is its `m`-th
exterior power, as submodules of the exterior algebra
(`determinantSubmodule_eq_exteriorPower_of_rankAtStalk`). Reading both determinant modules as
top exterior powers, the identification sends `z ⊗ φ` to the map `w ↦ φ(w) • z`; it carries the
canonical element of Tag 0FL8 to the canonical element `TwoTermComplex.delta`.

## Main definitions

* `Stacks.DeRham.determinantEquivExteriorPower`: the determinant module of a finite free module
  of rank `n` is its `n`-th exterior power.
* `Stacks.DeRham.twoTermDeterminantEval`: the evaluation `z ⊗ φ ↦ φ(Y) • z` of
  `⋀ⁿM⁰ ⊗ (⋀ⁿM⁻¹)^∨` at an element `Y` of `⋀ⁿM⁻¹`.
* `Stacks.DeRham.twoTermDeterminantEquivDeterminantLine`: the identification
  `⋀ⁿM⁰ ⊗ (⋀ⁿM⁻¹)^∨ ≃ Hom(det M⁻¹, det M⁰)`.

## Main results

* `Stacks.DeRham.determinantSubmodule_eq_exteriorPower_of_rankAtStalk`: the determinant module
  of a finite projective module of constant rank `m` is its `m`-th exterior power.
* `Stacks.DeRham.twoTermDeterminantEquivDeterminantLine_apply_tmul`,
  `Stacks.DeRham.twoTermDeterminantEquivDeterminantLine_apply`: the identification on pure
  tensors, and in general as an evaluation.
* `Stacks.DeRham.twoTermDeterminantEquivDeterminantLine_twoTermDeterminantElement`: it carries
  the canonical element of Tag 0FL8 to `TwoTermComplex.delta`.

## References

* [Stacks Project, Tag 0FL8](https://stacks.math.columbia.edu/tag/0FL8)
* [Stacks Project, Tag 0FJI](https://stacks.math.columbia.edu/tag/0FJI)
-/

@[expose] public section

namespace Stacks.DeRham

open scoped TensorProduct

universe u v w

section Rank

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- A module with a basis indexed by `Fin n` has rank `n` at every prime. -/
theorem rankAtStalk_eq_of_basis {n : ℕ} (b : Module.Basis (Fin n) R M)
    (p : PrimeSpectrum R) : Module.rankAtStalk M p = n := by
  have : Nontrivial R := ⟨⟨0, 1, fun h => p.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (h ▸ p.asIdeal.zero_mem))⟩⟩
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  simp [Module.finrank_eq_card_basis b]

/-- The `k`-th rank idempotent of a finite projective module of constant rank `m` is `1` if `k = m`
and `0` otherwise. -/
private theorem rankIdempotent_eq_ite [Module.Finite R M] [Module.Projective R M] {m : ℕ}
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = m) (k : ℕ) :
    ProjectiveDeterminant.rankIdempotent (R := R) (M := M) k = if k = m then 1 else 0 := by
  symm
  apply (Classical.choose_spec
    (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
      (ProjectiveDeterminant.rankLocus_isClopen (R := R) (M := M) k))).2
  split_ifs with hk
  · refine ⟨IsIdempotentElem.one, ?_⟩
    ext p
    simp [ProjectiveDeterminant.rankLocus, h p, hk]
  · refine ⟨IsIdempotentElem.zero, ?_⟩
    ext p
    simp [ProjectiveDeterminant.rankLocus, h p, Ne.symm hk]

/-- The determinant module of a finite projective module of constant rank `m` is its `m`-th
exterior power, as submodules of the exterior algebra. -/
theorem determinantSubmodule_eq_exteriorPower_of_rankAtStalk [Module.Finite R M]
    [Module.Projective R M] {m : ℕ} (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = m) :
    ProjectiveDeterminant.submodule (R := R) (M := M) = ⋀[R]^m M := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    rw [ProjectiveDeterminant.component, rankIdempotent_eq_ite h k]
    split_ifs with hk
    · subst k
      simp
    · simp
  · refine le_trans ?_ (ProjectiveDeterminant.component_le_submodule m)
    rw [ProjectiveDeterminant.component, rankIdempotent_eq_ite h m]
    simp

/-- The determinant module of a finite projective module with a basis indexed by `Fin n` is its
`n`-th exterior power. -/
noncomputable def determinantEquivExteriorPower [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (h : Nonempty (Module.Basis (Fin n) R M)) :
    ProjectiveDeterminant.module (R := R) (M := M) ≃ₗ[R] ⋀[R]^n M :=
  LinearEquiv.ofEq _ _
    (determinantSubmodule_eq_exteriorPower_of_rankAtStalk
      (rankAtStalk_eq_of_basis (Classical.choice h)))

/-- The identification of the determinant module with the top exterior power is the identity
on the underlying elements of the exterior algebra. -/
@[simp]
theorem coe_determinantEquivExteriorPower [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (h : Nonempty (Module.Basis (Fin n) R M))
    (x : ProjectiveDeterminant.module (R := R) (M := M)) :
    ((determinantEquivExteriorPower n h x : ⋀[R]^n M) : ExteriorAlgebra R M) =
      (x : ExteriorAlgebra R M) := rfl

/-- The inverse identification of the top exterior power with the determinant module is the
identity on the underlying elements of the exterior algebra. -/
@[simp]
theorem coe_determinantEquivExteriorPower_symm [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (h : Nonempty (Module.Basis (Fin n) R M)) (x : ⋀[R]^n M) :
    (((determinantEquivExteriorPower n h).symm x : ProjectiveDeterminant.module (R := R)
      (M := M)) : ExteriorAlgebra R M) = (x : ExteriorAlgebra R M) := rfl

end Rank

section Eval

variable {R : Type u} [CommRing R] {Mneg : Type v} {Mzero : Type w}
variable [AddCommGroup Mneg] [Module R Mneg] [AddCommGroup Mzero] [Module R Mzero]

/-- Evaluation of the determinant line `⋀ⁿM⁰ ⊗ (⋀ⁿM⁻¹)^∨` at an element `Y` of `⋀ⁿM⁻¹`: the
tensor `z ⊗ φ` goes to `φ(Y) • z`. -/
noncomputable def twoTermDeterminantEval (n : ℕ) (Y : ⋀[R]^n Mneg) :
    twoTermDeterminant R n Mneg Mzero →ₗ[R] ⋀[R]^n Mzero :=
  TensorProduct.lift ((LinearMap.lsmul R (⋀[R]^n Mzero)).flip.compl₂ (Module.Dual.eval R _ Y))

/-- The evaluation of the determinant line on pure tensors. -/
@[simp]
theorem twoTermDeterminantEval_tmul (n : ℕ) (Y : ⋀[R]^n Mneg) (z : ⋀[R]^n Mzero)
    (φ : Module.Dual R (⋀[R]^n Mneg)) :
    twoTermDeterminantEval n Y (z ⊗ₜ[R] φ) = φ Y • z := by
  simp [twoTermDeterminantEval]

end Eval

section Bridge

variable {R : Type u} [CommRing R] {Mneg : Type v} {Mzero : Type w}
variable [AddCommGroup Mneg] [Module R Mneg] [Module.Finite R Mneg] [Module.Projective R Mneg]
variable [AddCommGroup Mzero] [Module R Mzero] [Module.Finite R Mzero]
  [Module.Projective R Mzero]

omit [Module.Finite R Mneg] [Module.Projective R Mneg] [Module.Finite R Mzero]
  [Module.Projective R Mzero] in
/-- A two-term complex of modules with bases of the same length has rank zero. -/
theorem isRankZero_of_basis {n : ℕ} (dM : Mneg →ₗ[R] Mzero)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) : TwoTermComplex.IsRankZero dM :=
  fun p => (rankAtStalk_eq_of_basis (Classical.choice hneg) p).trans
    (rankAtStalk_eq_of_basis (Classical.choice hzero) p).symm

/-- The identification of the determinant line `⋀ⁿM⁰ ⊗ (⋀ⁿM⁻¹)^∨` of Tag 0FL8 with the
determinant line `Hom(det M⁻¹, det M⁰)` of a two-term complex of finite free modules of rank
`n`: the tensor `z ⊗ φ` goes to `w ↦ φ(w) • z`, the determinant modules being read as top
exterior powers. -/
noncomputable def twoTermDeterminantEquivDeterminantLine (n : ℕ) (dM : Mneg →ₗ[R] Mzero)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) :
    twoTermDeterminant R n Mneg Mzero ≃ₗ[R] TwoTermComplex.determinantLine dM :=
  letI := Module.Free.of_basis (Classical.choice hneg)
  (TensorProduct.comm R _ _).trans
    ((dualTensorHomEquiv R (⋀[R]^n Mneg) (⋀[R]^n Mzero)).trans
      (LinearEquiv.arrowCongr (determinantEquivExteriorPower n hneg).symm
        (determinantEquivExteriorPower n hzero).symm))

/-- The identification of determinant lines on pure tensors. -/
theorem twoTermDeterminantEquivDeterminantLine_apply_tmul (n : ℕ) (dM : Mneg →ₗ[R] Mzero)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) (z : ⋀[R]^n Mzero)
    (φ : Module.Dual R (⋀[R]^n Mneg)) (x : ProjectiveDeterminant.module (R := R) (M := Mneg)) :
    twoTermDeterminantEquivDeterminantLine n dM hzero hneg (z ⊗ₜ[R] φ) x =
      φ (determinantEquivExteriorPower n hneg x) •
        (determinantEquivExteriorPower n hzero).symm z := by
  let _ := Module.Free.of_basis (Classical.choice hneg)
  simp [twoTermDeterminantEquivDeterminantLine, dualTensorHomEquiv, dualTensorHom_apply]

/-- The identification of determinant lines, evaluated at an element of `det M⁻¹`, is the
evaluation of the determinant line of Tag 0FL8 at the corresponding top wedge. -/
theorem twoTermDeterminantEquivDeterminantLine_apply (n : ℕ) (dM : Mneg →ₗ[R] Mzero)
    (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) (t : twoTermDeterminant R n Mneg Mzero)
    (x : ProjectiveDeterminant.module (R := R) (M := Mneg)) :
    twoTermDeterminantEquivDeterminantLine n dM hzero hneg t x =
      (determinantEquivExteriorPower n hzero).symm
        (twoTermDeterminantEval n (determinantEquivExteriorPower n hneg x) t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul z φ =>
      rw [twoTermDeterminantEquivDeterminantLine_apply_tmul, twoTermDeterminantEval_tmul,
        map_smul]
  | add s t hs ht => rw [map_add, LinearMap.add_apply, hs, ht, map_add, map_add]

/-- The identification of determinant lines on the tensor attached to bases: the wedge of `c`
tensored with the dual of the wedge of a basis `b` goes to the map sending the wedge of `b` to
the wedge of `c`. -/
theorem twoTermDeterminantEquivDeterminantLine_ιMulti_tmul_basisTopDual (n : ℕ)
    (dM : Mneg →ₗ[R] Mzero) (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) (b : Module.Basis (Fin n) R Mneg)
    (c : Fin n → Mzero) :
    twoTermDeterminantEquivDeterminantLine n dM hzero hneg
        (exteriorPower.ιMulti R n c ⊗ₜ[R] basisTopDual b)
        ((determinantEquivExteriorPower n hneg).symm (exteriorPower.ιMulti R n b)) =
      (determinantEquivExteriorPower n hzero).symm (exteriorPower.ιMulti R n c) := by
  rw [twoTermDeterminantEquivDeterminantLine_apply_tmul, LinearEquiv.apply_symm_apply,
    basisTopDual_apply, one_smul]

/-- The identification of determinant lines carries the canonical element of Tag 0FL8 to the
canonical element `TwoTermComplex.delta` of the determinant line. -/
theorem twoTermDeterminantEquivDeterminantLine_twoTermDeterminantElement (n : ℕ)
    (dM : Mneg →ₗ[R] Mzero) (hzero : Nonempty (Module.Basis (Fin n) R Mzero))
    (hneg : Nonempty (Module.Basis (Fin n) R Mneg)) (hK : TwoTermComplex.IsRankZero dM) :
    twoTermDeterminantEquivDeterminantLine n dM hzero hneg
        (twoTermDeterminantElement R dM hneg) = TwoTermComplex.delta dM hK := by
  set b : Module.Basis (Fin n) R Mneg := Classical.choice hneg
  set E := determinantEquivExteriorPower n hneg
  have key : (TwoTermComplex.delta dM hK).comp E.symm.toLinearMap =
      (twoTermDeterminantEquivDeterminantLine n dM hzero hneg
        (twoTermDeterminantElement R dM hneg)).comp E.symm.toLinearMap := by
    refine linearMap_top_ext b ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      twoTermDeterminantElement_eq dM hneg b,
      twoTermDeterminantEquivDeterminantLine_ιMulti_tmul_basisTopDual]
    apply Subtype.ext
    show ExteriorAlgebra.map dM ((E.symm (exteriorPower.ιMulti R n b) :
      ProjectiveDeterminant.module (R := R) (M := Mneg)) : ExteriorAlgebra R Mneg) = _
    simp [E, ExteriorAlgebra.map_apply_ιMulti]
  refine LinearMap.ext fun x => ?_
  have hx := LinearMap.congr_fun key (E x)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at hx
  exact hx.symm

end Bridge

end Stacks.DeRham
