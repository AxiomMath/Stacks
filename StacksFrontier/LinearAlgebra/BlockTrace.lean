module

public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.Module.ZMod
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.GroupTrace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Traces of block endomorphisms, transported traces, and the projective trace

Three elementary facts about traces used to compute the trace of an endomorphism of the
cohomology of a disjoint union of curves.

* `LinearMap.trace_pi_eq_sum_trace_proj_comp_single`: the trace of an endomorphism of a finite
  product `∏_k M_k` of finite free modules is the sum of the traces of its diagonal blocks
  `M_k ⟶ ∏ M ⟶ ∏ M ⟶ M_k`.
* `AddMonoidHom.trace_toZModLinearMap_eq_of_addEquiv`: additive maps of `ℤ/n`-modules are
  linear, so conjugating an additive endomorphism by an additive equivalence does not change its
  trace over `ℤ/n`.
* `Stacks.Trace.projectiveModuleTrace_eq_mk_trace`: over a commutative ring, on a finite free
  module, the projective
  trace (valued in the additive commutator quotient) is the class of the usual trace.
-/

@[expose] public noncomputable section

open CategoryTheory.FilteredDerived

namespace LinearMap

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ι → Type*}
  [∀ k, AddCommGroup (M k)] [∀ k, Module R (M k)] [∀ k, Module.Free R (M k)]
  [∀ k, Module.Finite R (M k)]

/-- **The trace of an endomorphism of a finite product is the sum of the traces of its diagonal
blocks.** -/
@[sga "6 I 8.1.1" "special case"]
theorem trace_pi_eq_sum_trace_proj_comp_single (f : (∀ k, M k) →ₗ[R] (∀ k, M k)) :
    trace R (∀ k, M k) f = ∑ k, trace R (M k) ((proj k).comp (f.comp (single R M k))) := by
  have hf : f = ∑ k, (f.comp (single R M k)).comp (proj k) := by
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.sum_apply]
    simp only [comp_apply]
    rw [← map_sum]
    congr 1
    ext m
    simp [Finset.sum_apply]
  conv_lhs => rw [hf]
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => trace_comp_comm' _ _

end LinearMap

namespace AddMonoidHom

/-- **The trace over `ℤ/n` of an additive endomorphism is invariant under conjugation by an
additive equivalence**: additive maps of `ℤ/n`-modules are `ℤ/n`-linear. -/
@[sga "6 I 8.4" "special case"]
theorem trace_toZModLinearMap_eq_of_addEquiv {n : ℕ} {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [Module (ZMod n) A] [Module (ZMod n) B] [Module.Free (ZMod n) A]
    [Module.Finite (ZMod n) A] (e : A ≃+ B) (f : A →+ A) (g : B →+ B)
    (h : ∀ x, e (f x) = g (e x)) :
    LinearMap.trace (ZMod n) A (f.toZModLinearMap n) =
      LinearMap.trace (ZMod n) B (g.toZModLinearMap n) := by
  let E : A ≃ₗ[ZMod n] B := { e with map_smul' := ZMod.map_smul e.toAddMonoidHom }
  rw [← LinearMap.trace_conj' (f.toZModLinearMap n) E]
  congr 1
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  show e (f (e.symm (e x))) = g (e x)
  rw [e.symm_apply_apply, h]

end AddMonoidHom

namespace Stacks.Trace

/-- **Over a commutative ring the projective trace is the class of the trace.** -/
theorem projectiveModuleTrace_eq_mk_trace (R : Type*) [CommRing R] (P : Type*) [AddCommGroup P]
    [Module R P] [Module.Free R P] [Module.Finite R P] (f : Module.End R P) :
    projectiveModuleTrace R P f = additiveCommutatorQuotientMk R (LinearMap.trace R P f) := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R P
  let p : (Fin h.choose → R) →ₗ[R] P := h.choose_spec.choose
  let i : P →ₗ[R] (Fin h.choose → R) := h.choose_spec.choose_spec.choose
  have hi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  show freeModuleTrace R (Fin h.choose) (i.comp (f.comp p)) = _
  rw [freeModuleTrace_apply]
  congr 1
  have : LinearMap.trace R P f = LinearMap.trace R (Fin h.choose → R) (i.comp (f.comp p)) := by
    rw [LinearMap.trace_comp_comm' (f.comp p) i, LinearMap.comp_assoc, hi, LinearMap.comp_id]
  rw [this, LinearMap.trace_eq_matrix_trace R (Pi.basisFun R (Fin h.choose))]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply,
    Pi.basisFun_repr, standardBasisVector, LinearMap.comp_apply]
  convert rfl

end Stacks.Trace

end
