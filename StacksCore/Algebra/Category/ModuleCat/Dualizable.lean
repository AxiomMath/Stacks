module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-! # Dualizable modules are finite, and their evaluation is a perfect pairing

Two ungraded facts about an exact pairing `X`, `Y` of modules, used by the graded results of
Stacks 12.17 but of independent interest.

* `ModuleCat.finite_of_exactPairing`: a dualizable module is finite. Over a commutative ring;
  this is Mathlib's `Module.Finite.of_one_mem_range_dualTensorHom` fed by the coevaluation.
* `ModuleCat.pairingU_isPerfPair`: over a field, the evaluation is a perfect pairing. Both
  injectivity statements come from the two triangle identities, written out elementwise as
  `expand_X` and `expand_Y`.

Mathlib has no `Dualizable` class: dualizability is only ever expressed as `ExactPairing`, and
the finiteness consequence is stated in `Mathlib.LinearAlgebra.Contraction` in terms of
`dualTensorHom` rather than of duals in a monoidal category. These lemmas bridge the two.
-/

@[expose] public section

namespace ModuleCat

open CategoryTheory Category MonoidalCategory
open scoped TensorProduct

universe uF

section CommRing

variable {R : Type uF} [CommRing R] (X Y : ModuleCat.{uF} R) [pair : ExactPairing X Y]

/-- Expansion of the identity of `X` coming from the `X`-triangle. -/
lemma expand_X (s : Finset (X × Y)) (hs : ((η_ X Y).hom (1 : R)) = ∑ x ∈ s, x.1 ⊗ₜ[R] x.2)
    (v : X) : ∑ x ∈ s, ((ε_ X Y).hom (x.2 ⊗ₜ[R] v)) • x.1 = v := by
  simpa [-ExactPairing.evaluation_coevaluation, hs, TensorProduct.sum_tmul,
    MonoidalCategory.whiskerLeft_apply X (ε_ X Y)] using congrArg (TensorProduct.rid R X)
    congr($(ExactPairing.evaluation_coevaluation X Y).hom ((1 : R) ⊗ₜ[R] v))

/-- Expansion of the identity of `Y` coming from the `Y`-triangle. -/
lemma expand_Y (s : Finset (X × Y)) (hs : ((η_ X Y).hom (1 : R)) = ∑ x ∈ s, x.1 ⊗ₜ[R] x.2)
    (y : Y) : ∑ x ∈ s, ((ε_ X Y).hom (y ⊗ₜ[R] x.1)) • x.2 = y := by
  simpa [-ExactPairing.coevaluation_evaluation, hs, TensorProduct.tmul_sum,
    MonoidalCategory.whiskerRight_apply (ε_ X Y) Y] using congrArg (TensorProduct.lid R Y)
    congr($(ExactPairing.coevaluation_evaluation X Y).hom (y ⊗ₜ[R] (1 : R)))

include pair in
/-- Ungraded: a dualizable module is finite. -/
theorem finite_of_exactPairing : Module.Finite R X := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset ((η_ X Y).hom (1 : R))
  refine Module.Finite.of_one_mem_range_dualTensorHom (R := R) (M := X) ⟨
    ∑ x ∈ s, ((ε_ X Y).hom ∘ₗ TensorProduct.mk R Y X x.2) ⊗ₜ[R] x.1, ?_⟩
  ext v
  rw [map_sum, LinearMap.sum_apply, show (1 : X →ₗ[R] X) v = v from rfl]
  exact .trans (Finset.sum_congr rfl fun _ _ => rfl) (expand_X X Y s hs v)

end CommRing

section Field

variable {F : Type uF} [Field F] (X Y : ModuleCat.{uF} F) [ExactPairing X Y]

/-- The pairing `Y × X → F` defined by the evaluation. -/
noncomputable def pairingU : Y →ₗ[F] X →ₗ[F] F :=
  TensorProduct.curry ((ε_ X Y).hom : (Y ⊗[F] X) →ₗ[F] F)

lemma pairingU_apply (y : Y) (x : X) : pairingU X Y y x = (ε_ X Y).hom (y ⊗ₜ[F] x) := rfl

/-- Ungraded nondegeneracy: the evaluation of an exact pairing of `F`-modules is perfect. -/
theorem pairingU_isPerfPair : (pairingU X Y).IsPerfPair := by
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset ((η_ X Y).hom (1 : F))
  have : FiniteDimensional F X := finite_of_exactPairing X Y
  refine LinearMap.IsPerfPair.of_injective' ?_ ?_ <;>
    refine (injective_iff_map_eq_zero _).2 fun v hv => ?_
  · rw [← expand_Y X Y s hs v]
    exact Finset.sum_eq_zero fun x _ => by simp [← pairingU_apply, hv]
  · rw [← expand_X X Y s hs v]
    exact Finset.sum_eq_zero fun z _ => by simp [← pairingU_apply, ← LinearMap.flip_apply, hv]

end Field

end ModuleCat
