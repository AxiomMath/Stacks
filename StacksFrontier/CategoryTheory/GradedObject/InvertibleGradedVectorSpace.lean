module

public import StacksCore.CategoryTheory.GradedObject.GradedVectorSpace
public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObject
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.Basic

/-!
# Invertible graded vector spaces are one dimensional

Let `F` be a field and `V` a `ℤ`-graded `F`-vector space, with the monoidal structure of Stacks,
Homology, Example 0FFX. If `V ⊗ W ≅ 𝟏` for some graded vector space `W` — in particular if `V` is
invertible (Stacks 0FFN) — then `V` is one dimensional and concentrated in a single degree: there
is an `n` with `dim_F Vⁿ = 1` and `Vᵐ = 0` for `m ≠ n`, that is `∑ᵢ dim_F Vⁱ = 1`.

## Main results

* `CategoryTheory.GradedObject.Monoidal.ιTensorObj_injective`: each summand `Vᵖ ⊗_F W^q` of
  `(V ⊗ W)^{p+q}` injects into it, the projection `πTensorObj` being a retraction.
* `CategoryTheory.GradedObject.Monoidal.exists_finrank_eq_one_of_tensorObj_iso_tensorUnit`: if
  `V ⊗ W ≅ 𝟏` then `V` is one dimensional, concentrated in one degree.
* `CategoryTheory.GradedObject.Monoidal.exists_finrank_eq_one_of_isInvertible`: the same for an
  invertible `V`.

## References

* [Stacks Project, Tag 0FFX](https://stacks.math.columbia.edu/tag/0FFX)
* [Stacks Project, Tag 0FFN](https://stacks.math.columbia.edu/tag/0FFN)
* [Stacks Project, Tag 0FH1](https://stacks.math.columbia.edu/tag/0FH1)
-/

@[expose] public section

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory Limits MonoidalCategory GradedObject
open scoped TensorProduct

universe uF

variable {F : Type uF} [Field F] (V W : GradedObject ℤ (ModuleCat.{uF} F))

/-- The inclusion of a summand `Vᵖ ⊗_F W^q` into `(V ⊗ W)^{p+q}` is injective. -/
lemma ιTensorObj_injective (p q n : ℤ) (h : p + q = n) :
    Function.Injective (ιTensorObj V W p q n h).hom := by
  intro x y hxy
  have := congrArg (πTensorObj V W p q n h).hom hxy
  rwa [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ιTensorObj_πTensorObj_self,
    ModuleCat.id_apply, ModuleCat.id_apply] at this

/-- A tensor product of two nonzero vector spaces is nonzero. -/
private lemma nontrivial_tensorProduct (M N : Type*) [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] [Nontrivial M] [Nontrivial N] : Nontrivial (M ⊗[F] N) := by
  obtain ⟨n, hn⟩ := exists_ne (0 : N)
  exact TensorProduct.nontrivial_of_linearMap_injective_of_flat_left F M N
    (LinearMap.toSpanSingleton F N n) (fun a b hab => smul_left_injective F hn hab)

/-- A degree of `V ⊗ W` receiving a summand `Vᵖ ⊗ W^q` with both factors nonzero is nonzero. -/
private lemma nontrivial_tensorObj (p q : ℤ) [Nontrivial (V p)] [Nontrivial (W q)] :
    Nontrivial ((V ⊗ W) (p + q)) := by
  have := nontrivial_tensorProduct (F := F) (V p) (W q)
  exact (ιTensorObj_injective V W p q (p + q) rfl).nontrivial

open scoped Classical in
/-- If `V ⊗ W ≅ 𝟏` in graded `F`-vector spaces, then `V` is one dimensional and concentrated in a
single degree `n`: `dim_F Vⁿ = 1` and `Vᵐ = 0` for `m ≠ n`. -/
theorem exists_finrank_eq_one_of_tensorObj_iso_tensorUnit (e : V ⊗ W ≅ 𝟙_ _) :
    ∃ n : ℤ, Module.finrank F (V n) = 1 ∧ ∀ m, m ≠ n → IsZero (V m) := by
  have e₀ : (V ⊗ W) 0 ≅ 𝟙_ (ModuleCat.{uF} F) :=
    (GradedObject.eval 0).mapIso e ≪≫ tensorUnit₀ (I := ℤ) (C := ModuleCat.{uF} F)
  have hrank₀ : Module.finrank F ((V ⊗ W) 0) = 1 :=
    e₀.toLinearEquiv.finrank_eq.trans (Module.finrank_self F)
  have hzero : ∀ m, m ≠ 0 → Subsingleton ((V ⊗ W) m) := fun m hm =>
    ModuleCat.subsingleton_of_isZero
      (((isInitialTensorUnitApply (I := ℤ) (C := ModuleCat.{uF} F) m hm).isZero).of_iso
        ((GradedObject.eval m).mapIso e))
  have : Module.Finite F ((V ⊗ W) 0) := Module.finite_of_finrank_eq_succ hrank₀
  have : Nontrivial ((V ⊗ W) 0) := Module.nontrivial_of_finrank_eq_succ hrank₀
  obtain ⟨x, hx⟩ := exists_ne (0 : (V ⊗ W) 0)
  obtain ⟨a, -, ha⟩ : ∃ a ∈ (comps V W 0 x).support, comps V W 0 x a ≠ 0 := by
    by_contra! H
    exact hx ((sum_ι_comps V W 0 x).symm.trans
      (Finset.sum_eq_zero fun a h => by rw [H a h, map_zero]))
  obtain ⟨⟨p, q⟩, hpq⟩ := a
  have hq : q = -p := by simp only [Set.mem_preimage, Set.mem_singleton_iff] at hpq; omega
  subst hq
  have : Nontrivial (V p ⊗[F] W (-p)) := ⟨⟨_, 0, ha⟩⟩
  have hι := ιTensorObj_injective V W p (-p) 0 (add_neg_cancel p)
  refine ⟨p, ?_, fun m hm => ?_⟩
  · have : Module.Finite F (V p ⊗[F] W (-p)) := Module.Finite.of_injective _ hι
    have h₁ : Module.finrank F (V p ⊗[F] W (-p)) = 1 :=
      le_antisymm (hrank₀ ▸ LinearMap.finrank_le_finrank_of_injective hι) Module.finrank_pos
    rw [Module.finrank_tensorProduct] at h₁
    exact Nat.eq_one_of_mul_eq_one_right h₁
  · rw [ModuleCat.isZero_iff_subsingleton, ← not_nontrivial_iff_subsingleton]
    intro hV
    have : Nontrivial (W (-p)) := by
      by_contra hW
      rw [not_nontrivial_iff_subsingleton] at hW
      exact not_subsingleton (V p ⊗[F] W (-p)) inferInstance
    have := nontrivial_tensorObj V W m (-p)
    exact not_subsingleton _ (hzero (m + -p) (by omega))

/-- An invertible graded `F`-vector space is one dimensional and concentrated in a single
degree `n`: `dim_F Vⁿ = 1` and `Vᵐ = 0` for `m ≠ n`. -/
theorem exists_finrank_eq_one_of_isInvertible (hV : IsInvertible V) :
    ∃ n : ℤ, Module.finrank F (V n) = 1 ∧ ∀ m, m ≠ n → IsZero (V m) :=
  let ⟨h⟩ := hV
  exists_finrank_eq_one_of_tensorObj_iso_tensorUnit V h.inv h.isoLeft

end CategoryTheory.GradedObject.Monoidal
