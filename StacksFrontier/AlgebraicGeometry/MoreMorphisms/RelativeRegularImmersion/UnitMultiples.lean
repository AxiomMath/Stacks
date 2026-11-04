module

public import StacksFrontier.RingTheory.Sequence.QuasiRegular.Basic
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regularity and generation only depend on a sequence up to unit multiples

Replacing every member of a finite family or a list of elements of a commutative ring by a unit
multiple changes neither the ideal it generates nor, for a list, its regularity on a module.

## Main results

* `Stacks.AlgebraicGeometry.span_range_eq_of_unit_mul`: the ideal generated is unchanged.
* `Stacks.AlgebraicGeometry.isWeaklyRegular_of_forall₂_unit_mul`: weak regularity is unchanged.
* `Stacks.AlgebraicGeometry.isRegular_of_forall₂_unit_mul`: regularity is unchanged.
-/

@[expose] public section

open RingTheory.Sequence

open scoped Pointwise

namespace Stacks.AlgebraicGeometry

variable {R : Type*} [CommRing R]

/-- **Replacing every member of a finite family by a unit multiple does not change the ideal it
generates.** -/
theorem span_range_eq_of_unit_mul {r : ℕ} (a b : Fin r → R) (u : Fin r → Rˣ)
    (hab : ∀ i, b i = (u i : R) * a i) :
    Ideal.span (Set.range a) = Ideal.span (Set.range b) := by
  simp_rw [Ideal.span_range_eq_iSup, hab, Ideal.span_singleton_mul_left_unit (u _).isUnit]

/-- Replacing every member of a list by a unit multiple does not change the ideal it generates. -/
theorem ofList_eq_of_forall₂_unit_mul {ss rs : List R}
    (h : List.Forall₂ (fun s r => ∃ u : Rˣ, s = (u : R) * r) ss rs) :
    Ideal.ofList ss = Ideal.ofList rs := by
  induction h with
  | nil => rfl
  | @cons s r ss' rs' hu _ ih =>
    obtain ⟨u, rfl⟩ := hu
    rw [Ideal.ofList_cons, Ideal.ofList_cons, ih, Ideal.span_singleton_mul_left_unit u.isUnit]

/-- **Weak regularity only depends on a sequence up to unit multiples.** -/
theorem isWeaklyRegular_of_forall₂_unit_mul {ss rs : List R}
    (h : List.Forall₂ (fun s r => ∃ u : Rˣ, s = (u : R) * r) ss rs) :
    ∀ {V : Type*} [AddCommGroup V] [Module R V],
      IsWeaklyRegular V rs → IsWeaklyRegular V ss := by
  induction h with
  | nil => intro V _ _ _; simp
  | @cons s r ss' rs' hu _ ih =>
    intro V _ _ hr
    obtain ⟨u, rfl⟩ := hu
    rw [isWeaklyRegular_cons_iff] at hr ⊢
    have heq : ((u : R) * r) • (⊤ : Submodule R V) = r • (⊤ : Submodule R V) := by
      rw [← Submodule.ideal_span_singleton_smul, ← Submodule.ideal_span_singleton_smul,
        Ideal.span_singleton_mul_left_unit u.isUnit]
    exact ⟨(u.isUnit.isSMulRegular V).mul hr.1,
      ih (((Submodule.quotEquivOfEq _ _ heq).isWeaklyRegular_congr rs').mpr hr.2)⟩

/-- **Regularity only depends on a sequence up to unit multiples.** -/
theorem isRegular_of_forall₂_unit_mul {V : Type*} [AddCommGroup V] [Module R V]
    {ss rs : List R} (h : List.Forall₂ (fun s r => ∃ u : Rˣ, s = (u : R) * r) ss rs)
    (hreg : IsRegular V rs) : IsRegular V ss :=
  ⟨isWeaklyRegular_of_forall₂_unit_mul h hreg.toIsWeaklyRegular, by
    rw [ofList_eq_of_forall₂_unit_mul h]
    exact hreg.top_ne_smul⟩

/-- The unit-multiple relation between two families, as a relation between the corresponding
lists. -/
theorem forall₂_unit_mul_ofFn {r : ℕ} (a b : Fin r → R) (u : Fin r → Rˣ)
    (hab : ∀ i, b i = (u i : R) * a i) :
    List.Forall₂ (fun s t => ∃ v : Rˣ, s = (v : R) * t) (List.ofFn b) (List.ofFn a) := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.forall₂_map_left_iff,
    List.forall₂_map_right_iff]
  exact List.forall₂_same.mpr fun i _ => ⟨u i, hab i⟩

end Stacks.AlgebraicGeometry

end
