module

public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Strong limit cardinals closed under a function

For every function `f` on cardinals and every cardinal `μ₀` there is a strong limit cardinal
`κ > μ₀` of uncountable cofinality such that `f μ < κ` for every `μ < κ`. This is the cardinal
form of the transfinite construction in the proof of Stacks 000J, which closes an ordinal under
finitely many operations by an induction of length `ω₁`.

The witness is `ℶ_ (deriv g ω₁)` for a suitable `g`: since `Ordinal.deriv g` is a normal function
with `g (deriv g o + 1) ≤ deriv g (o + 1)`, every stage of the beth hierarchy along it bounds `f` on
the previous stage, and the cofinality of the supremum of an `ω₁`-indexed normal sequence is `ℵ₁`.

## Main results

* `Cardinal.exists_isStrongPrelimit_gt_forall_lt`: the closure point described above.
-/

@[expose] public section

open Ordinal Order

universe u

namespace Cardinal

/-- For every function `f` on cardinals and every cardinal `μ₀` there is a strong limit cardinal
`κ > μ₀` with `ℵ₀ < cf(κ)` such that `f μ < κ` for every `μ < κ`. -/
theorem exists_isStrongPrelimit_gt_forall_lt (f : Cardinal.{u} → Cardinal.{u})
    (μ₀ : Cardinal.{u}) :
    ∃ κ : Cardinal.{u}, μ₀ < κ ∧ IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof ∧ ∀ μ < κ, f μ < κ := by
  let g : Ordinal.{u} → Ordinal.{u} := fun x =>
    (succ (max μ₀ (⨆ μ : Set.Iic (ℶ_ x), f μ))).ord
  let h := deriv g
  have hh : IsNormal h := isNormal_deriv g
  have hlim : IsSuccLimit (ℵ_ 1).ord := isSuccLimit_ord (aleph0_le_aleph 1)
  have hN : IsNormal fun o => (ℶ_ (h o)).ord := (isNormal_ord.comp isNormal_beth).comp hh
  have key : ∀ o, ∀ μ ≤ ℶ_ (h o), max μ₀ (f μ) < ℶ_ (h (o + 1)) := by
    intro o μ hμ
    have hb : BddAbove (Set.range fun μ : Set.Iic (ℶ_ (h o + 1)) => f μ) :=
      bddAbove_of_small
    have h1 : max μ₀ (f μ) ≤ max μ₀ (⨆ μ : Set.Iic (ℶ_ (h o + 1)), f μ) :=
      max_le_max le_rfl (le_ciSup (f := fun μ : Set.Iic (ℶ_ (h o + 1)) => f μ) hb
        ⟨μ, hμ.trans (beth_mono le_self_add)⟩)
    have h2 : g (h o + 1) ≤ h (o + 1) := by
      simpa [h, deriv_add_one] using iterate_le_nfp g (deriv g o + 1) 1
    calc max μ₀ (f μ) < succ (max μ₀ (⨆ μ : Set.Iic (ℶ_ (h o + 1)), f μ)) :=
          lt_succ_of_le h1
      _ ≤ ℶ_ (g (h o + 1)) := le_beth_ord _
      _ ≤ ℶ_ (h (o + 1)) := beth_mono h2
  have hle : ∀ o < (ℵ_ 1).ord, ℶ_ (h (o + 1)) ≤ ℶ_ (h (ℵ_ 1).ord) := fun o ho =>
    beth_mono (hh.monotone (hlim.add_one_lt ho).le)
  refine ⟨ℶ_ (h (ℵ_ 1).ord), ?_, ?_, ?_, fun μ hμ => ?_⟩
  · exact (le_max_left _ _).trans_lt ((key 0 0 zero_le).trans_le (hle 0 hlim.bot_lt))
  · exact (isStrongLimit_beth.mpr (hh.map_isSuccLimit hlim).isSuccPrelimit).isStrongPrelimit
  · rw [cof_map_of_isNormal hN hlim, isRegular_aleph_one.cof_ord]
    exact aleph0_lt_aleph_one
  · obtain ⟨o, ho, hμo⟩ := (hN.lt_iff_exists_lt hlim).1 (ord_lt_ord.2 hμ)
    exact (le_max_right _ _).trans_lt ((key o μ (ord_lt_ord.1 hμo).le).trans_le (hle o ho))

end Cardinal
