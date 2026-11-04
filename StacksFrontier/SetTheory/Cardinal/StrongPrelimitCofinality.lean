module

public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# Strong limit cardinals of large cofinality

`Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof` produces, above any cardinal, a strong
limit cardinal of uncountable cofinality. This file strengthens the cofinality bound to exceed
any prescribed cardinal.

## Main results

* `Cardinal.exists_isStrongPrelimit_gt_of_lt_cof`: strong limit cardinals of cofinality above any
  prescribed cardinal are unbounded.
-/

@[expose] public section

open Cardinal Ordinal

universe u

namespace Cardinal

/-- **Strong limit cardinals of cofinality above a prescribed cardinal are unbounded.** For all
cardinals `mu` and `lam` there is a strong limit cardinal `κ > mu` whose cofinality exceeds both
`ℵ₀` and `lam`.

The witness is `ℶ_ (mu.ord + ν.ord)` for the regular cardinal `ν = (max lam ℵ₀)⁺`, exactly as in
`Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof` with `ℵ₁` replaced by `ν`: the cofinality
of `κ.ord` is that of `mu.ord + ν.ord`, which is `cf(ν.ord) = ν`. -/
theorem exists_isStrongPrelimit_gt_of_lt_cof (mu lam : Cardinal.{u}) :
    ∃ κ : Cardinal.{u}, mu < κ ∧ IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof ∧ lam < κ.ord.cof := by
  set ν : Cardinal.{u} := Order.succ (max lam ℵ₀) with hν
  have hreg : ν.IsRegular := isRegular_succ (le_max_right _ _)
  have hlim : Order.IsSuccLimit ν.ord := isSuccLimit_ord hreg.aleph0_le
  have hlim' : Order.IsSuccLimit (mu.ord + ν.ord) := Ordinal.isSuccLimit_add _ hlim
  have hcof : (ℶ_ (mu.ord + ν.ord)).ord.cof = ν := by
    rw [Ordinal.cof_map_of_isNormal (f := fun o => (ℶ_ o).ord)
        (isNormal_ord.comp isNormal_beth) hlim',
      Ordinal.cof_add _ hlim.ne_bot, hreg.cof_ord]
  have hlt : max lam ℵ₀ < ν := Order.lt_succ_of_not_isMax (not_isMax _)
  refine ⟨ℶ_ (mu.ord + ν.ord), ?_,
    (isStrongLimit_beth.mpr hlim'.isSuccPrelimit).isStrongPrelimit, ?_, ?_⟩
  · exact (le_beth_ord mu).trans_lt (beth_strictMono (by simpa using hlim.bot_lt))
  · rw [hcof]; exact (le_max_right _ _).trans_lt hlt
  · rw [hcof]; exact (le_max_left _ _).trans_lt hlt

end Cardinal

end
