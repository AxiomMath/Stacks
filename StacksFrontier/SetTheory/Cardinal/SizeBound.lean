module

public import Mathlib.SetTheory.Cardinal.Regular
public import StacksCore.Tactic.StacksAttribute

/-!
# The Stacks size bound function (Stacks 046U)

Stacks 046U introduces the auxiliary cardinal function
`Bound(κ) = max {κ ^ ℵ₀, κ⁺}`, used in Chapter 3 to fix a cardinal large enough that a
class of schemes bounded by `κ` stays inside a fixed set: it is the size bound appearing in
the construction of the big site `Sch_α` (Stacks 000J), where one closes a collection of
schemes under the constructions of interest by repeatedly enlarging `κ` to `Bound(κ)`.

Both ingredients are needed: `κ ^ ℵ₀` absorbs countable sequences of data (affine charts,
countable unions), while the cardinal successor `κ⁺` guarantees strict growth even when
`κ ^ ℵ₀ = κ`. On `Cardinal`, `Order.succ` *is* the cardinal successor `κ⁺`, since the
cardinals are well-ordered, so `Order.succ κ` needs no further translation.

## Main results

Besides the definition, this file collects the cardinal arithmetic behind the cutoff
cardinals of Stacks 000J and 000U.

* `Cardinal.power_aleph0_lt_of_isStrongPrelimit` and
  `Cardinal.stacksBound_lt_of_isStrongPrelimit`: a strong limit cardinal above `ℵ₀` is
  closed under `lam ↦ lam ^ ℵ₀` and under `Bound`.
* `Cardinal.stacksBound_iSup_lt_of_isStrongPrelimit`: if moreover the cofinality is
  uncountable, it is closed under `Bound` of a countable supremum.
* `Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof`: such cardinals are unbounded.
-/

@[expose] public section

open Cardinal Ordinal

universe u

/-- **Stacks 046U.** The bound function `Bound(κ) = max {κ ^ ℵ₀, κ⁺}` on cardinals.
Here `Order.succ κ` is the cardinal successor `κ⁺`. -/
@[stacks 046U]
noncomputable def Cardinal.stacksBound (κ : Cardinal) : Cardinal :=
  max (κ ^ Cardinal.aleph0) (Order.succ κ)

namespace Cardinal

/-- A power of two cardinals bounded by an infinite cardinal `μ` is bounded by `2 ^ μ`. -/
private theorem power_le_two_power_of_le {μ a b : Cardinal.{u}}
    (hμ : aleph0 ≤ μ) (ha : a ≤ μ) (hb : b ≤ μ) : a ^ b ≤ 2 ^ μ :=
  calc
    a ^ b ≤ (2 ^ μ) ^ μ :=
      (power_le_power_right (ha.trans (cantor μ).le)).trans
        (power_le_power_left (power_ne_zero _ two_ne_zero) hb)
    _ = 2 ^ μ := by rw [← power_mul, mul_eq_self hμ]

/-- A strong limit cardinal `κ > ℵ₀` is closed under `lam ↦ lam ^ ℵ₀`: writing
`mu = max lam ℵ₀`, we have `lam ^ ℵ₀ ≤ 2 ^ mu < κ`. -/
theorem power_aleph0_lt_of_isStrongPrelimit {κ lam : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (h : IsStrongPrelimit κ) (hlam : lam < κ) : lam ^ ℵ₀ < κ :=
  (power_le_two_power_of_le (le_max_right lam ℵ₀) (le_max_left _ _) (le_max_right _ _)).trans_lt
    (h (max_lt hlam hκ))

/-- **A strong limit cardinal above `ℵ₀` is closed under the Stacks bound function.**
Both halves of `Bound(lam) = max {lam ^ ℵ₀, lam⁺}` stay below `κ`: the first by
`Cardinal.power_aleph0_lt_of_isStrongPrelimit`, the second because `lam⁺ ≤ 2 ^ lam`. -/
theorem stacksBound_lt_of_isStrongPrelimit {κ lam : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (h : IsStrongPrelimit κ) (hlam : lam < κ) : stacksBound lam < κ :=
  max_lt (power_aleph0_lt_of_isStrongPrelimit hκ h hlam)
    ((Order.succ_le_of_lt (cantor lam)).trans_lt (h hlam))

/-- **A strong limit cardinal above `ℵ₀` of uncountable cofinality is closed under `Bound`
of a countable supremum.** The supremum of countably many cardinals below `κ` is below `κ`
because `cf(κ) > ℵ₀`, and `Bound` of it is below `κ` because `κ` is a strong limit. -/
theorem stacksBound_iSup_lt_of_isStrongPrelimit {κ : Cardinal.{u}} (hκ : ℵ₀ < κ)
    (h : IsStrongPrelimit κ) (hcof : ℵ₀ < κ.ord.cof) {ι : Type u} (hι : #ι ≤ ℵ₀)
    (f : ι → Cardinal.{u}) (hf : ∀ i, f i < κ) : stacksBound (⨆ i, f i) < κ :=
  stacksBound_lt_of_isStrongPrelimit hκ h (iSup_lt_of_lt_cof_ord (hι.trans_lt hcof) hf)

/-- **Strong limit cardinals of uncountable cofinality are unbounded.** For every cardinal
`mu` there is a strong limit cardinal `κ > mu` with `ℵ₀ < cf(κ)`.

The witness is `ℶ_ (mu.ord + ω₁)`. Its index is a limit ordinal, so the beth number is a
strong limit cardinal (`Cardinal.isStrongLimit_beth`); the index exceeds `mu.ord`, so
`κ > mu`; and `o ↦ (ℶ_ o).ord` is a normal function, so the cofinality of `κ.ord` is that
of `mu.ord + ω₁`, which is `cf(ω₁) = ℵ₁` because `ℵ₁` is regular. -/
theorem exists_isStrongPrelimit_gt_of_aleph0_lt_cof (mu : Cardinal.{u}) :
    ∃ κ : Cardinal.{u}, mu < κ ∧ IsStrongPrelimit κ ∧ ℵ₀ < κ.ord.cof := by
  have hlim : Order.IsSuccLimit ((ℵ_ 1).ord) := isSuccLimit_ord (aleph0_le_aleph 1)
  have hlim' : Order.IsSuccLimit (mu.ord + (ℵ_ 1).ord) := Ordinal.isSuccLimit_add _ hlim
  refine ⟨ℶ_ (mu.ord + (ℵ_ 1).ord),
    (le_beth_ord mu).trans_lt (beth_strictMono (by simpa using hlim.bot_lt)),
    (isStrongLimit_beth.mpr hlim'.isSuccPrelimit).isStrongPrelimit, ?_⟩
  rw [Ordinal.cof_map_of_isNormal (f := fun o => (ℶ_ o).ord)
      (isNormal_ord.comp isNormal_beth) hlim',
    Ordinal.cof_add _ hlim.ne_bot, isRegular_aleph_one.cof_ord]
  exact aleph0_lt_aleph_one

/-- A power of two cardinals below a strong prelimit uncountable cardinal stays below it. -/
theorem power_lt_of_isStrongPrelimit {κ a b : Cardinal.{u}} (hκ : aleph0 < κ)
    (hlim : κ.IsStrongPrelimit) (ha : a < κ) (hb : b < κ) : a ^ b < κ :=
  (power_le_two_power_of_le (le_max_left aleph0 (max a b))
    (le_max_left a b |>.trans (le_max_right _ _))
    (le_max_right a b |>.trans (le_max_right _ _))).trans_lt
    (hlim (max_lt hκ (max_lt ha hb)))

/-- A power of two cardinals bounded by an infinite cardinal `μ` is bounded by `2 ^ μ`. -/
theorem power_le_two_power {μ a b : Cardinal.{u}}
    (hμ : aleph0 ≤ μ) (ha : a ≤ μ) (hb : b ≤ μ) : a ^ b ≤ 2 ^ μ :=
  power_le_two_power_of_le hμ ha hb

end Cardinal
