module

public import Mathlib.Data.Int.LeastGreatest
public import StacksFrontier.Order.HeightCoheight

/-!
# Height and coheight in a poset with an integer grading

Let `δ : α → ℤ` be strictly monotone on a partial order `α`, with `δ b = δ a + 1` whenever `b`
covers `a`. Between two comparable points `x ≤ y` every strictly increasing chain has length at
most `δ y - δ x`, and there is one of exactly that length: refine step by step through a point
below `y` of largest grade. Consequently, if every point lies above a minimal one and minimal
points have grade `0`, the height of `x` is `δ x`; if every point lies below a maximal one, the
coheight of `x` is the largest value of `δ η - δ x` over maximal `η ≥ x`.

On a sober space with the specialization order these are the statements that a dimension
function vanishing at closed points is the dimension of the closure of a point, and that the
dimension of the local ring is the largest drop of the dimension function to a generic point.

## Main results

* `Order.exists_ltSeries_of_grade` and `Order.length_le_of_grade` — the two halves of the chain
  count between comparable points.
* `Order.height_eq_of_grade` — `height x = δ x`.
* `Order.coheight_eq_of_grade` — `coheight x` is the supremum of `δ η - δ x` over maximal
  `η ≥ x`.
* `Order.height_add_coheight_eq_iff_of_grade` — `height x + coheight x = m` exactly when some
  maximal `η ≥ x` has grade `m`, provided no maximal `η ≥ x` has larger grade.
-/

@[expose] public section

namespace Order

variable {α : Type*} [PartialOrder α] {δ : α → ℤ}

/-- In a graded poset every strictly increasing chain gains at least one grade per step. -/
theorem length_le_of_grade (hδ : StrictMono δ) (p : LTSeries α) :
    (p.length : ℤ) ≤ δ p.last - δ p.head := by
  induction p using RelSeries.inductionOn' with
  | singleton a => simp
  | snoc p a h ih =>
    rw [RelSeries.last_snoc, RelSeries.head_snoc, RelSeries.snoc_length]
    have := hδ h
    push_cast
    omega

/-- Between comparable points of a graded poset there is a chain of the length of the grade
difference. -/
theorem exists_ltSeries_of_grade (hδ : StrictMono δ) (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1)
    {x y : α} (hxy : x ≤ y) :
    ∃ p : LTSeries α, p.head = x ∧ p.last = y ∧ (p.length : ℤ) = δ y - δ x := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = δ y - δ x := ⟨(δ y - δ x).toNat,
    Int.toNat_of_nonneg (sub_nonneg.mpr (hδ.monotone hxy))⟩
  induction n generalizing y with
  | zero =>
    have hxy' : x = y := by
      by_contra hne
      have := hδ (lt_of_le_of_ne hxy hne)
      omega
    subst hxy'
    exact ⟨RelSeries.singleton _ x, rfl, rfl, by simp⟩
  | succ n ih =>
    have hlt : x < y := lt_of_le_of_ne hxy (by rintro rfl; omega)
    -- a point of largest grade in `[x, y)`
    obtain ⟨m, ⟨z, ⟨hxz, hzy⟩, rfl⟩, hmax⟩ := Int.exists_greatest_of_bdd
      (P := fun m => ∃ z, (x ≤ z ∧ z < y) ∧ δ z = m)
      ⟨δ y, fun m ⟨z, ⟨_, hzy⟩, hm⟩ => hm ▸ (hδ hzy).le⟩ ⟨δ x, x, ⟨le_rfl, hlt⟩, rfl⟩
    have hcz : z ⋖ y := by
      refine ⟨hzy, fun w hzw hwy => ?_⟩
      have := hmax (δ w) ⟨w, ⟨hxz.trans hzw.le, hwy⟩, rfl⟩
      exact absurd (hδ hzw) (not_lt.mpr this)
    have hdz := hcov z y hcz
    obtain ⟨p, hph, hpl, hpn⟩ := ih hxz (by omega)
    refine ⟨p.snoc y (hpl ▸ hzy), by simp [hph], by simp, ?_⟩
    rw [RelSeries.snoc_length]
    push_cast
    omega

/-- In a graded poset whose minimal points have grade `0` and in which every point lies above a
minimal point, the grade is nonnegative and the height of a point is its grade. -/
theorem height_eq_of_grade (hδ : StrictMono δ) (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1)
    (hmin : ∀ a : α, IsMin a → δ a = 0) (hbelow : ∀ a : α, ∃ c ≤ a, IsMin c) (x : α) :
    0 ≤ δ x ∧ height x = ((δ x).toNat : ℕ∞) := by
  obtain ⟨c, hcx, hc⟩ := hbelow x
  have h0 : 0 ≤ δ x := hmin c hc ▸ hδ.monotone hcx
  refine ⟨h0, le_antisymm (height_le fun p hp => ?_) ?_⟩
  · obtain ⟨c', hc'p, hc'⟩ := hbelow p.head
    have h1 := length_le_of_grade hδ p
    have h2 : 0 ≤ δ p.head := hmin c' hc' ▸ hδ.monotone hc'p
    rw [hp] at h1
    exact_mod_cast (show p.length ≤ (δ x).toNat by omega)
  · obtain ⟨p, hph, hpl, hpn⟩ := exists_ltSeries_of_grade hδ hcov hcx
    rw [hmin c hc, sub_zero] at hpn
    have := length_le_height (p := p) hpl.le
    exact (by exact_mod_cast (show (δ x).toNat = p.length by omega) :
      ((δ x).toNat : ℕ∞) = p.length) ▸ this

/-- A chain from `x` to a point `η ≥ x` gives the lower bound `δ η - δ x` for the coheight. -/
private theorem toNat_le_coheight_of_grade (hδ : StrictMono δ)
    (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1) {x η : α} (hxη : x ≤ η) :
    (((δ η - δ x).toNat : ℕ) : ℕ∞) ≤ coheight x := by
  obtain ⟨p, hph, hpl, hpn⟩ := exists_ltSeries_of_grade hδ hcov hxη
  have := length_le_coheight (p := p) hph.ge
  exact (by exact_mod_cast (show (δ η - δ x).toNat = p.length by omega) :
    (((δ η - δ x).toNat : ℕ) : ℕ∞) = p.length) ▸ this

/-- A chain starting at `x` is no longer than `δ η - δ x` for some maximal `η ≥ x`. -/
private theorem exists_isMax_length_le_of_grade (hδ : StrictMono δ)
    (habove : ∀ a : α, ∃ η, a ≤ η ∧ IsMax η) {x : α} (p : LTSeries α) (hp : p.head = x) :
    ∃ η, x ≤ η ∧ IsMax η ∧ p.length ≤ (δ η - δ x).toNat := by
  obtain ⟨η, hη, hηmax⟩ := habove p.last
  have h1 := length_le_of_grade hδ p
  have h2 := hδ.monotone hη
  rw [hp] at h1
  exact ⟨η, hp ▸ p.head_le_last.trans hη, hηmax, by omega⟩

/-- In a graded poset in which every point lies below a maximal point, a chain starting at `x`
is no longer than `δ η - δ x` for some maximal `η ≥ x`, and such a length is attained. -/
theorem coheight_eq_of_grade (hδ : StrictMono δ) (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1)
    (habove : ∀ a : α, ∃ η, a ≤ η ∧ IsMax η) (x : α) :
    coheight x = ⨆ (η : α) (_ : x ≤ η ∧ IsMax η), (((δ η - δ x).toNat : ℕ) : ℕ∞) := by
  refine le_antisymm (coheight_le fun p hp => ?_) (iSup₂_le fun η ⟨hxη, _⟩ => ?_)
  · obtain ⟨η, hxη, hη, h⟩ := exists_isMax_length_le_of_grade hδ habove p hp
    exact le_trans (by exact_mod_cast h) (le_iSup₂_of_le η ⟨hxη, hη⟩ le_rfl)
  · exact toNat_le_coheight_of_grade hδ hcov hxη

/-- A chain from `x` to a point `η ≥ x` gives the lower bound `δ η - δ x` for the coheight. -/
theorem le_coheight_of_grade (hδ : StrictMono δ) (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1)
    {x η : α} (hxη : x ≤ η) : (((δ η - δ x).toNat : ℕ) : ℕ∞) ≤ coheight x :=
  toNat_le_coheight_of_grade hδ hcov hxη

/-- If every point lies below a maximal point and the maximal points above `x` have grade at
most `m`, the coheight of `x` is at most `m - δ x`. -/
theorem coheight_le_of_grade (hδ : StrictMono δ) (habove : ∀ a : α, ∃ η, a ≤ η ∧ IsMax η)
    {x : α} {m : ℤ} (hm : ∀ η, x ≤ η → IsMax η → δ η ≤ m) :
    coheight x ≤ (((m - δ x).toNat : ℕ) : ℕ∞) := by
  refine coheight_le fun p hp => ?_
  obtain ⟨η, hxη, hη, h⟩ := exists_isMax_length_le_of_grade hδ habove p hp
  have := hm η hxη hη
  exact_mod_cast h.trans (by omega : (δ η - δ x).toNat ≤ (m - δ x).toNat)

/-- In a graded poset satisfying the hypotheses of `Order.height_eq_of_grade` and
`Order.coheight_eq_of_grade`, the height and coheight of `x` add up to `m` exactly when some
maximal point above `x` has grade `m`, provided no maximal point above `x` has larger grade. -/
theorem height_add_coheight_eq_iff_of_grade (hδ : StrictMono δ)
    (hcov : ∀ a b : α, a ⋖ b → δ b = δ a + 1) (hmin : ∀ a : α, IsMin a → δ a = 0)
    (hbelow : ∀ a : α, ∃ c ≤ a, IsMin c) (habove : ∀ a : α, ∃ η, a ≤ η ∧ IsMax η) (x : α)
    (m : ℕ) (hm : ∀ η, x ≤ η → IsMax η → δ η ≤ m) :
    height x + coheight x = (m : ℕ∞) ↔ ∃ η, x ≤ η ∧ IsMax η ∧ δ η = m := by
  obtain ⟨h0, hh⟩ := height_eq_of_grade hδ hcov hmin hbelow x
  have hup := coheight_le_of_grade hδ habove hm
  obtain ⟨c, hc⟩ : ∃ c : ℕ, coheight x = c :=
    ⟨(coheight x).toNat, (ENat.coe_toNat (ne_top_of_le_ne_top (by simp) hup)).symm⟩
  rw [hc] at hup
  rw [hh, hc]
  have hup' : c ≤ ((m : ℤ) - δ x).toNat := by exact_mod_cast hup
  rw [← ENat.coe_add, Nat.cast_inj]
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨η, hxη, hη⟩ := habove x
    have h1 := hm η hxη hη
    have h2 := hne η hxη hη
    have h3 := hδ.monotone hxη
    have hup'' : c ≤ ((m - 1 : ℤ) - δ x).toNat := by
      have := coheight_le_of_grade (m := (m : ℤ) - 1) hδ habove
        (fun η' hxη' hη' => by have := hm η' hxη' hη'; have := hne η' hxη' hη'; omega)
      rw [hc] at this
      exact_mod_cast this
    omega
  · rintro ⟨η, hxη, hη, hδη⟩
    have := le_coheight_of_grade hδ hcov hxη
    rw [hc] at this
    have h' : (δ η - δ x).toNat ≤ c := by exact_mod_cast this
    have h3 := hδ.monotone hxη
    omega

end Order
