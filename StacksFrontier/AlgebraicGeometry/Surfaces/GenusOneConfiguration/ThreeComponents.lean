module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneConfiguration.Basic

/-!
# Genus-one configurations of numerical types: three components

In the three-component case connectedness leaves a triangle or a chain. Each intersecting pair
is a rank-two configuration of type `A₂`, `B₂` or `G₂`, so the square of its intersection
number is one, two or three times the product of the two weights; call that factor the level of
the pair. Eliminating the three multiplicities from the three balance relations leaves a single
identity in the weights and the intersection numbers, and rewriting it in terms of the levels
turns it into `k + l = 4` for a chain with levels `k` and `l`, and into
`k₁ + k₂ + k₃ + abc / w₁w₂w₃ = 4` for a triangle. Since every level is at least one and the
triangle's extra term is positive, the triangle forces all three levels to be one; the chain
leaves three level pairs and, with the two orientations of each pair, eight configurations. All
nine are on the list, and together they are its six three-component entries.

This file carries out the three-component case of the classification of
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/Basic.lean`.

## Main results

* `AlgebraicGeometry.NumericalType.weight_pair_level` —
  two positively intersecting minus-two indices have level `1`, `2` or `3`.
* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_componentCount_eq_three` —
  a three-component numerical type of minus-two indices is on the list.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_three` — the
  classification for three components, cases (4)-(9) of Tag 0C8T.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### The classification for three components -/

/-- The pairwise shapes available to two positively intersecting minus-two indices. -/
private lemma weight_pair_shape (T : NumericalType) (hn : 2 < T.componentCount)
    (x y : Fin T.componentCount) (hx : IsMinusTwoIndex T x) (hy : IsMinusTwoIndex T y)
    (hxy : 0 < T.intersection x y) :
    (T.weight y = T.weight x ∧ T.intersection x y = T.weight x) ∨
      (T.weight y = 2 * T.weight x ∧ T.intersection x y = 2 * T.weight x) ∨
      (T.weight x = 2 * T.weight y ∧ T.intersection x y = 2 * T.weight y) ∨
      (T.weight y = 3 * T.weight x ∧ T.intersection x y = 3 * T.weight x) ∨
      (T.weight x = 3 * T.weight y ∧ T.intersection x y = 3 * T.weight y) := by
  rcases isTwoVertexConfiguration_or_swap T hn x y hx hy hxy with h | h
  · rcases h with ⟨w, hwx, hwy, -, hc, -, -, -, -⟩ | ⟨w, hwx, hwy, -, hc, -, -, -, -⟩ |
      ⟨w, hwx, hwy, -, hc, -, -, -, -⟩
    · exact Or.inl ⟨by rw [hwx, hwy], by rw [hwx, hc]⟩
    · exact Or.inr (Or.inl ⟨by rw [hwx, hwy], by rw [hwx, hc]⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hwx, hwy], by rw [hwx, hc]⟩)))
  · rcases h with ⟨w, hwy, hwx, -, hc, -, -, -, -⟩ | ⟨w, hwy, hwx, -, hc, -, -, -, -⟩ |
      ⟨w, hwy, hwx, -, hc, -, -, -, -⟩
    · exact Or.inl ⟨by rw [hwx, hwy], by rw [T.intersection_symm, hc, hwx]⟩
    · exact Or.inr (Or.inr (Or.inl ⟨by rw [hwx, hwy], by rw [hwy, T.intersection_symm, hc]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by rw [hwx, hwy], by
        rw [hwy, T.intersection_symm, hc]⟩)))

/-- In a numerical type with exactly three components, listed as `x`, `y`, `z`, the
intersection matrix balances the multiplicities three terms at a time. -/
private lemma intersection_balance_three (T : NumericalType) (hn : T.componentCount = 3)
    (x y z : Fin T.componentCount) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (u : Fin T.componentCount) :
    T.intersection u x * T.multiplicity x + T.intersection u y * T.multiplicity y +
      T.intersection u z * T.multiplicity z = 0 := by
  classical
  have huniv : ({x, y, z} : Finset (Fin T.componentCount)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton,
      Fintype.card_fin, hn]
  have hsum := T.intersection_mul_multiplicity u
  rw [← huniv, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton] at hsum
  linarith

/-- The level of a positively intersecting pair of minus-two indices: the ratio of the square
of their intersection number to the product of their weights is `1`, `2` or `3`, and the
heavier weight is that multiple of the lighter one. -/
public lemma weight_pair_level (T : NumericalType) (hn : 2 < T.componentCount)
    (x y : Fin T.componentCount) (hx : IsMinusTwoIndex T x) (hy : IsMinusTwoIndex T y)
    (hxy : 0 < T.intersection x y) :
    ∃ k : ℤ, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      T.intersection x y ^ 2 = k * (T.weight x * T.weight y) ∧
      ((T.weight y = k * T.weight x ∧ T.intersection x y = k * T.weight x) ∨
        (T.weight x = k * T.weight y ∧ T.intersection x y = k * T.weight y)) := by
  rcases weight_pair_shape T hn x y hx hy hxy with ⟨hw, hi⟩ | ⟨hw, hi⟩ | ⟨hw, hi⟩ |
    ⟨hw, hi⟩ | ⟨hw, hi⟩
  · exact ⟨1, Or.inl rfl, by rw [hi, hw]; ring, Or.inl ⟨by rw [hw]; ring, by rw [hi]; ring⟩⟩
  · exact ⟨2, Or.inr (Or.inl rfl), by rw [hi, hw]; ring, Or.inl ⟨hw, hi⟩⟩
  · exact ⟨2, Or.inr (Or.inl rfl), by rw [hi, hw]; ring, Or.inr ⟨hw, hi⟩⟩
  · exact ⟨3, Or.inr (Or.inr rfl), by rw [hi, hw]; ring, Or.inl ⟨hw, hi⟩⟩
  · exact ⟨3, Or.inr (Or.inr rfl), by rw [hi, hw]; ring, Or.inr ⟨hw, hi⟩⟩

/-- A relabelling of three components of a numerical type with exactly three components. -/
private noncomputable def equivOfInjectiveThree (T : NumericalType) (hn : T.componentCount = 3)
    (v : Fin 3 → Fin T.componentCount) (hv : Function.Injective v) :
    Fin 3 ≃ Fin T.componentCount :=
  Equiv.ofBijective v ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hv, by simp [hn]⟩)

private lemma equivOfInjectiveThree_apply (T : NumericalType) (hn : T.componentCount = 3)
    (v : Fin 3 → Fin T.componentCount) (hv : Function.Injective v) (i : Fin 3) :
    equivOfInjectiveThree T hn v hv i = v i := rfl

/-- Three distinct components of a numerical type with three components, all minus-two indices,
whose multiplicities, weights and intersection numbers are given by an exceptional coefficient
table, form a genus-one configuration. The hypotheses are by default proved by `linarith`. -/
private lemma isGenusOneConfiguration_of_three_table (T : NumericalType)
    (hn : T.componentCount = 3) (h : ∀ i, IsMinusTwoIndex T i)
    (x y z : Fin T.componentCount) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a₁ a₂ a₃ b₁ b₂ b₃ c₁₂ c₁₃ c₂₃ m w : ℤ) (hm : 0 < m) (hw : 0 < w)
    (hp : ([a₁, a₂, a₃], [b₁, b₂, b₃], [[-2 * b₁, c₁₂, c₁₃], [c₁₂, -2 * b₂, c₂₃],
      [c₁₃, c₂₃, -2 * b₃]]) ∈ GenusOne.finitePatterns := by decide)
    (hmx : T.multiplicity x = a₁ * m := by linarith)
    (hmy : T.multiplicity y = a₂ * m := by linarith)
    (hmz : T.multiplicity z = a₃ * m := by linarith)
    (hwx : T.weight x = b₁ * w := by linarith)
    (hwy : T.weight y = b₂ * w := by linarith)
    (hwz : T.weight z = b₃ * w := by linarith)
    (hxy' : T.intersection x y = c₁₂ * w := by linarith)
    (hxz' : T.intersection x z = c₁₃ * w := by linarith)
    (hyz' : T.intersection y z = c₂₃ * w := by linarith) :
    IsGenusOneConfiguration T := by
  have hinj : Function.Injective (![x, y, z] : Fin 3 → Fin T.componentCount) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine Or.inr (Or.inl ⟨_, hp, equivOfInjectiveThree T hn _ hinj, m, w, hm, hw, ?_, ?_, ?_,
    fun _ => (h _).1⟩)
  · intro i
    fin_cases i <;> simp [equivOfInjectiveThree_apply, hmx, hmy, hmz]
  · intro i
    fin_cases i <;> simp [equivOfInjectiveThree_apply, hwx, hwy, hwz]
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [equivOfInjectiveThree_apply, (h x).2, (h y).2, (h z).2, hwx, hwy, hwz, hxy', hxz',
        hyz', T.intersection_symm y x, T.intersection_symm z y, T.intersection_symm z x] <;> ring

/-- A numerical type with three components forming a chain `x — y — z` of minus-two indices is
one of the six three-component exceptional configurations. -/
private lemma isGenusOneConfiguration_of_chain_three (T : NumericalType)
    (hn : T.componentCount = 3) (h : ∀ i, IsMinusTwoIndex T i)
    (x y z : Fin T.componentCount) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hzero : T.intersection x z = 0)
    (hapos : 0 < T.intersection x y) (hcpos : 0 < T.intersection y z) :
    IsGenusOneConfiguration T := by
  have hn2 : 2 < T.componentCount := by omega
  have hmx := T.multiplicity_pos x
  have hmy := T.multiplicity_pos y
  have hmz := T.multiplicity_pos z
  have hwx := T.weight_pos x
  have hwy := T.weight_pos y
  have hwz := T.weight_pos z
  have s1 := T.intersection_symm y x
  have s2 := T.intersection_symm z y
  have s3 := T.intersection_symm z x
  have hE1 : 2 * T.weight x * T.multiplicity x
      = T.intersection x y * T.multiplicity y := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz x
    rw [(h x).2, hzero] at hb
    linarith
  have hE3 : 2 * T.weight z * T.multiplicity z
      = T.intersection y z * T.multiplicity y := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz z
    rw [(h z).2, T.intersection_symm z x, hzero, T.intersection_symm z y] at hb
    linarith
  have hE2 : 2 * T.weight y * T.multiplicity y
      = T.intersection x y * T.multiplicity x + T.intersection y z * T.multiplicity z := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz y
    rw [(h y).2, T.intersection_symm y x] at hb
    linarith
  have hid : T.intersection x y ^ 2 * T.weight z + T.intersection y z ^ 2 * T.weight x
      = 4 * (T.weight x * T.weight y * T.weight z) := by
    have h2 : 2 * ((T.intersection x y ^ 2 * T.weight z
        + T.intersection y z ^ 2 * T.weight x
        - 4 * (T.weight x * T.weight y * T.weight z)) * T.multiplicity y) = 0 := by
      linear_combination (-4 * T.weight x * T.weight z) * hE2
        + (-2 * T.weight z * T.intersection x y) * hE1
        + (-2 * T.weight x * T.intersection y z) * hE3
    have h3 : (T.intersection x y ^ 2 * T.weight z
        + T.intersection y z ^ 2 * T.weight x
        - 4 * (T.weight x * T.weight y * T.weight z)) * T.multiplicity y = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · omega
  obtain ⟨k, hk, hka, hkor⟩ := weight_pair_level T hn2 x y (h x) (h y) hapos
  obtain ⟨l, hl, hlc, hlor⟩ := weight_pair_level T hn2 y z (h y) (h z) hcpos
  have hkl : k + l = 4 := by
    have hpos : 0 < T.weight x * T.weight y * T.weight z := by positivity
    have heq : (k + l) * (T.weight x * T.weight y * T.weight z)
        = 4 * (T.weight x * T.weight y * T.weight z) := by
      linear_combination hid - T.weight z * hka - T.weight x * hlc
    exact mul_right_cancel₀ (ne_of_gt hpos) heq
  rcases hk with rfl | rfl | rfl
  · obtain rfl : l = 3 := by omega
    have hwy : T.weight y = T.weight x := by
      rcases hkor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hax : T.intersection x y = T.weight x := by
      rcases hkor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    rcases hlor with ⟨hwz, hcy⟩ | ⟨hwy3, hcz⟩
    · rw [hax] at hE1
      rw [hwz, hcy, hwy] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := T.weight x) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = T.multiplicity x :=
        mul_left_cancel₀ (a := 6 * T.weight x) (by omega)
          (by linear_combination hE3 + 3 * T.weight x * hq)
      exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
        1 2 1 1 1 3 1 0 3 (T.multiplicity x) (T.weight x) hmx hwx
    · rw [hax] at hE1
      rw [hcz] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := T.weight x) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = 3 * T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight z) (by omega)
          (by linear_combination hE3 + 3 * T.weight z * hq)
      exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
        1 2 3 3 3 1 3 0 3 (T.multiplicity x) (T.weight z) hmx hwz
  · obtain rfl : l = 2 := by omega
    rcases hkor with ⟨hwy, hax⟩ | ⟨hwx, hay⟩ <;> rcases hlor with ⟨hwz, hcy⟩ | ⟨hwy2, hcz⟩
    · rw [hax] at hE1
      rw [hwz, hcy, hwy] at hE3
      have hq1 : T.multiplicity y = T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight x) (by omega) (by linear_combination -hE1)
      have hq2 : T.multiplicity y = 2 * T.multiplicity z :=
        mul_left_cancel₀ (a := 4 * T.weight x) (by omega) (by linear_combination -hE3)
      exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
        2 2 1 1 2 4 2 0 4 (T.multiplicity z) (T.weight x) hmz hwx
    · rw [hax] at hE1
      rw [hcz] at hE3
      have hq : T.multiplicity y = T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight x) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = T.multiplicity y :=
        mul_left_cancel₀ (a := 2 * T.weight z) (by omega) (by linear_combination hE3)
      exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
        1 1 1 1 2 1 2 0 2 (T.multiplicity x) (T.weight x) hmx hwx
    · rw [hay, hwx] at hE1
      rw [hwz, hcy] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight y) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = T.multiplicity x :=
        mul_left_cancel₀ (a := 4 * T.weight y) (by omega)
          (by linear_combination hE3 + 2 * T.weight y * hq)
      exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
        1 2 1 2 1 2 2 0 2 (T.multiplicity x) (T.weight y) hmx hwy
    · rw [hay, hwx] at hE1
      rw [hcz] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight y) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight z) (by omega)
          (by linear_combination hE3 + 2 * T.weight z * hq)
      exact isGenusOneConfiguration_of_three_table T hn h z y x hyz.symm hxz.symm hxy.symm
        2 2 1 1 2 4 2 0 4 (T.multiplicity x) (T.weight z) hmx hwz
  · obtain rfl : l = 1 := by omega
    have hwzy : T.weight z = T.weight y := by
      rcases hlor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    have hcy : T.intersection y z = T.weight y := by
      rcases hlor with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
    rcases hkor with ⟨hwy, hax⟩ | ⟨hwx, hay⟩
    · rw [hax] at hE1
      rw [hwzy, hcy, hwy] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity z :=
        mul_left_cancel₀ (a := 3 * T.weight x) (by omega) (by linear_combination -hE3)
      have hp : T.multiplicity x = 3 * T.multiplicity z :=
        mul_left_cancel₀ (a := 2 * T.weight x) (by omega)
          (by linear_combination hE1 + 3 * T.weight x * hq)
      exact isGenusOneConfiguration_of_three_table T hn h z y x hyz.symm hxz.symm hxy.symm
        1 2 3 3 3 1 3 0 3 (T.multiplicity z) (T.weight x) hmz hwx
    · rw [hay, hwx] at hE1
      rw [hwzy, hcy] at hE3
      have hq : T.multiplicity y = 2 * T.multiplicity x :=
        mul_left_cancel₀ (a := 3 * T.weight y) (by omega) (by linear_combination -hE1)
      have hr : T.multiplicity z = T.multiplicity x :=
        mul_left_cancel₀ (a := 2 * T.weight y) (by omega)
          (by linear_combination hE3 + T.weight y * hq)
      exact isGenusOneConfiguration_of_three_table T hn h z y x hyz.symm hxz.symm hxy.symm
        1 2 1 1 1 3 1 0 3 (T.multiplicity x) (T.weight y) hmx hwy

private lemma not_isolated_three (T : NumericalType)
    (u v w : Fin T.componentCount) (huv : u ≠ v) (hcover : ∀ t, t = u ∨ t = v ∨ t = w)
    (h1 : T.intersection u v = 0) (h2 : T.intersection u w = 0) : False := by
  refine T.connected ⟨{u}, ⟨u, rfl⟩, ?_, ?_⟩
  · intro huniv
    have hv : v ∈ ({u} : Set (Fin T.componentCount)) := huniv ▸ Set.mem_univ v
    exact huv (Set.mem_singleton_iff.mp hv).symm
  · intro i hi j hj
    obtain rfl : i = u := hi
    rcases hcover j with rfl | rfl | rfl
    · exact absurd rfl hj
    · exact h1
    · exact h2

/-- A numerical type with three components whose minus-two indices pairwise intersect is the
three-component affine cycle. -/
private lemma isGenusOneConfiguration_of_triangle_three (T : NumericalType)
    (hn : T.componentCount = 3) (h : ∀ i, IsMinusTwoIndex T i)
    (x y z : Fin T.componentCount) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hapos : 0 < T.intersection x y) (hbpos : 0 < T.intersection x z)
    (hcpos : 0 < T.intersection y z) :
    IsGenusOneConfiguration T := by
  have hn2 : 2 < T.componentCount := by omega
  have hmx := T.multiplicity_pos x
  have hmy := T.multiplicity_pos y
  have hmz := T.multiplicity_pos z
  have hwx := T.weight_pos x
  have hwy := T.weight_pos y
  have hwz := T.weight_pos z
  have hB1 : 2 * T.weight x * T.multiplicity x
      = T.intersection x y * T.multiplicity y + T.intersection x z * T.multiplicity z := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz x
    rw [(h x).2] at hb
    linarith
  have hB2 : 2 * T.weight y * T.multiplicity y
      = T.intersection x y * T.multiplicity x + T.intersection y z * T.multiplicity z := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz y
    rw [(h y).2, T.intersection_symm y x] at hb
    linarith
  have hB3 : 2 * T.weight z * T.multiplicity z
      = T.intersection x z * T.multiplicity x + T.intersection y z * T.multiplicity y := by
    have hb := intersection_balance_three T hn x y z hxy hxz hyz z
    rw [(h z).2, T.intersection_symm z x, T.intersection_symm z y] at hb
    linarith
  have hid : T.weight z * T.intersection x y ^ 2 + T.weight y * T.intersection x z ^ 2
      + T.weight x * T.intersection y z ^ 2
      + T.intersection x y * T.intersection x z * T.intersection y z
      = 4 * (T.weight x * T.weight y * T.weight z) := by
    have h2 : 2 * ((T.weight z * T.intersection x y ^ 2
        + T.weight y * T.intersection x z ^ 2 + T.weight x * T.intersection y z ^ 2
        + T.intersection x y * T.intersection x z * T.intersection y z
        - 4 * (T.weight x * T.weight y * T.weight z)) * T.multiplicity x) = 0 := by
      linear_combination (T.intersection y z ^ 2 - 4 * T.weight y * T.weight z) * hB1
        - (2 * T.weight z * T.intersection x y
            + T.intersection x z * T.intersection y z) * hB2
        - (2 * T.weight y * T.intersection x z
            + T.intersection x y * T.intersection y z) * hB3
    have h3 : (T.weight z * T.intersection x y ^ 2
        + T.weight y * T.intersection x z ^ 2 + T.weight x * T.intersection y z ^ 2
        + T.intersection x y * T.intersection x z * T.intersection y z
        - 4 * (T.weight x * T.weight y * T.weight z)) * T.multiplicity x = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · omega
  obtain ⟨k, hk, hka, hkor⟩ := weight_pair_level T hn2 x y (h x) (h y) hapos
  obtain ⟨k2, hk2, hkb, hk2or⟩ := weight_pair_level T hn2 x z (h x) (h z) hbpos
  obtain ⟨k3, hk3, hkc, hk3or⟩ := weight_pair_level T hn2 y z (h y) (h z) hcpos
  have habc : T.intersection x y * T.intersection x z * T.intersection y z
      = (4 - k - k2 - k3) * (T.weight x * T.weight y * T.weight z) := by
    linear_combination hid - T.weight z * hka - T.weight y * hkb - T.weight x * hkc
  have hW : 0 < T.weight x * T.weight y * T.weight z := by positivity
  have habcpos : 0 < T.intersection x y * T.intersection x z * T.intersection y z := by
    positivity
  have hsum : k + k2 + k3 < 4 := by
    by_contra hcon
    have hnn : 0 ≤ (k + k2 + k3 - 4) * (T.weight x * T.weight y * T.weight z) :=
      mul_nonneg (by omega) (le_of_lt hW)
    linarith
  have h1 : 1 ≤ k := by rcases hk with rfl | rfl | rfl <;> omega
  have h2 : 1 ≤ k2 := by rcases hk2 with rfl | rfl | rfl <;> omega
  have h3 : 1 ≤ k3 := by rcases hk3 with rfl | rfl | rfl <;> omega
  obtain rfl : k = 1 := by omega
  obtain rfl : k2 = 1 := by omega
  obtain rfl : k3 = 1 := by omega
  have hYX : T.weight y = T.weight x := by
    rcases hkor with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  have hA : T.intersection x y = T.weight x := by
    rcases hkor with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  have hZX : T.weight z = T.weight x := by
    rcases hk2or with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  have hB : T.intersection x z = T.weight x := by
    rcases hk2or with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  have hC : T.intersection y z = T.weight x := by
    rcases hk3or with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> linarith
  rw [hA, hB] at hB1
  rw [hA, hC, hYX] at hB2
  rw [hB, hC, hZX] at hB3
  have hq : T.multiplicity y = T.multiplicity x :=
    mul_left_cancel₀ (a := 3 * T.weight x) (by omega) (by linear_combination hB2 - hB1)
  have hr : T.multiplicity z = T.multiplicity x :=
    mul_left_cancel₀ (a := 3 * T.weight x) (by omega) (by linear_combination hB3 - hB1)
  exact isGenusOneConfiguration_of_three_table T hn h x y z hxy hxz hyz
    1 1 1 1 1 1 1 1 1 (T.multiplicity x) (T.weight x) hmx hwx

/-- A numerical type with three components all of whose indices are minus-two indices is one of
the six three-component exceptional configurations. -/
public lemma isGenusOneConfiguration_of_componentCount_eq_three (T : NumericalType)
    (hn : T.componentCount = 3) (h : ∀ i, IsMinusTwoIndex T i) :
    IsGenusOneConfiguration T := by
  set e : Fin 3 ≃ Fin T.componentCount := finCongr hn.symm with he
  set x : Fin T.componentCount := e 0 with hxdef
  set y : Fin T.componentCount := e 1 with hydef
  set z : Fin T.componentCount := e 2 with hzdef
  have hxy : x ≠ y := fun hq => by simpa [hxdef, hydef] using e.injective hq
  have hxz : x ≠ z := fun hq => by simpa [hxdef, hzdef] using e.injective hq
  have hyz : y ≠ z := fun hq => by simpa [hydef, hzdef] using e.injective hq
  have hcoverx : ∀ u : Fin T.componentCount, u = x ∨ u = y ∨ u = z := by
    intro u
    have hu := u.isLt
    rcases (by omega : u.val = 0 ∨ u.val = 1 ∨ u.val = 2) with h0 | h0 | h0
    · exact Or.inl (Fin.ext (by simpa [hxdef, he] using h0))
    · exact Or.inr (Or.inl (Fin.ext (by simpa [hydef, he] using h0)))
    · exact Or.inr (Or.inr (Fin.ext (by simpa [hzdef, he] using h0)))
  have hcovery : ∀ u : Fin T.componentCount, u = y ∨ u = x ∨ u = z := by
    intro u
    rcases hcoverx u with hu | hu | hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inl hu
    · exact Or.inr (Or.inr hu)
  have hcoverz : ∀ u : Fin T.componentCount, u = z ∨ u = x ∨ u = y := by
    intro u
    rcases hcoverx u with hu | hu | hu
    · exact Or.inr (Or.inl hu)
    · exact Or.inr (Or.inr hu)
    · exact Or.inl hu
  have ha := T.intersection_nonneg x y hxy
  have hb := T.intersection_nonneg x z hxz
  have hc := T.intersection_nonneg y z hyz
  by_cases hA0 : T.intersection x y = 0
  · -- `x` and `y` do not meet, so the chain is `x — z — y`.
    have hbpos : 0 < T.intersection x z := by
      rcases hb.lt_or_eq with h' | h'
      · exact h'
      · exact (not_isolated_three T x y z hxy hcoverx hA0 h'.symm).elim
    have hcpos : 0 < T.intersection y z := by
      rcases hc.lt_or_eq with h' | h'
      · exact h'
      · exact (not_isolated_three T y x z (Ne.symm hxy) hcovery
          (by rwa [T.intersection_symm y x]) h'.symm).elim
    exact isGenusOneConfiguration_of_chain_three T hn h x z y hxz hxy (Ne.symm hyz) hA0 hbpos
      (by rwa [T.intersection_symm z y])
  · have hapos : 0 < T.intersection x y := lt_of_le_of_ne ha (Ne.symm hA0)
    by_cases hB0 : T.intersection x z = 0
    · -- `x` and `z` do not meet, so the chain is `x — y — z`.
      have hcpos : 0 < T.intersection y z := by
        rcases hc.lt_or_eq with h' | h'
        · exact h'
        · exact (not_isolated_three T z x y (Ne.symm hxz) hcoverz
            (by rwa [T.intersection_symm z x])
            (by rw [T.intersection_symm z y]; exact h'.symm)).elim
      exact isGenusOneConfiguration_of_chain_three T hn h x y z hxy hxz hyz hB0 hapos hcpos
    · have hbpos : 0 < T.intersection x z := lt_of_le_of_ne hb (Ne.symm hB0)
      by_cases hC0 : T.intersection y z = 0
      · -- `y` and `z` do not meet, so the chain is `y — x — z`.
        exact isGenusOneConfiguration_of_chain_three T hn h y x z (Ne.symm hxy) hyz hxz hC0
          (by rwa [T.intersection_symm y x]) hbpos
      · exact isGenusOneConfiguration_of_triangle_three T hn h x y z hxy hxz hyz hapos hbpos
          (lt_of_le_of_ne hc (Ne.symm hC0))

/-- **Stacks Project, Tag 0C8T**, cases (4)-(9). A numerical type with three components is
minimal of genus one exactly when it is one of the six three-component exceptional
configurations: the affine cycle and the five affine chains. -/
@[stacks 0C8T "the classification for three components, cases (4)-(9)"]
public lemma isMinimal_and_genus_eq_one_iff_of_componentCount_eq_three (T : NumericalType)
    (hn : T.componentCount = 3) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T :=
  ⟨fun hT => isGenusOneConfiguration_of_componentCount_eq_three T hn
      (forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hT.1 hT.2 (by omega)),
    isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩

end AlgebraicGeometry.NumericalType
