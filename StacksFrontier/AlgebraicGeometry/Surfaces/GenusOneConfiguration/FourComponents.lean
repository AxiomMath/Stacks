module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneConfiguration.FourComponentShape
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneConfiguration.ThreeComponents

/-!
# Genus-one configurations of numerical types: four components

A connected triangle-free graph on four vertices is a chain, a star or a cycle, and the level
identity of each of those three shapes pins it down. For a chain with edge levels `k`, `l`, `l'`,
eliminating the four multiplicities from the four balance relations leaves `(4 - k)(4 - l') = 4l`,
whose only solution in levels is `(2, 1, 2)`; the two orientations of each outer edge give the three
chains of the list, one of them twice, read in either direction. For a star the same elimination
gives `k + l + l' = 4`, so one leg has level two and the other two level one, and the two
orientations of the level-two leg give the two forks. For a cycle the elimination leaves the
vanishing of the determinant of the intersection matrix, which in terms of the levels `k, l, l',
l''` of the four edges reads `w₁w₂w₃w₄ · (16 - 4(k + l + l' + l'') + kl' + ll'') = 2abcd`. The
right-hand side is positive and the bracket is `(4 - k)(4 - l') + (4 - l)(4 - l'') - 16`, which is
two when every level is one and nonpositive otherwise; so every level is one, all four weights
agree, and the balance relations make the four multiplicities agree.

The shape of the incidence graph is settled in
`StacksFrontier/AlgebraicGeometry/Surfaces/GenusOneConfiguration/FourComponentShape.lean`.

## Main results

* `AlgebraicGeometry.NumericalType.isGenusOneConfiguration_of_componentCount_eq_four` —
  a four-component numerical type of minus-two indices is on the list.
* `AlgebraicGeometry.NumericalType.isMinimal_and_genus_eq_one_iff_of_componentCount_eq_four` — the
  classification for four components, cases (10)-(15) of Tag 0C8T.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-- In a numerical type with exactly four components, the intersection matrix balances the
multiplicities four terms at a time. -/
private lemma intersection_balance_four (T : NumericalType) (hn : T.componentCount = 4)
    (x y z t : Fin T.componentCount) (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t)
    (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t) (u : Fin T.componentCount) :
    T.intersection u x * T.multiplicity x + T.intersection u y * T.multiplicity y +
      T.intersection u z * T.multiplicity z + T.intersection u t * T.multiplicity t = 0 := by
  classical
  have huniv : ({x, y, z, t} : Finset (Fin T.componentCount)) = Finset.univ := by
    refine Finset.eq_univ_of_card _ ?_
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz, hxt]),
      Finset.card_insert_of_notMem (by simp [hyz, hyt]),
      Finset.card_insert_of_notMem (by simp [hzt]), Finset.card_singleton,
      Fintype.card_fin, hn]
  have hsum := T.intersection_mul_multiplicity u
  rw [← huniv, Finset.sum_insert (by simp [hxy, hxz, hxt]),
    Finset.sum_insert (by simp [hyz, hyt]), Finset.sum_insert (by simp [hzt]),
    Finset.sum_singleton] at hsum
  linarith

/-- A relabelling of four components of a numerical type with exactly four components. -/
private noncomputable def equivOfInjectiveFour (T : NumericalType) (hn : T.componentCount = 4)
    (v : Fin 4 → Fin T.componentCount) (hv : Function.Injective v) :
    Fin 4 ≃ Fin T.componentCount :=
  Equiv.ofBijective v ((Fintype.bijective_iff_injective_and_card v).mpr ⟨hv, by simp [hn]⟩)

private lemma equivOfInjectiveFour_apply (T : NumericalType) (hn : T.componentCount = 4)
    (v : Fin 4 → Fin T.componentCount) (hv : Function.Injective v) (i : Fin 4) :
    equivOfInjectiveFour T hn v hv i = v i := rfl

/-- A four-component numerical type of minus-two indices matches a coefficient table as soon as
some ordering `x, y, z, t` of its components realises the table entry by entry. -/
private lemma matchesFinite_four (T : NumericalType) (hn : T.componentCount = 4)
    (h : ∀ i, IsMinusTwoIndex T i) (x y z t : Fin T.componentCount)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (mc wc : List ℤ) (ac : List (List ℤ)) (hlen : mc.length = 4) (m w : ℤ)
    (hm : 0 < m) (hw : 0 < w)
    (hint : ∀ i j : Fin 4, T.intersection (![x, y, z, t] i) (![x, y, z, t] j)
      = (ac.getD i.val []).getD j.val 0 * w)
    (hmul : ∀ i : Fin 4, T.multiplicity (![x, y, z, t] i) = mc.getD i.val 0 * m)
    (hwt : ∀ i : Fin 4, T.weight (![x, y, z, t] i) = wc.getD i.val 0 * w) :
    MatchesFinite T mc wc ac := by
  have hv : Function.Injective (![x, y, z, t] : Fin 4 → Fin T.componentCount) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨(finCongr hlen).trans (equivOfInjectiveFour T hn _ hv), m, w, hm, hw,
    fun i => hmul (finCongr hlen i), fun i => hwt (finCongr hlen i),
    fun i j => hint (finCongr hlen i) (finCongr hlen j), fun i => (h _).1⟩

/-- Cancelling a nonzero multiple of a weight from both sides of an equation of integers. -/
private lemma mul_weight_cancel (T : NumericalType) (c u₁ u₂ : ℤ) (q : Fin T.componentCount)
    (hc : c ≠ 0) (hq : c * T.weight q * u₁ = c * T.weight q * u₂) : u₁ = u₂ :=
  mul_left_cancel₀ (mul_ne_zero hc (ne_of_gt (T.weight_pos q))) hq

/-- The product of the weights of four components is positive. -/
private lemma weight_mul_pos_four (T : NumericalType) (x y z t : Fin T.componentCount) :
    0 < T.weight x * T.weight y * T.weight z * T.weight t :=
  mul_pos (mul_pos (mul_pos (T.weight_pos x) (T.weight_pos y)) (T.weight_pos z))
    (T.weight_pos t)

/-- Two components joined at level one have the same weight, which is their intersection number. -/
private lemma weight_eq_of_level_one {T : NumericalType} {x y : Fin T.componentCount}
    (h : (T.weight y = 1 * T.weight x ∧ T.intersection x y = 1 * T.weight x) ∨
      (T.weight x = 1 * T.weight y ∧ T.intersection x y = 1 * T.weight y)) :
    T.weight y = T.weight x ∧ T.intersection x y = T.weight x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

/-- A numerical type with four components forming a chain `x — y — z — t` of minus-two indices
is one of the three four-component affine chains. Eliminating the multiplicities from the four
balance relations leaves `(4 - k)(4 - l') = 4l` for the levels `k, l, l'` of the three edges,
which forces `(k, l, l') = (2, 1, 2)`; the two orientations of each outer edge then give the
three chains and the reversal of the first one. -/
private lemma isGenusOneConfiguration_of_chain_four (T : NumericalType)
    (hn : T.componentCount = 4) (h : ∀ i, IsMinusTwoIndex T i)
    (x y z t : Fin T.componentCount)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hxz0 : T.intersection x z = 0) (hxt0 : T.intersection x t = 0)
    (hyt0 : T.intersection y t = 0)
    (hapos : 0 < T.intersection x y) (hbpos : 0 < T.intersection y z)
    (hcpos : 0 < T.intersection z t) :
    IsGenusOneConfiguration T := by
  have hn2 : 2 < T.componentCount := by omega
  have hzx0 : T.intersection z x = 0 := by rwa [T.intersection_symm]
  have htx0 : T.intersection t x = 0 := by rwa [T.intersection_symm]
  have hty0 : T.intersection t y = 0 := by rwa [T.intersection_symm]
  have hyx : T.intersection y x = T.intersection x y := T.intersection_symm y x
  have hzy : T.intersection z y = T.intersection y z := T.intersection_symm z y
  have htz : T.intersection t z = T.intersection z t := T.intersection_symm t z
  have hE1 : 2 * T.weight x * T.multiplicity x
      = T.intersection x y * T.multiplicity y := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt x
    rw [(h x).2, hxz0, hxt0] at hb
    linarith
  have hE2 : 2 * T.weight y * T.multiplicity y
      = T.intersection x y * T.multiplicity x + T.intersection y z * T.multiplicity z := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt y
    rw [(h y).2, hyx, hyt0] at hb
    linarith
  have hE3 : 2 * T.weight z * T.multiplicity z
      = T.intersection y z * T.multiplicity y + T.intersection z t * T.multiplicity t := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt z
    rw [(h z).2, hzx0, hzy] at hb
    linarith
  have hE4 : 2 * T.weight t * T.multiplicity t
      = T.intersection z t * T.multiplicity z := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt t
    rw [(h t).2, htx0, hty0, htz] at hb
    linarith
  have hP : T.multiplicity x * (4 * T.weight x * T.weight y - T.intersection x y ^ 2)
      = T.intersection x y * T.intersection y z * T.multiplicity z := by
    linear_combination (2 * T.weight y) * hE1 + T.intersection x y * hE2
  have hQ : T.multiplicity t * (4 * T.weight z * T.weight t - T.intersection z t ^ 2)
      = T.intersection y z * T.intersection z t * T.multiplicity y := by
    linear_combination (2 * T.weight z) * hE4 + T.intersection z t * hE3
  have hP' : T.multiplicity x * (4 * T.weight x * T.weight y - T.intersection x y ^ 2)
        * T.intersection z t
      = 2 * T.intersection x y * T.intersection y z * T.weight t * T.multiplicity t := by
    linear_combination T.intersection z t * hP
      - (T.intersection x y * T.intersection y z) * hE4
  have hQ' : T.multiplicity t * (4 * T.weight z * T.weight t - T.intersection z t ^ 2)
        * T.intersection x y
      = 2 * T.intersection y z * T.intersection z t * T.weight x * T.multiplicity x := by
    linear_combination T.intersection x y * hQ
      - (T.intersection y z * T.intersection z t) * hE1
  have hprod : (T.intersection x y * T.intersection z t
        * T.multiplicity x * T.multiplicity t)
        * ((4 * T.weight x * T.weight y - T.intersection x y ^ 2)
          * (4 * T.weight z * T.weight t - T.intersection z t ^ 2))
      = (T.intersection x y * T.intersection z t * T.multiplicity x * T.multiplicity t)
        * (4 * T.intersection y z ^ 2 * T.weight x * T.weight t) := by
    linear_combination (T.multiplicity t
        * (4 * T.weight z * T.weight t - T.intersection z t ^ 2)
        * T.intersection x y) * hP'
      + (2 * T.intersection x y * T.intersection y z * T.weight t * T.multiplicity t) * hQ'
  have hposfac : 0 < T.intersection x y * T.intersection z t
      * T.multiplicity x * T.multiplicity t :=
    mul_pos (mul_pos (mul_pos hapos hcpos) (T.multiplicity_pos x)) (T.multiplicity_pos t)
  have hPQ : (4 * T.weight x * T.weight y - T.intersection x y ^ 2)
      * (4 * T.weight z * T.weight t - T.intersection z t ^ 2)
      = 4 * T.intersection y z ^ 2 * T.weight x * T.weight t :=
    mul_left_cancel₀ (ne_of_gt hposfac) hprod
  obtain ⟨k, hk, hka, hkor⟩ := weight_pair_level T hn2 x y (h x) (h y) hapos
  obtain ⟨l, hl, hlb, hlor⟩ := weight_pair_level T hn2 y z (h y) (h z) hbpos
  obtain ⟨p, hp, hpc, hpor⟩ := weight_pair_level T hn2 z t (h z) (h t) hcpos
  rw [hka, hlb, hpc] at hPQ
  have hlevel : (4 - k) * (4 - p) = 4 * l :=
    mul_right_cancel₀ (weight_mul_pos_four T x y z t).ne' (by linear_combination hPQ)
  obtain ⟨rfl, rfl, rfl⟩ : k = 2 ∧ l = 1 ∧ p = 2 := by
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
      rcases hp with rfl | rfl | rfl <;> omega
  obtain ⟨hmid, hmidb⟩ := weight_eq_of_level_one hlor
  have h2ne : (2 : ℤ) ≠ 0 := by norm_num
  have h4ne : (4 : ℤ) ≠ 0 := by norm_num
  rcases hkor with ⟨hw1, ha1⟩ | ⟨hw1, ha1⟩
  · rcases hpor with ⟨hw2, hc2⟩ | ⟨hw2, hc2⟩
    · -- the chain of weights `(w, 2w, 2w, 4w)`
      have hwz : T.weight z = 2 * T.weight x := by linarith
      have hwt4 : T.weight t = 4 * T.weight x := by linarith
      have hbv : T.intersection y z = 2 * T.weight x := by linarith
      have hcv : T.intersection z t = 4 * T.weight x := by linarith
      simp only [ha1, hbv, hcv, hw1, hwt4] at hE1 hE2 hE4
      have hmxy : T.multiplicity x = T.multiplicity y :=
        mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE1)
      have hmzt : T.multiplicity z = 2 * T.multiplicity t :=
        mul_weight_cancel T 4 _ _ x h4ne (by linear_combination -hE4)
      have hmzx : T.multiplicity z = T.multiplicity x :=
        mul_weight_cancel T 2 _ _ x h2ne (by linear_combination -hE2 - 4 * T.weight x * hmxy)
      refine Or.inr (Or.inl ⟨([2, 2, 2, 1], [1, 2, 2, 4],
        [[-2, 2, 0, 0], [2, -4, 2, 0], [0, 2, -4, 4], [0, 0, 4, -8]]), by decide, ?_⟩)
      refine matchesFinite_four T hn h x y z t hxy hxz hxt hyz hyt hzt _ _ _ rfl
        (T.multiplicity t) (T.weight x) (T.multiplicity_pos t) (T.weight_pos x) ?_ ?_ ?_
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxz0, hxt0, hyt0, hzx0, htx0, hty0, hyx, hzy, htz,
            (h x).2, (h y).2, (h z).2, (h t).2, ha1, hbv, hcv, hw1, hwz, hwt4] <;>
          linarith
      all_goals
        intro i
        fin_cases i <;> simp <;> linarith
    · -- the chain of weights `(w, 2w, 2w, w)`
      have hwz : T.weight z = 2 * T.weight x := by linarith
      have hwt1 : T.weight t = T.weight x := by linarith
      have hbv : T.intersection y z = 2 * T.weight x := by linarith
      have hcv : T.intersection z t = 2 * T.weight x := by linarith
      simp only [ha1, hbv, hcv, hw1, hwt1] at hE1 hE2 hE4
      have hmxy : T.multiplicity x = T.multiplicity y :=
        mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE1)
      have hmtz : T.multiplicity t = T.multiplicity z :=
        mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE4)
      have hmzx : T.multiplicity z = T.multiplicity x :=
        mul_weight_cancel T 2 _ _ x h2ne (by linear_combination -hE2 - 4 * T.weight x * hmxy)
      refine Or.inr (Or.inl ⟨([1, 1, 1, 1], [1, 2, 2, 1],
        [[-2, 2, 0, 0], [2, -4, 2, 0], [0, 2, -4, 2], [0, 0, 2, -2]]), by decide, ?_⟩)
      refine matchesFinite_four T hn h x y z t hxy hxz hxt hyz hyt hzt _ _ _ rfl
        (T.multiplicity x) (T.weight x) (T.multiplicity_pos x) (T.weight_pos x) ?_ ?_ ?_
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxz0, hxt0, hyt0, hzx0, htx0, hty0, hyx, hzy, htz,
            (h x).2, (h y).2, (h z).2, (h t).2, ha1, hbv, hcv, hw1, hwz, hwt1] <;>
          linarith
      all_goals
        intro i
        fin_cases i <;> simp <;> linarith
  · rcases hpor with ⟨hw2, hc2⟩ | ⟨hw2, hc2⟩
    · -- the chain of weights `(2w, w, w, 2w)`
      have hwt2 : T.weight t = 2 * T.weight y := by linarith
      have hcv : T.intersection z t = 2 * T.weight y := by linarith
      simp only [ha1, hmidb, hcv, hw1, hwt2] at hE1 hE2 hE4
      have hmy : T.multiplicity y = 2 * T.multiplicity x :=
        mul_weight_cancel T 2 _ _ y h2ne (by linear_combination -hE1)
      have hmz : T.multiplicity z = 2 * T.multiplicity t :=
        mul_weight_cancel T 2 _ _ y h2ne (by linear_combination -hE4)
      have hmt : T.multiplicity t = T.multiplicity x := by
        refine mul_weight_cancel T 2 _ _ y h2ne ?_
        linear_combination -hE2 + 2 * T.weight y * hmy - T.weight y * hmz
      refine Or.inr (Or.inl ⟨([1, 2, 2, 1], [2, 1, 1, 2],
        [[-4, 2, 0, 0], [2, -2, 1, 0], [0, 1, -2, 2], [0, 0, 2, -4]]), by decide, ?_⟩)
      refine matchesFinite_four T hn h x y z t hxy hxz hxt hyz hyt hzt _ _ _ rfl
        (T.multiplicity x) (T.weight y) (T.multiplicity_pos x) (T.weight_pos y) ?_ ?_ ?_
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxz0, hxt0, hyt0, hzx0, htx0, hty0, hyx, hzy, htz,
            (h x).2, (h y).2, (h z).2, (h t).2, ha1, hmidb, hcv, hw1, hmid, hwt2] <;>
          linarith
      all_goals
        intro i
        fin_cases i <;> simp <;> linarith
    · -- the chain of weights `(4w, 2w, 2w, w)`, the first chain read backwards
      have hwy2 : T.weight y = 2 * T.weight t := by linarith
      have hwx4 : T.weight x = 4 * T.weight t := by linarith
      have hav : T.intersection x y = 4 * T.weight t := by linarith
      have hbv : T.intersection y z = 2 * T.weight t := by linarith
      simp only [hav, hbv, hc2, hwx4, hwy2] at hE1 hE2 hE4
      have hmy : T.multiplicity y = 2 * T.multiplicity x :=
        mul_weight_cancel T 4 _ _ t h4ne (by linear_combination -hE1)
      have hmt : T.multiplicity t = T.multiplicity z :=
        mul_weight_cancel T 2 _ _ t h2ne (by linear_combination hE4)
      have hmz : T.multiplicity z = 2 * T.multiplicity x :=
        mul_weight_cancel T 2 _ _ t h2ne (by linear_combination -hE2 + 4 * T.weight t * hmy)
      refine Or.inr (Or.inl ⟨([2, 2, 2, 1], [1, 2, 2, 4],
        [[-2, 2, 0, 0], [2, -4, 2, 0], [0, 2, -4, 4], [0, 0, 4, -8]]), by decide, ?_⟩)
      refine matchesFinite_four T hn h t z y x hzt.symm hyt.symm hxt.symm hyz.symm hxz.symm
        hxy.symm _ _ _ rfl (T.multiplicity x) (T.weight t) (T.multiplicity_pos x)
        (T.weight_pos t) ?_ ?_ ?_
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [hxz0, hxt0, hyt0, hzx0, htx0, hty0, hyx, hzy, htz,
            (h x).2, (h y).2, (h z).2, (h t).2, hav, hbv, hc2, hwx4, hwy2, hw2] <;>
          linarith
      all_goals
        intro i
        fin_cases i <;> simp <;> linarith

/-- Eliminating the four multiplicities from the four balance relations of a cycle leaves one
identity in its weights and intersection numbers: the vanishing of the determinant of the
intersection matrix of a four-cycle. -/
private lemma cycle_four_identity {wx wy wz wt a b c d mx my mz mt : ℤ}
    (hmzpos : 0 < mz) (hmtpos : 0 < mt)
    (hE1 : 2 * wx * mx = a * my + d * mt)
    (hE2 : 2 * wy * my = a * mx + b * mz)
    (hE3 : 2 * wz * mz = b * my + c * mt)
    (hE4 : 2 * wt * mt = d * mx + c * mz)
    (hPpos : 0 < 4 * wx * wy - a ^ 2) :
    16 * (wx * wy * wz * wt) - 4 * wx * wy * c ^ 2 - 4 * wx * wt * b ^ 2
      - 4 * wz * wt * a ^ 2 - 4 * wy * wz * d ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2
      - 2 * (a * b * c * d) = 0 := by
  have hPx : (4 * wx * wy - a ^ 2) * mx = 2 * wy * d * mt + a * b * mz := by
    linear_combination (2 * wy) * hE1 + a * hE2
  have hPy : (4 * wx * wy - a ^ 2) * my = a * d * mt + 2 * wx * b * mz := by
    linear_combination (2 * wx) * hE2 + a * hE1
  have hR : mz * (2 * wz * (4 * wx * wy - a ^ 2) - 2 * wx * b ^ 2)
      = mt * (a * b * d + c * (4 * wx * wy - a ^ 2)) := by
    linear_combination (4 * wx * wy - a ^ 2) * hE3 + b * hPy
  have hS : mt * (2 * wt * (4 * wx * wy - a ^ 2) - 2 * wy * d ^ 2)
      = mz * (a * b * d + c * (4 * wx * wy - a ^ 2)) := by
    linear_combination (4 * wx * wy - a ^ 2) * hE4 + d * hPx
  have hmul : (mz * mt) * ((2 * wz * (4 * wx * wy - a ^ 2) - 2 * wx * b ^ 2)
        * (2 * wt * (4 * wx * wy - a ^ 2) - 2 * wy * d ^ 2))
      = (mz * mt) * ((a * b * d + c * (4 * wx * wy - a ^ 2)) ^ 2) := by
    linear_combination (mt * (2 * wt * (4 * wx * wy - a ^ 2) - 2 * wy * d ^ 2)) * hR
      + (mt * (a * b * d + c * (4 * wx * wy - a ^ 2))) * hS
  have hABC := mul_left_cancel₀ (ne_of_gt (mul_pos hmzpos hmtpos)) hmul
  have hdet : (4 * wx * wy - a ^ 2)
      * (16 * (wx * wy * wz * wt) - 4 * wx * wy * c ^ 2 - 4 * wx * wt * b ^ 2
        - 4 * wz * wt * a ^ 2 - 4 * wy * wz * d ^ 2 + a ^ 2 * c ^ 2 + b ^ 2 * d ^ 2
        - 2 * (a * b * c * d)) = 0 := by
    linear_combination hABC
  rcases mul_eq_zero.mp hdet with h' | h'
  · exact absurd h' (ne_of_gt hPpos)
  · exact h'

/-- Every level of a four-cycle of minus-two indices is one. Writing the cycle identity in terms
of the levels `k, l, p, q` of its four edges turns it into `W · F = 2abcd` with
`F = (4 - k)(4 - p) + (4 - l)(4 - q) - 16`; the right-hand side is positive, and each factor is
at most three, so the only way for `F` to be positive is for all four levels to be one. -/
private lemma cycle_four_levels {k l p q W S : ℤ} (hWpos : 0 < W) (hSpos : 0 < S)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hl : l = 1 ∨ l = 2 ∨ l = 3)
    (hp : p = 1 ∨ p = 2 ∨ p = 3) (hq : q = 1 ∨ q = 2 ∨ q = 3)
    (hWF : W * (16 - 4 * (k + l + p + q) + k * p + l * q) = 2 * S) :
    k = 1 ∧ l = 1 ∧ p = 1 ∧ q = 1 := by
  have hFpos : (0 : ℤ) < 16 - 4 * (k + l + p + q) + k * p + l * q := by
    by_contra hcon
    rw [not_lt] at hcon
    have hle := mul_le_mul_of_nonneg_left hcon hWpos.le
    rw [mul_zero] at hle
    linarith
  rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> omega

/-- A numerical type with four components forming a cycle `x — y — z — t — x` of minus-two
indices is the four-component affine cycle: all four levels are one, so all four weights agree
and the four balance relations make all four multiplicities agree. -/
private lemma isGenusOneConfiguration_of_cycle_four (T : NumericalType)
    (hn : T.componentCount = 4) (h : ∀ i, IsMinusTwoIndex T i)
    (x y z t : Fin T.componentCount)
    (hxy : x ≠ y) (hxz : x ≠ z) (hxt : x ≠ t) (hyz : y ≠ z) (hyt : y ≠ t) (hzt : z ≠ t)
    (hxz0 : T.intersection x z = 0) (hyt0 : T.intersection y t = 0)
    (hapos : 0 < T.intersection x y) (hbpos : 0 < T.intersection y z)
    (hcpos : 0 < T.intersection z t) (hdpos : 0 < T.intersection x t) :
    IsGenusOneConfiguration T := by
  have hn2 : 2 < T.componentCount := by omega
  have hzx0 : T.intersection z x = 0 := by rwa [T.intersection_symm]
  have hty0 : T.intersection t y = 0 := by rwa [T.intersection_symm]
  have hyx : T.intersection y x = T.intersection x y := T.intersection_symm y x
  have hzy : T.intersection z y = T.intersection y z := T.intersection_symm z y
  have htz : T.intersection t z = T.intersection z t := T.intersection_symm t z
  have htx : T.intersection t x = T.intersection x t := T.intersection_symm t x
  have hE1 : 2 * T.weight x * T.multiplicity x
      = T.intersection x y * T.multiplicity y + T.intersection x t * T.multiplicity t := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt x
    rw [(h x).2, hxz0] at hb
    linarith
  have hE2 : 2 * T.weight y * T.multiplicity y
      = T.intersection x y * T.multiplicity x + T.intersection y z * T.multiplicity z := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt y
    rw [(h y).2, hyx, hyt0] at hb
    linarith
  have hE3 : 2 * T.weight z * T.multiplicity z
      = T.intersection y z * T.multiplicity y + T.intersection z t * T.multiplicity t := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt z
    rw [(h z).2, hzx0, hzy] at hb
    linarith
  have hE4 : 2 * T.weight t * T.multiplicity t
      = T.intersection x t * T.multiplicity x + T.intersection z t * T.multiplicity z := by
    have hb := intersection_balance_four T hn x y z t hxy hxz hxt hyz hyt hzt t
    rw [(h t).2, htx, hty0, htz] at hb
    linarith
  obtain ⟨k, hk, hka, hkor⟩ := weight_pair_level T hn2 x y (h x) (h y) hapos
  obtain ⟨l, hl, hlb, hlor⟩ := weight_pair_level T hn2 y z (h y) (h z) hbpos
  obtain ⟨p, hp, hpc, hpor⟩ := weight_pair_level T hn2 z t (h z) (h t) hcpos
  obtain ⟨q, hq, hqd, hqor⟩ := weight_pair_level T hn2 x t (h x) (h t) hdpos
  have hPpos : (0 : ℤ) < 4 * T.weight x * T.weight y - T.intersection x y ^ 2 := by
    have hxy' : (0 : ℤ) < T.weight x * T.weight y :=
      mul_pos (T.weight_pos x) (T.weight_pos y)
    rw [hka]
    rcases hk with rfl | rfl | rfl <;> linarith only [hxy']
  have hDzero := cycle_four_identity (T.multiplicity_pos z) (T.multiplicity_pos t)
    hE1 hE2 hE3 hE4 hPpos
  rw [hka, hlb, hpc, hqd] at hDzero
  have hWF : (T.weight x * T.weight y * T.weight z * T.weight t)
      * (16 - 4 * (k + l + p + q) + k * p + l * q)
      = 2 * (T.intersection x y * T.intersection y z * T.intersection z t
        * T.intersection x t) := by
    linear_combination hDzero
  obtain ⟨rfl, rfl, rfl, rfl⟩ :=
    cycle_four_levels (weight_mul_pos_four T x y z t)
      (mul_pos (mul_pos (mul_pos hapos hbpos) hcpos) hdpos) hk hl hp hq hWF
  obtain ⟨hwy, hav⟩ := weight_eq_of_level_one hkor
  obtain ⟨hwz, hbv⟩ := weight_eq_of_level_one hlor
  obtain ⟨hwt, hcv⟩ := weight_eq_of_level_one hpor
  obtain ⟨-, hdv⟩ := weight_eq_of_level_one hqor
  have h2ne : (2 : ℤ) ≠ 0 := by norm_num
  simp only [hav, hbv, hcv, hdv, hwy, hwz, hwt] at hE1 hE2 hE3 hE4
  have hmxz : T.multiplicity x = T.multiplicity z :=
    mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE1 - hE3)
  have hmy : T.multiplicity y = T.multiplicity x :=
    mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE2 - T.weight x * hmxz)
  have hmt : T.multiplicity t = T.multiplicity x :=
    mul_weight_cancel T 2 _ _ x h2ne (by linear_combination hE4 - T.weight x * hmxz)
  refine Or.inr (Or.inl ⟨([1, 1, 1, 1], [1, 1, 1, 1],
    [[-2, 1, 0, 1], [1, -2, 1, 0], [0, 1, -2, 1], [1, 0, 1, -2]]), by decide, ?_⟩)
  refine matchesFinite_four T hn h x y z t hxy hxz hxt hyz hyt hzt _ _ _ rfl
    (T.multiplicity x) (T.weight x) (T.multiplicity_pos x) (T.weight_pos x) ?_ ?_ ?_
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hxz0, hyt0, hzx0, hty0, hyx, hzy, htz, htx,
        (h x).2, (h y).2, (h z).2, (h t).2, hav, hbv, hcv, hdv, hwy, hwz, hwt]
  all_goals
    intro i
    fin_cases i <;> simp <;> linarith

/-- A numerical type with four components forming a star with centre `c` and legs of levels
one, one and two is one of the two four-component affine forks, according to the orientation of
the level-two leg. -/
private lemma isGenusOneConfiguration_of_star_four_aux (T : NumericalType)
    (hn : T.componentCount = 4) (h : ∀ i, IsMinusTwoIndex T i)
    (c u v s : Fin T.componentCount)
    (hcu : c ≠ u) (hcv : c ≠ v) (hcs : c ≠ s) (huv : u ≠ v) (hus : u ≠ s) (hvs : v ≠ s)
    (huv0 : T.intersection u v = 0) (hus0 : T.intersection u s = 0)
    (hvs0 : T.intersection v s = 0)
    (hwu : T.weight u = T.weight c) (hau : T.intersection c u = T.weight c)
    (hwv : T.weight v = T.weight c) (hav : T.intersection c v = T.weight c)
    (hleg : (T.weight s = 2 * T.weight c ∧ T.intersection c s = 2 * T.weight c) ∨
      (T.weight c = 2 * T.weight s ∧ T.intersection c s = 2 * T.weight s)) :
    IsGenusOneConfiguration T := by
  have hvu0 : T.intersection v u = 0 := by rwa [T.intersection_symm]
  have hsu0 : T.intersection s u = 0 := by rwa [T.intersection_symm]
  have hsv0 : T.intersection s v = 0 := by rwa [T.intersection_symm]
  have huc : T.intersection u c = T.intersection c u := T.intersection_symm u c
  have hvc : T.intersection v c = T.intersection c v := T.intersection_symm v c
  have hsc : T.intersection s c = T.intersection c s := T.intersection_symm s c
  have hEu : 2 * T.weight u * T.multiplicity u
      = T.intersection c u * T.multiplicity c := by
    have hb := intersection_balance_four T hn c u v s hcu hcv hcs huv hus hvs u
    rw [(h u).2, huc, huv0, hus0] at hb
    linarith
  have hEv : 2 * T.weight v * T.multiplicity v
      = T.intersection c v * T.multiplicity c := by
    have hb := intersection_balance_four T hn c u v s hcu hcv hcs huv hus hvs v
    rw [(h v).2, hvc, hvu0, hvs0] at hb
    linarith
  have hEs : 2 * T.weight s * T.multiplicity s
      = T.intersection c s * T.multiplicity c := by
    have hb := intersection_balance_four T hn c u v s hcu hcv hcs huv hus hvs s
    rw [(h s).2, hsc, hsu0, hsv0] at hb
    linarith
  have h2ne : (2 : ℤ) ≠ 0 := by norm_num
  rw [hwu, hau] at hEu
  rw [hwv, hav] at hEv
  have hmc : T.multiplicity c = 2 * T.multiplicity u :=
    mul_weight_cancel T 2 _ _ c h2ne (by linear_combination -2 * hEu)
  have hmv : T.multiplicity v = T.multiplicity u :=
    mul_weight_cancel T 2 _ _ c h2ne (by linear_combination hEv + T.weight c * hmc)
  rcases hleg with ⟨hws, hes⟩ | ⟨hwc, hes⟩
  · rw [hws, hes] at hEs
    have hms : T.multiplicity s = T.multiplicity u :=
      mul_weight_cancel T 4 _ _ c (by norm_num) (by linear_combination hEs + 2 * T.weight c * hmc)
    refine Or.inr (Or.inl ⟨([2, 1, 1, 1], [1, 1, 1, 2],
      [[-2, 1, 1, 2], [1, -2, 0, 0], [1, 0, -2, 0], [2, 0, 0, -4]]), by decide, ?_⟩)
    refine matchesFinite_four T hn h c u v s hcu hcv hcs huv hus hvs _ _ _ rfl
      (T.multiplicity u) (T.weight c) (T.multiplicity_pos u) (T.weight_pos c) ?_ ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [huv0, hus0, hvs0, hvu0, hsu0, hsv0, huc, hvc, hsc,
          (h c).2, (h u).2, (h v).2, (h s).2, hau, hav, hes, hwu, hwv, hws]
      all_goals linarith
    all_goals
      intro i
      fin_cases i <;> simp <;> linarith
  · rw [hes] at hEs
    have hms : T.multiplicity s = 2 * T.multiplicity u :=
      mul_weight_cancel T 2 _ _ s (by norm_num) (by linear_combination hEs + 2 * T.weight s * hmc)
    refine Or.inr (Or.inl ⟨([2, 1, 1, 2], [2, 2, 2, 1],
      [[-4, 2, 2, 2], [2, -4, 0, 0], [2, 0, -4, 0], [2, 0, 0, -2]]), by decide, ?_⟩)
    refine matchesFinite_four T hn h c u v s hcu hcv hcs huv hus hvs _ _ _ rfl
      (T.multiplicity u) (T.weight s) (T.multiplicity_pos u) (T.weight_pos s) ?_ ?_ ?_
    · intro i j
      fin_cases i <;> fin_cases j <;>
        simp [huv0, hus0, hvs0, hvu0, hsu0, hsv0, huc, hvc, hsc,
          (h c).2, (h u).2, (h v).2, (h s).2, hau, hav, hes, hwu, hwv] <;>
        linarith
    all_goals
      intro i
      fin_cases i <;> simp <;> linarith

/-- A numerical type with four components forming a star of minus-two indices with centre `c`
is one of the two four-component affine forks: the three legs have levels summing to four, so
two of them have level one and the third level two. -/
private lemma isGenusOneConfiguration_of_star_four (T : NumericalType)
    (hn : T.componentCount = 4) (h : ∀ i, IsMinusTwoIndex T i)
    (c x y z : Fin T.componentCount)
    (hcx : c ≠ x) (hcy : c ≠ y) (hcz : c ≠ z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hxy0 : T.intersection x y = 0) (hxz0 : T.intersection x z = 0)
    (hyz0 : T.intersection y z = 0)
    (hapos : 0 < T.intersection c x) (hbpos : 0 < T.intersection c y)
    (hepos : 0 < T.intersection c z) :
    IsGenusOneConfiguration T := by
  have hn2 : 2 < T.componentCount := by omega
  have hyx0 : T.intersection y x = 0 := by rwa [T.intersection_symm]
  have hzx0 : T.intersection z x = 0 := by rwa [T.intersection_symm]
  have hzy0 : T.intersection z y = 0 := by rwa [T.intersection_symm]
  have hE0 : 2 * T.weight c * T.multiplicity c
      = T.intersection c x * T.multiplicity x + T.intersection c y * T.multiplicity y
        + T.intersection c z * T.multiplicity z := by
    have hb := intersection_balance_four T hn c x y z hcx hcy hcz hxy hxz hyz c
    rw [(h c).2] at hb
    linarith
  have hEx : 2 * T.weight x * T.multiplicity x
      = T.intersection c x * T.multiplicity c := by
    have hb := intersection_balance_four T hn c x y z hcx hcy hcz hxy hxz hyz x
    rw [(h x).2, T.intersection_symm x c, hxy0, hxz0] at hb
    linarith
  have hEy : 2 * T.weight y * T.multiplicity y
      = T.intersection c y * T.multiplicity c := by
    have hb := intersection_balance_four T hn c x y z hcx hcy hcz hxy hxz hyz y
    rw [(h y).2, T.intersection_symm y c, hyx0, hyz0] at hb
    linarith
  have hEz : 2 * T.weight z * T.multiplicity z
      = T.intersection c z * T.multiplicity c := by
    have hb := intersection_balance_four T hn c x y z hcx hcy hcz hxy hxz hyz z
    rw [(h z).2, T.intersection_symm z c, hzx0, hzy0] at hb
    linarith
  have hkey0 : (4 * T.multiplicity c)
        * (4 * T.weight c * T.weight x * T.weight y * T.weight z)
      = (4 * T.multiplicity c)
        * (T.intersection c x ^ 2 * T.weight y * T.weight z
          + T.intersection c y ^ 2 * T.weight x * T.weight z
          + T.intersection c z ^ 2 * T.weight x * T.weight y) := by
    linear_combination (8 * T.weight x * T.weight y * T.weight z) * hE0
      + (4 * T.weight y * T.weight z * T.intersection c x) * hEx
      + (4 * T.weight x * T.weight z * T.intersection c y) * hEy
      + (4 * T.weight x * T.weight y * T.intersection c z) * hEz
  have hkey : 4 * T.weight c * T.weight x * T.weight y * T.weight z
      = T.intersection c x ^ 2 * T.weight y * T.weight z
        + T.intersection c y ^ 2 * T.weight x * T.weight z
        + T.intersection c z ^ 2 * T.weight x * T.weight y :=
    mul_left_cancel₀ (ne_of_gt (by linarith [T.multiplicity_pos c] :
      (0 : ℤ) < 4 * T.multiplicity c)) hkey0
  obtain ⟨k, hk, hka, hkor⟩ := weight_pair_level T hn2 c x (h c) (h x) hapos
  obtain ⟨l, hl, hlb, hlor⟩ := weight_pair_level T hn2 c y (h c) (h y) hbpos
  obtain ⟨p, hp, hpe, hpor⟩ := weight_pair_level T hn2 c z (h c) (h z) hepos
  rw [hka, hlb, hpe] at hkey
  have hsum : k + l + p = 4 :=
    mul_right_cancel₀ (weight_mul_pos_four T c x y z).ne' (by linear_combination -hkey)
  obtain hcase | hcase | hcase :
      (k = 2 ∧ l = 1 ∧ p = 1) ∨ (k = 1 ∧ l = 2 ∧ p = 1) ∨ (k = 1 ∧ l = 1 ∧ p = 2) := by
    rcases hk with rfl | rfl | rfl <;> rcases hl with rfl | rfl | rfl <;>
      rcases hp with rfl | rfl | rfl <;> omega
  · obtain ⟨rfl, rfl, rfl⟩ := hcase
    obtain ⟨hwy, hby⟩ := weight_eq_of_level_one hlor
    obtain ⟨hwz, hez⟩ := weight_eq_of_level_one hpor
    exact isGenusOneConfiguration_of_star_four_aux T hn h c y z x hcy hcz hcx hyz
      (Ne.symm hxy) (Ne.symm hxz) hyz0 hyx0 hzx0 hwy hby hwz hez hkor
  · obtain ⟨rfl, rfl, rfl⟩ := hcase
    obtain ⟨hwx, hax⟩ := weight_eq_of_level_one hkor
    obtain ⟨hwz, hez⟩ := weight_eq_of_level_one hpor
    exact isGenusOneConfiguration_of_star_four_aux T hn h c x z y hcx hcz hcy hxz
      hxy (Ne.symm hyz) hxz0 hxy0 hzy0 hwx hax hwz hez hlor
  · obtain ⟨rfl, rfl, rfl⟩ := hcase
    obtain ⟨hwx, hax⟩ := weight_eq_of_level_one hkor
    obtain ⟨hwy, hby⟩ := weight_eq_of_level_one hlor
    exact isGenusOneConfiguration_of_star_four_aux T hn h c x y z hcx hcy hcz hxy
      hxz hyz hxy0 hxz0 hyz0 hwx hax hwy hby hpor

/-- A numerical type with four components all of whose indices are minus-two indices is one of
the six four-component exceptional configurations: the affine cycle, the three affine chains and
the two affine forks. -/
public lemma isGenusOneConfiguration_of_componentCount_eq_four (T : NumericalType)
    (hn : T.componentCount = 4) (h : ∀ i, IsMinusTwoIndex T i) :
    IsGenusOneConfiguration T := by
  set e : Fin 4 ≃ Fin T.componentCount := finCongr hn.symm with he
  have hne : ∀ i j : Fin 4, i ≠ j → e i ≠ e j := fun i j hij hq => hij (e.injective hq)
  have hzs : ∀ i j : Fin 4, T.intersection (e i) (e j) = 0 →
      T.intersection (e j) (e i) = 0 := fun i j hij => by rwa [T.intersection_symm]
  have hps : ∀ i j : Fin 4, 0 < T.intersection (e i) (e j) →
      0 < T.intersection (e j) (e i) := fun i j hij => by rwa [T.intersection_symm]
  rcases four_vertex_shape_of_minusTwo T hn h e with hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase | hcase |
    hcase | hcase | hcase
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 1) (e 2) (e 3)
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide))
      (hne 1 3 (by decide)) (hne 2 3 (by decide)) g02 g03 g13 g01 g12 g23
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 1) (e 3) (e 2)
      (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 0 2 (by decide)) (hne 1 3 (by decide))
      (hne 1 2 (by decide)) (hne 3 2 (by decide)) g03 g02 g12 g01 g13 (hps 2 3 g23)
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 2) (e 1) (e 3)
      (hne 0 2 (by decide)) (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 2 1 (by decide))
      (hne 2 3 (by decide)) (hne 1 3 (by decide)) g01 g03 g23 g02 (hps 1 2 g12) g13
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 2) (e 3) (e 1)
      (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 0 1 (by decide)) (hne 2 3 (by decide))
      (hne 2 1 (by decide)) (hne 3 1 (by decide)) g03 g01 (hzs 1 2 g12) g02 g23 (hps 1 3 g13)
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 3) (e 1) (e 2)
      (hne 0 3 (by decide)) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 3 1 (by decide))
      (hne 3 2 (by decide)) (hne 1 2 (by decide)) g01 g02 (hzs 2 3 g23) g03 (hps 1 3 g13) g12
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 0) (e 3) (e 2) (e 1)
      (hne 0 3 (by decide)) (hne 0 2 (by decide)) (hne 0 1 (by decide)) (hne 3 2 (by decide))
      (hne 3 1 (by decide)) (hne 2 1 (by decide)) g02 g01 (hzs 1 3 g13) g03 (hps 2 3 g23)
      (hps 1 2 g12)
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 1) (e 0) (e 2) (e 3)
      (hne 1 0 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 0 2 (by decide))
      (hne 0 3 (by decide)) (hne 2 3 (by decide)) g12 g13 g03 (hps 0 1 g01) g02 g23
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 1) (e 2) (e 0) (e 3)
      (hne 1 2 (by decide)) (hne 1 0 (by decide)) (hne 1 3 (by decide)) (hne 2 0 (by decide))
      (hne 2 3 (by decide)) (hne 0 3 (by decide)) (hzs 0 1 g01) g13 g23 g12 (hps 0 2 g02) g03
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 1) (e 0) (e 3) (e 2)
      (hne 1 0 (by decide)) (hne 1 3 (by decide)) (hne 1 2 (by decide)) (hne 0 3 (by decide))
      (hne 0 2 (by decide)) (hne 3 2 (by decide)) g13 g12 g02 (hps 0 1 g01) g03 (hps 2 3 g23)
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 1) (e 3) (e 0) (e 2)
      (hne 1 3 (by decide)) (hne 1 0 (by decide)) (hne 1 2 (by decide)) (hne 3 0 (by decide))
      (hne 3 2 (by decide)) (hne 0 2 (by decide)) (hzs 0 1 g01) g12 (hzs 2 3 g23) g13
      (hps 0 3 g03) g02
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 2) (e 0) (e 1) (e 3)
      (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 2 3 (by decide)) (hne 0 1 (by decide))
      (hne 0 3 (by decide)) (hne 1 3 (by decide)) (hzs 1 2 g12) g23 g03 (hps 0 2 g02) g01 g13
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_chain_four T hn h (e 2) (e 1) (e 0) (e 3)
      (hne 2 1 (by decide)) (hne 2 0 (by decide)) (hne 2 3 (by decide)) (hne 1 0 (by decide))
      (hne 1 3 (by decide)) (hne 0 3 (by decide)) (hzs 0 2 g02) g23 g13 (hps 1 2 g12)
      (hps 0 1 g01) g03
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_star_four T hn h (e 0) (e 1) (e 2) (e 3)
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide))
      (hne 1 3 (by decide)) (hne 2 3 (by decide)) g12 g13 g23 g01 g02 g03
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_star_four T hn h (e 1) (e 0) (e 2) (e 3)
      (hne 1 0 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 0 2 (by decide))
      (hne 0 3 (by decide)) (hne 2 3 (by decide)) g02 g03 g23 (hps 0 1 g01) g12 g13
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_star_four T hn h (e 2) (e 0) (e 1) (e 3)
      (hne 2 0 (by decide)) (hne 2 1 (by decide)) (hne 2 3 (by decide)) (hne 0 1 (by decide))
      (hne 0 3 (by decide)) (hne 1 3 (by decide)) g01 g03 g13 (hps 0 2 g02) (hps 1 2 g12) g23
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_star_four T hn h (e 3) (e 0) (e 1) (e 2)
      (hne 3 0 (by decide)) (hne 3 1 (by decide)) (hne 3 2 (by decide)) (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 1 2 (by decide)) g01 g02 g12 (hps 0 3 g03) (hps 1 3 g13)
      (hps 2 3 g23)
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_cycle_four T hn h (e 0) (e 2) (e 1) (e 3)
      (hne 0 2 (by decide)) (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 2 1 (by decide))
      (hne 2 3 (by decide)) (hne 1 3 (by decide)) g01 g23 g02 (hps 1 2 g12) g13 g03
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_cycle_four T hn h (e 0) (e 1) (e 2) (e 3)
      (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide))
      (hne 1 3 (by decide)) (hne 2 3 (by decide)) g02 g13 g01 g12 g23 g03
  · obtain ⟨g01, g02, g03, g12, g13, g23⟩ := hcase
    exact isGenusOneConfiguration_of_cycle_four T hn h (e 0) (e 1) (e 3) (e 2)
      (hne 0 1 (by decide)) (hne 0 3 (by decide)) (hne 0 2 (by decide)) (hne 1 3 (by decide))
      (hne 1 2 (by decide)) (hne 3 2 (by decide)) g03 g12 g01 g13 (hps 2 3 g23) g02

/-- **Stacks Project, Tag 0C8T**, cases (10)-(15). A numerical type with four components is
minimal of genus one exactly when it is one of the six four-component exceptional
configurations: the affine cycle, the three affine chains and the two affine forks. -/
@[stacks 0C8T "the classification for four components, cases (10)-(15)"]
public lemma isMinimal_and_genus_eq_one_iff_of_componentCount_eq_four (T : NumericalType)
    (hn : T.componentCount = 4) :
    (IsMinimal T ∧ genus T = 1) ↔ IsGenusOneConfiguration T :=
  ⟨fun hT => isGenusOneConfiguration_of_componentCount_eq_four T hn
      (forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hT.1 hT.2 (by omega)),
    isMinimal_and_genus_eq_one_of_isGenusOneConfiguration T⟩

end AlgebraicGeometry.NumericalType
