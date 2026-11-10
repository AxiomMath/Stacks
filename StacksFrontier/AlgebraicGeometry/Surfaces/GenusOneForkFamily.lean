module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkPattern

/-!
# The unbounded affine extensions

Three of the seven possibilities for the shape, the attachment vertex and the level left open by
`AlgebraicGeometry.NumericalType.exists_affine_extension_of_three_le_neighborCount` occur for
every number of vertices from five on, and each produces one of the three unbounded fork
families of `AlgebraicGeometry.NumericalType.GenusOne.LongFamily`: a diagram of type `D`
attached at the far end of its long arm gives the single forks `forkUp` and `forkDown` — cases
(29) and (30) — according to which of the two weights at the attachment is the larger; the same
diagram attached at the second vertex of its long arm gives the double fork `doubleFork`, case
(31); and a chain of type `C` or of type `B` attached at its second vertex gives `forkUp` and
`forkDown` again, read along the reversed chain.

## Main definitions

* `AlgebraicGeometry.NumericalType.leafFirst` and
  `AlgebraicGeometry.NumericalType.leafLast` — the two orderings of the components used: the
  attached component first and the vertices of the diagram after it in their own order, or the
  vertices in reverse order and the attached component last.

## Main results

One lemma per branch, named after the shape and the attachment vertex; each concludes
`AlgebraicGeometry.NumericalType.IsGenusOneConfiguration`.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry.NumericalType

/-! ### Matching one of the unbounded families -/

/-- A numerical type which is a Dynkin configuration with one component attached is a genus-one
configuration as soon as an ordering of its components realises the coefficient table of one of
the unbounded families; the diagonal of that table is automatic. -/
private lemma isGenusOneConfiguration_of_longFamily {t N : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hcard : N = T.componentCount) (hN : 6 ≤ N)
    (ι : Fin N → Option (Fin t)) (hιinj : Function.Injective ι)
    (E : Fin t → Fin t → Prop) (hE : ∀ r s, d.Edge r s ↔ E r s)
    (mv wv : Fin t → ℤ) (mcl wcl m W : ℤ) (hm : 0 < m) (hW : 0 < W)
    (hmv : ∀ r, T.multiplicity (v r) = mv r * m) (hml : T.multiplicity l = mcl * m)
    (hwv : ∀ r, T.weight (v r) = wv r * W) (hwl : T.weight l = wcl * W)
    (f : GenusOne.LongFamily)
    (hmc : ∀ a : Fin N, (ι a).elim mcl mv = GenusOne.longMultiplicity f N a)
    (hwc : ∀ a : Fin N, (ι a).elim wcl wv = GenusOne.longWeight f N a)
    (Adj : ℕ → ℕ → Prop) (hadj : ∀ a b : Fin N, a ≠ b → (AttachAdj ι E r₀ a b ↔ Adj a.val b.val))
    (hfam : (Adj = GenusOne.ForkAdj N ∧ (f = .forkUp ∨ f = .forkDown)) ∨
      (Adj = GenusOne.DoubleForkAdj N ∧ f = .doubleFork)) :
    IsGenusOneConfiguration T := by
  refine Or.inr (Or.inr ⟨N, f, hN,
    matchesCoefficients_of_erase_leaf T hn hminus l x hlx hleaf v hvinj hvl d w hcfg r₀ hr₀
      hcard ι hιinj E hE mv wv mcl wcl m W hm hW hmv hml hwv hwl _ _ _ hmc hwc
      (fun a => GenusOne.longIntersection_self f N a) ?_ ?_⟩)
  · intro a b hab hA
    rcases hfam with ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact GenusOne.longIntersection_fork_eq_max hN f hf a b hab ((hadj a b hab).mp hA)
    · exact GenusOne.longIntersection_doubleFork_eq_max hN a b hab ((hadj a b hab).mp hA)
  · intro a b hab hA
    rcases hfam with ⟨rfl, hf⟩ | ⟨rfl, rfl⟩
    · exact GenusOne.longIntersection_fork_eq_zero hN f hf a b hab
        (fun hc => hA ((hadj a b hab).mpr hc))
    · exact GenusOne.longIntersection_doubleFork_eq_zero hN a b hab
        (fun hc => hA ((hadj a b hab).mpr hc))

/-- At an attachment of level one, the attached component has the weight of the attachment vertex
and half of its multiplicity, once the weight factor and the multiplicity there are known. -/
private lemma pendant_level_one_of_affine {t : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y) (d : DynkinShape) (w : ℤ)
    (hcfg : IsDynkinConfiguration T v d w) (r₀ : Fin t) (hr₀ : v r₀ = x)
    (hmain : 2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * d.weightFactor r₀ * T.multiplicity (v r₀)) {a c : ℤ}
    (hwfr : d.weightFactor r₀ = c) (hmr : T.multiplicity (v r₀) = 2 * a) :
    T.weight l = c * w ∧ T.multiplicity l = 1 * a := by
  obtain ⟨hwl, hml⟩ := pendant_level_one (pendant_of_affine_system T hn hminus l x hlx
    hleaf v hvinj hvl hvsurj d w hcfg r₀ hr₀ 1 hmain)
  rw [← hr₀, hmr] at hml
  rw [← hr₀] at hwl
  exact ⟨by rw [hwl, hcfg.2.2.1 r₀, hwfr], by omega⟩

/-! ### Two orderings of the components -/

/-- The ordering of a Dynkin configuration with one component attached which puts the attached
component first and then the vertices of the diagram in their own order. -/
private def leafFirst (t : ℕ) (b : Fin (t + 1)) : Option (Fin t) :=
  if h : 0 < b.val then some ⟨b.val - 1, by omega⟩ else none

private lemma leafFirst_zero {t : ℕ} {b : Fin (t + 1)} (h : b.val = 0) :
    leafFirst t b = none := by
  rw [leafFirst, dite_eq_right (by omega)]

private lemma leafFirst_pos {t : ℕ} {b : Fin (t + 1)} (h : 0 < b.val) :
    leafFirst t b = some ⟨b.val - 1, by have := b.isLt; omega⟩ := by
  rw [leafFirst, dite_eq_left h]

private lemma leafFirst_elim_eq_of {α : Type*} {t : ℕ} (p : Fin (t + 1)) (a c : α)
    (g : Fin t → α) (h0 : p.val = 0 → a = c) (hs : ∀ r : Fin t, r.val + 1 = p.val → g r = c) :
    (leafFirst t p).elim a g = c := by
  rcases Nat.eq_zero_or_pos p.val with hp | hp
  · rw [leafFirst_zero hp]
    exact h0 hp
  · rw [leafFirst_pos hp]
    exact hs _ (by simp only; omega)

private lemma leafFirst_injective (t : ℕ) : Function.Injective (leafFirst t) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
  · rcases Nat.eq_zero_or_pos b.val with hb0 | hb0
    · exact Fin.ext (by omega)
    · rw [leafFirst_zero ha0, leafFirst_pos hb0] at hab
      simp at hab
  · rcases Nat.eq_zero_or_pos b.val with hb0 | hb0
    · rw [leafFirst_zero hb0, leafFirst_pos ha0] at hab
      simp at hab
    · rw [leafFirst_pos ha0,
        leafFirst_pos hb0] at hab
      simp only [Option.some.injEq, Fin.mk.injEq] at hab
      exact Fin.ext (by omega)

/-- The ordering of a Dynkin configuration with one component attached which lists the vertices
of the diagram in reverse order and puts the attached component last. -/
private def leafLast (t : ℕ) (b : Fin (t + 1)) : Option (Fin t) :=
  if h : b.val < t then some ⟨t - 1 - b.val, by omega⟩ else none

private lemma leafLast_last {t : ℕ} {b : Fin (t + 1)} (h : t ≤ b.val) :
    leafLast t b = none := by
  rw [leafLast, dite_eq_right (by omega)]

private lemma leafLast_lt {t : ℕ} {b : Fin (t + 1)} (h : b.val < t) :
    leafLast t b = some ⟨t - 1 - b.val, by omega⟩ := by
  rw [leafLast, dite_eq_left h]

private lemma leafLast_elim_eq_of {α : Type*} {t : ℕ} (p : Fin (t + 1)) (a c : α)
    (g : Fin t → α) (h0 : t ≤ p.val → a = c)
    (hs : ∀ r : Fin t, r.val + p.val + 1 = t → g r = c) : (leafLast t p).elim a g = c := by
  rcases Nat.lt_or_ge p.val t with hp | hp
  · rw [leafLast_lt hp]
    exact hs _ (by simp only; omega)
  · rw [leafLast_last hp]
    exact h0 hp

private lemma leafLast_injective (t : ℕ) : Function.Injective (leafLast t) := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  rcases Nat.lt_or_ge a.val t with ha0 | ha0
  · rcases Nat.lt_or_ge b.val t with hb0 | hb0
    · rw [leafLast_lt ha0,
        leafLast_lt hb0] at hab
      simp only [Option.some.injEq, Fin.mk.injEq] at hab
      exact Fin.ext (by omega)
    · rw [leafLast_last hb0, leafLast_lt ha0] at hab
      simp at hab
  · rcases Nat.lt_or_ge b.val t with hb0 | hb0
    · rw [leafLast_last ha0, leafLast_lt hb0] at hab
      simp at hab
    · exact Fin.ext (by omega)

/-! ### Adjacency along the two orderings -/

/-- Adjacency along `leafFirst`, as a statement about positions: the attached component sits at
position zero and the `r`-th vertex of the diagram at position `r + 1`. -/
private lemma attachAdj_leafFirst {t : ℕ} (E : Fin t → Fin t → Prop) (r₀ : Fin t)
    (EN : ℕ → ℕ → Prop) (hEN : ∀ r s : Fin t, E r s ↔ EN r.val s.val)
    (a b : Fin (t + 1)) (hab : a ≠ b) :
    AttachAdj (leafFirst t) E r₀ a b ↔
      ((0 < a.val ∧ 0 < b.val ∧ EN (a.val - 1) (b.val - 1)) ∨
        (a.val = 0 ∧ b.val = r₀.val + 1) ∨ (b.val = 0 ∧ a.val = r₀.val + 1)) := by
  have ha := a.isLt
  have hb := b.isLt
  have hr := r₀.isLt
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases Nat.eq_zero_or_pos a.val with ha0 | ha0
  · rcases Nat.eq_zero_or_pos b.val with hb0 | hb0
    · omega
    · rw [attachAdj_none_some _ _ r₀ (leafFirst_zero ha0)
        (leafFirst_pos hb0)]
      constructor
      · intro h
        have h2 : b.val - 1 = r₀.val := congrArg Fin.val h
        exact Or.inr (Or.inl ⟨ha0, by omega⟩)
      · rintro (⟨h, -, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
        · omega
        · exact Fin.ext (show b.val - 1 = r₀.val by omega)
        · omega
  · rcases Nat.eq_zero_or_pos b.val with hb0 | hb0
    · rw [attachAdj_some_none _ _ r₀
        (leafFirst_pos ha0)
        (leafFirst_zero hb0)]
      constructor
      · intro h
        have h2 : a.val - 1 = r₀.val := congrArg Fin.val h
        exact Or.inr (Or.inr ⟨hb0, by omega⟩)
      · rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
        · omega
        · omega
        · exact Fin.ext (show a.val - 1 = r₀.val by omega)
    · rw [attachAdj_some_some _ _ r₀
        (leafFirst_pos ha0)
        (leafFirst_pos hb0),
        hEN]
      constructor
      · intro h
        exact Or.inl ⟨ha0, hb0, h⟩
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h
        · omega
        · omega

/-- Adjacency along `leafLast`, as a statement about positions: the `r`-th vertex of the diagram
sits at position `t - 1 - r` and the attached component at position `t`. -/
private lemma attachAdj_leafLast {t : ℕ} (E : Fin t → Fin t → Prop) (r₀ : Fin t)
    (EN : ℕ → ℕ → Prop) (hEN : ∀ r s : Fin t, E r s ↔ EN r.val s.val)
    (a b : Fin (t + 1)) (hab : a ≠ b) :
    AttachAdj (leafLast t) E r₀ a b ↔
      ((a.val < t ∧ b.val < t ∧ EN (t - 1 - a.val) (t - 1 - b.val)) ∨
        (t ≤ a.val ∧ b.val + r₀.val + 1 = t) ∨ (t ≤ b.val ∧ a.val + r₀.val + 1 = t)) := by
  have ha := a.isLt
  have hb := b.isLt
  have hr := r₀.isLt
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  rcases Nat.lt_or_ge a.val t with ha0 | ha0
  · rcases Nat.lt_or_ge b.val t with hb0 | hb0
    · rw [attachAdj_some_some _ _ r₀
        (leafLast_lt ha0)
        (leafLast_lt hb0), hEN]
      constructor
      · intro h
        exact Or.inl ⟨ha0, hb0, h⟩
      · rintro (⟨-, -, h⟩ | ⟨h, -⟩ | ⟨h, -⟩)
        · exact h
        · omega
        · omega
    · rw [attachAdj_some_none _ _ r₀
        (leafLast_lt ha0)
        (leafLast_last hb0)]
      constructor
      · intro h
        have h2 : t - 1 - a.val = r₀.val := congrArg Fin.val h
        exact Or.inr (Or.inr ⟨hb0, by omega⟩)
      · rintro (⟨-, h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩)
        · omega
        · omega
        · exact Fin.ext (show t - 1 - a.val = r₀.val by omega)
  · rcases Nat.lt_or_ge b.val t with hb0 | hb0
    · rw [attachAdj_none_some _ _ r₀ (leafLast_last ha0)
        (leafLast_lt hb0)]
      constructor
      · intro h
        have h2 : t - 1 - b.val = r₀.val := congrArg Fin.val h
        exact Or.inr (Or.inl ⟨ha0, by omega⟩)
      · rintro (⟨h, -, -⟩ | ⟨-, h⟩ | ⟨h, -⟩)
        · omega
        · exact Fin.ext (show t - 1 - b.val = r₀.val by omega)
        · omega
    · omega

/-- The positional form of the adjacency of a type-`D` diagram with one component attached at
the second vertex of its long arm: the double-fork adjacency on one more position. -/
private lemma doubleForkAdj_iff {t : ℕ} (ht : 5 ≤ t) (α β ρ : ℕ) (hα : α < t + 1)
    (hβ : β < t + 1) (hρ : ρ = 1) :
    ((0 < α ∧ 0 < β ∧
          (((α - 1 + 1 = β - 1 ∨ β - 1 + 1 = α - 1) ∧ α - 1 < t - 1 ∧ β - 1 < t - 1) ∨
            (α - 1 = t - 3 ∧ β - 1 = t - 1) ∨ (β - 1 = t - 3 ∧ α - 1 = t - 1))) ∨
        (α = 0 ∧ β = ρ + 1) ∨ (β = 0 ∧ α = ρ + 1))
      ↔ GenusOne.DoubleForkAdj (t + 1) α β := by
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 5 := ⟨t - 5, by omega⟩
  simp only [GenusOne.DoubleForkAdj]
  omega

/-! ### Adjacency and coefficient tables of the three families -/

private lemma attachAdj_leafFirst_D_iff_forkAdj {t : ℕ} (ht : 5 ≤ t) (r₀ : Fin t)
    (hr0 : r₀.val = 0) (p q : Fin (t + 1)) (hpq : p ≠ q) :
    AttachAdj (leafFirst t)
      (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
        (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1)) r₀ p q
      ↔ GenusOne.ForkAdj (t + 1) p.val q.val := by
  rw [attachAdj_leafFirst _ r₀
    (fun j k => ((j + 1 = k ∨ k + 1 = j) ∧ j < t - 1 ∧ k < t - 1) ∨
      (j = t - 3 ∧ k = t - 1) ∨ (k = t - 3 ∧ j = t - 1)) (fun _ _ => Iff.rfl) p q hpq]
  simp only [GenusOne.ForkAdj]
  have hp := p.isLt
  have hq := q.isLt
  omega

private lemma attachAdj_leafFirst_D_iff_doubleForkAdj {t : ℕ} (ht : 5 ≤ t) (r₀ : Fin t)
    (hr0 : r₀.val = 1) (p q : Fin (t + 1)) (hpq : p ≠ q) :
    AttachAdj (leafFirst t)
      (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
        (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1)) r₀ p q
      ↔ GenusOne.DoubleForkAdj (t + 1) p.val q.val := by
  rw [attachAdj_leafFirst _ r₀
    (fun j k => ((j + 1 = k ∨ k + 1 = j) ∧ j < t - 1 ∧ k < t - 1) ∨
      (j = t - 3 ∧ k = t - 1) ∨ (k = t - 3 ∧ j = t - 1)) (fun _ _ => Iff.rfl) p q hpq]
  exact doubleForkAdj_iff ht p.val q.val r₀.val p.isLt q.isLt hr0

private lemma attachAdj_leafLast_chain_iff_forkAdj {t : ℕ} (r₀ : Fin t)
    (hr0 : r₀.val = 1) (p q : Fin (t + 1)) (hpq : p ≠ q) :
    AttachAdj (leafLast t) (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) r₀ p q
      ↔ GenusOne.ForkAdj (t + 1) p.val q.val := by
  rw [attachAdj_leafLast _ r₀ (fun j k => j + 1 = k ∨ k + 1 = j) (fun _ _ => Iff.rfl) p q hpq]
  simp only [GenusOne.ForkAdj]
  have hp := p.isLt
  have hq := q.isLt
  omega

private lemma leafFirst_elim_eq_longMultiplicity_forkDown {t : ℕ} (ht : 5 ≤ t)
    (p : Fin (t + 1)) :
    (leafFirst t p).elim (2 : ℤ) (fun r : Fin t => if r.val + 3 ≤ t then (2 : ℤ) else 1)
      = GenusOne.longMultiplicity .forkDown (t + 1) p := by
  have := p.isLt
  refine leafFirst_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longMultiplicity] <;> split_ifs <;> omega

private lemma leafFirst_elim_eq_longWeight_forkDown {t : ℕ} (p : Fin (t + 1)) :
    (leafFirst t p).elim (1 : ℤ) (fun _ : Fin t => (2 : ℤ))
      = GenusOne.longWeight .forkDown (t + 1) p := by
  have := p.isLt
  refine leafFirst_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longWeight] <;> split_ifs <;> omega

private lemma leafFirst_elim_eq_longMultiplicity_forkUp {t : ℕ} (p : Fin (t + 1)) :
    (leafFirst t p).elim (1 : ℤ) (fun r : Fin t => if r.val + 3 ≤ t then (2 : ℤ) else 1)
      = GenusOne.longMultiplicity .forkUp (t + 1) p := by
  have := p.isLt
  refine leafFirst_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longMultiplicity] <;> split_ifs <;> omega

private lemma leafFirst_elim_eq_longWeight_forkUp {t : ℕ} (p : Fin (t + 1)) :
    (leafFirst t p).elim (2 : ℤ) DynkinShape.D.weightFactor
      = GenusOne.longWeight .forkUp (t + 1) p := by
  have := p.isLt
  refine leafFirst_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longWeight, DynkinShape.weightFactor] <;> split_ifs <;> omega

private lemma leafFirst_elim_eq_longMultiplicity_doubleFork {t : ℕ} (p : Fin (t + 1)) :
    (leafFirst t p).elim (1 : ℤ)
        (fun r : Fin t => if r.val = 0 then (1 : ℤ) else if r.val + 3 ≤ t then 2 else 1)
      = GenusOne.longMultiplicity .doubleFork (t + 1) p := by
  have := p.isLt
  refine leafFirst_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longMultiplicity] <;> split_ifs <;> omega

private lemma leafFirst_elim_eq_longWeight_doubleFork {t : ℕ} (p : Fin (t + 1)) :
    (leafFirst t p).elim (1 : ℤ) DynkinShape.D.weightFactor
      = GenusOne.longWeight .doubleFork (t + 1) p :=
  leafFirst_elim_eq_of p _ _ _ (fun _ => rfl) (fun _ _ => rfl)

private lemma leafLast_elim_eq_longMultiplicity_forkUp {t : ℕ} (p : Fin (t + 1)) :
    (leafLast t p).elim (1 : ℤ)
        (fun r : Fin t => if r.val = 0 ∨ r.val + 1 = t then (1 : ℤ) else 2)
      = GenusOne.longMultiplicity .forkUp (t + 1) p := by
  have := p.isLt
  refine leafLast_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longMultiplicity] <;> split_ifs <;> omega

private lemma leafLast_elim_eq_longWeight_forkUp {t : ℕ} (ht : 5 ≤ t) (p : Fin (t + 1)) :
    (leafLast t p).elim (1 : ℤ) DynkinShape.C.weightFactor
      = GenusOne.longWeight .forkUp (t + 1) p := by
  have := p.isLt
  refine leafLast_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longWeight, DynkinShape.weightFactor] <;> split_ifs <;> omega

private lemma leafLast_elim_eq_longMultiplicity_forkDown {t : ℕ} (p : Fin (t + 1)) :
    (leafLast t p).elim (1 : ℤ) (fun r : Fin t => if r.val = 0 then (1 : ℤ) else 2)
      = GenusOne.longMultiplicity .forkDown (t + 1) p := by
  have := p.isLt
  refine leafLast_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longMultiplicity] <;> split_ifs <;> omega

private lemma leafLast_elim_eq_longWeight_forkDown {t : ℕ} (ht : 5 ≤ t) (p : Fin (t + 1)) :
    (leafLast t p).elim (2 : ℤ) DynkinShape.B.weightFactor
      = GenusOne.longWeight .forkDown (t + 1) p := by
  have := p.isLt
  refine leafLast_elim_eq_of p _ _ _ (fun _ => ?_) (fun r _ => ?_) <;>
    simp only [GenusOne.longWeight, DynkinShape.weightFactor] <;> split_ifs <;> omega

/-! ### Type `D` attached at the far end of its long arm -/

/-- The affine extension of a diagram of type `D` on at least five vertices at the far end of
its long arm is case (29) or case (30), according to which of the two weights at the attachment
is the larger: the ordering puts the attached component first, then the long arm, then the two
short arms, and the resulting type is a single fork. -/
public lemma isGenusOneConfiguration_of_affine_D_zero {t : ℕ} (ht : 5 ≤ t) (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : t + 1 = T.componentCount)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hr0 : r₀.val = 0)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 2 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) r₀ 2 hrest hmain
  rcases hcases with h | h | h | h
  · obtain ⟨-, -, hlo, hhi⟩ := h
    have hmv : ∀ r : Fin t,
        T.multiplicity (v r) = (if r.val + 3 ≤ t then (2 : ℤ) else 1) * a := by
      intro r
      have hr := r.isLt
      by_cases hc : r.val + 3 ≤ t
      · rw [ite_eq_left hc]
        linear_combination hlo r hc
      · rw [ite_eq_right hc]
        linear_combination hhi r (by omega)
    have hmr : T.multiplicity (v r₀) = 2 * a := by
      rw [hmv r₀, ite_eq_left (show r₀.val + 3 ≤ t by omega)]
    have hpend := pendant_of_affine_system T hn hminus l x hlx hleaf v hvinj hvl hvsurj .D w
      hcfg r₀ hr₀ 2 hmain
    rw [← hr₀] at hpend
    have hadj := attachAdj_leafFirst_D_iff_forkAdj ht r₀ hr0
    rcases pendant_level_two T l (v r₀) v w a (fun r => hcfg.2.2.1 r) (hcfg.2.2.1 r₀) hmr
      hpend with ⟨W, hWpos, hwv, hwl, hml⟩ | ⟨hwl, hml⟩
    · exact isGenusOneConfiguration_of_longFamily T hn hminus l x hlx hleaf v hvinj hvl
        DynkinShape.D w hcfg r₀ hr₀ hcard (by omega) (leafFirst t) (leafFirst_injective t)
        (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
          (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1))
        (fun _ _ => Iff.rfl) _ (fun _ => 2) 2 1 a W hapos hWpos hmv hml hwv hwl
        .forkDown (leafFirst_elim_eq_longMultiplicity_forkDown ht)
        leafFirst_elim_eq_longWeight_forkDown (GenusOne.ForkAdj _) hadj
        (Or.inl ⟨rfl, Or.inr rfl⟩)
    · exact isGenusOneConfiguration_of_longFamily T hn hminus l x hlx hleaf v hvinj hvl
        DynkinShape.D w hcfg r₀ hr₀ hcard (by omega) (leafFirst t) (leafFirst_injective t)
        (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
          (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1))
        (fun _ _ => Iff.rfl) _ DynkinShape.D.weightFactor 1 2 a w hapos hcfg.2.1 hmv hml
        hcfg.2.2.1 hwl .forkUp leafFirst_elim_eq_longMultiplicity_forkUp
        leafFirst_elim_eq_longWeight_forkUp (GenusOne.ForkAdj _) hadj (Or.inl ⟨rfl, Or.inl rfl⟩)
  all_goals exact absurd h.1 (by omega)

/-! ### Type `D` attached at the second vertex of its long arm -/

/-- The affine extension of a diagram of type `D` on at least five vertices at the second
vertex of its long arm is case (31): two prongs at each end of a chain, the double fork. -/
public lemma isGenusOneConfiguration_of_affine_D_one {t : ℕ} (ht : 5 ≤ t) (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .D w) (hcard : t + 1 = T.componentCount)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.D.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.D.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.D.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain ⟨a, hapos, hcases⟩ := affine_system_solved_D (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) r₀ 1 hrest hmain
  rcases hcases with h | h | h | h
  · exact absurd h.1 (by omega)
  · obtain ⟨-, -, hd0, hd1, hd2⟩ := h
    have hmv : ∀ r : Fin t,
        T.multiplicity (v r)
          = (if r.val = 0 then (1 : ℤ) else if r.val + 3 ≤ t then 2 else 1) * a := by
      intro r
      have hr := r.isLt
      by_cases hc : r.val = 0
      · rw [ite_eq_left hc]
        linear_combination hd0 r hc
      · rw [ite_eq_right hc]
        by_cases hc2 : r.val + 3 ≤ t
        · rw [ite_eq_left hc2]
          linear_combination hd1 r (by omega) hc2
        · rw [ite_eq_right hc2]
          linear_combination hd2 r (by omega)
    have hmr : T.multiplicity (v r₀) = 2 * a := by
      rw [hmv r₀, ite_eq_right (show ¬(r₀.val = 0) by omega),
        ite_eq_left (show r₀.val + 3 ≤ t by omega)]
    obtain ⟨hwl, hml⟩ := pendant_level_one_of_affine T hn hminus l x hlx hleaf v hvinj hvl hvsurj
      .D w hcfg r₀ hr₀ hmain (c := 1) rfl hmr
    have hadj := attachAdj_leafFirst_D_iff_doubleForkAdj ht r₀ hr0
    exact isGenusOneConfiguration_of_longFamily T hn hminus l x hlx hleaf v hvinj hvl
      DynkinShape.D w hcfg r₀ hr₀ hcard (by omega) (leafFirst t) (leafFirst_injective t)
      (fun r s => ((r.val + 1 = s.val ∨ s.val + 1 = r.val) ∧ r.val < t - 1 ∧ s.val < t - 1) ∨
        (r.val = t - 3 ∧ s.val = t - 1) ∨ (s.val = t - 3 ∧ r.val = t - 1))
      (fun _ _ => Iff.rfl) _ DynkinShape.D.weightFactor 1 1 a w hapos hcfg.2.1 hmv hml
      hcfg.2.2.1 hwl .doubleFork leafFirst_elim_eq_longMultiplicity_doubleFork
      leafFirst_elim_eq_longWeight_doubleFork (GenusOne.DoubleForkAdj _) hadj
      (Or.inr ⟨rfl, rfl⟩)
  all_goals exact absurd h.1 (by omega)

/-! ### The chains of type `C` and of type `B` -/

/-- The affine extension of a chain of type `C` on at least five vertices at its second vertex
is case (29): read along the reversed chain, the heavy end comes first and the two prongs last,
which is the single fork `forkUp`. -/
public lemma isGenusOneConfiguration_of_affine_C {t : ℕ} (ht : 5 ≤ t) (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .C w) (hcard : t + 1 = T.componentCount)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.C.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.C.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.C.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain ⟨-, -, a, hapos, hc0, hc1, hc2⟩ := affine_system_solved_C (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) r₀ 1 (by omega) (by omega)
    hrest hmain
  have hmv : ∀ r : Fin t,
      T.multiplicity (v r) = (if r.val = 0 ∨ r.val + 1 = t then (1 : ℤ) else 2) * a := by
    intro r
    have hr := r.isLt
    by_cases hc : r.val = 0 ∨ r.val + 1 = t
    · rw [ite_eq_left hc]
      rcases hc with hc | hc
      · linear_combination hc0 r hc
      · linear_combination hc2 r hc
    · rw [ite_eq_right hc]
      linear_combination hc1 r (by omega) (by omega)
  have hmr : T.multiplicity (v r₀) = 2 * a := by
    rw [hmv r₀, ite_eq_right (show ¬(r₀.val = 0 ∨ r₀.val + 1 = t) by omega)]
  have hwfr : DynkinShape.C.weightFactor r₀ = 1 := by
    simp only [DynkinShape.weightFactor]
    rw [ite_eq_right (by omega)]
  obtain ⟨hwl, hml⟩ := pendant_level_one_of_affine T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .C w hcfg r₀ hr₀ hmain hwfr hmr
  have hadj := attachAdj_leafLast_chain_iff_forkAdj r₀ hr0
  exact isGenusOneConfiguration_of_longFamily T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.C w hcfg r₀ hr₀ hcard (by omega) (leafLast t) (leafLast_injective t)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.C.weightFactor 1 1 a w hapos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
    .forkUp leafLast_elim_eq_longMultiplicity_forkUp (leafLast_elim_eq_longWeight_forkUp ht)
    (GenusOne.ForkAdj _) hadj (Or.inl ⟨rfl, Or.inl rfl⟩)

/-- The affine extension of a chain of type `B` on at least five vertices at its second vertex
is case (30): read along the reversed chain, the light end comes first and the two prongs last,
which is the single fork `forkDown`. -/
public lemma isGenusOneConfiguration_of_affine_B {t : ℕ} (ht : 5 ≤ t) (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (w : ℤ) (hcfg : IsDynkinConfiguration T v .B w) (hcard : t + 1 = T.componentCount)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hr0 : r₀.val = 1)
    (hrest : ∀ r, r ≠ r₀ → ∑ s, DynkinShape.B.weightedCartan r s * T.multiplicity (v s) = 0)
    (hmain : 2 * ∑ s, DynkinShape.B.weightedCartan r₀ s * T.multiplicity (v s)
      = 1 * DynkinShape.B.weightFactor r₀ * T.multiplicity (v r₀)) :
    IsGenusOneConfiguration T := by
  obtain ⟨-, -, a, hapos, hb0, hb1⟩ := affine_system_solved_B (by omega)
    (fun r => T.multiplicity (v r)) (fun r => T.multiplicity_pos _) r₀ 1 (by omega) (by omega)
    hrest hmain
  have hmv : ∀ r : Fin t,
      T.multiplicity (v r) = (if r.val = 0 then (1 : ℤ) else 2) * a := by
    intro r
    by_cases hc : r.val = 0
    · rw [ite_eq_left hc]
      linear_combination hb0 r hc
    · rw [ite_eq_right hc]
      linear_combination hb1 r (by omega)
  have hmr : T.multiplicity (v r₀) = 2 * a := by
    rw [hmv r₀, ite_eq_right (show ¬(r₀.val = 0) by omega)]
  have hwfr : DynkinShape.B.weightFactor r₀ = 2 := by
    simp only [DynkinShape.weightFactor]
    rw [ite_eq_right (by omega)]
  obtain ⟨hwl, hml⟩ := pendant_level_one_of_affine T hn hminus l x hlx hleaf v hvinj hvl hvsurj
    .B w hcfg r₀ hr₀ hmain hwfr hmr
  have hadj := attachAdj_leafLast_chain_iff_forkAdj r₀ hr0
  exact isGenusOneConfiguration_of_longFamily T hn hminus l x hlx hleaf v hvinj hvl
    DynkinShape.B w hcfg r₀ hr₀ hcard (by omega) (leafLast t) (leafLast_injective t)
    (fun r s => r.val + 1 = s.val ∨ s.val + 1 = r.val) (fun _ _ => Iff.rfl)
    _ DynkinShape.B.weightFactor 1 2 a w hapos hcfg.2.1 hmv hml hcfg.2.2.1 hwl
    .forkDown leafLast_elim_eq_longMultiplicity_forkDown
    (leafLast_elim_eq_longWeight_forkDown ht)
    (GenusOne.ForkAdj _) hadj (Or.inl ⟨rfl, Or.inr rfl⟩)

end AlgebraicGeometry.NumericalType
