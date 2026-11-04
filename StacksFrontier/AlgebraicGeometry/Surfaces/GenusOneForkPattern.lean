module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneFork

/-!
# Reading a coefficient table off an affine extension

`AlgebraicGeometry.NumericalType.exists_affine_extension_of_three_le_neighborCount` presents a
minimal numerical type of genus one with a component meeting three or more others as a Dynkin
configuration `v` of shape `d` together with one further component `l` attached at the vertex
`r₀`, and pins the shape, the attachment vertex and the level to seven possibilities. Turning
one of those possibilities into a coefficient table means choosing an ordering of all the
components — the vertices of the diagram and the attached component together — and checking the
three tables entry by entry against it.

This file supplies the common machinery for that step, so that one possibility costs only the
choice of the ordering and the arithmetic of its entries.

## Main definitions

* `AlgebraicGeometry.NumericalType.AttachAdj` — adjacency in a Dynkin configuration with one
  component attached, transported along an ordering of the components presented as a map `ι`
  into `Option` of the vertex set, `none` marking the position of the attached component.
* `AlgebraicGeometry.NumericalType.GenusOne.ForkAdj` and
  `AlgebraicGeometry.NumericalType.GenusOne.DoubleForkAdj` — the positions joined in the
  single-fork and the double-fork unbounded families.

## Main results

* `AlgebraicGeometry.NumericalType.pendant_of_affine_system` — the weight and the multiplicity
  of the attached component, read off the level of the affine extension system, with
  `AlgebraicGeometry.NumericalType.pendant_level_one` and
  `AlgebraicGeometry.NumericalType.pendant_level_two` resolving it at the two levels that
  occur.
* `AlgebraicGeometry.NumericalType.matchesCoefficients_of_erase_leaf` — a numerical type which
  is a Dynkin configuration with one component attached matches a coefficient table as soon as
  an ordering of its components realises the table entry by entry; the conditions on the table
  are arithmetic in the coefficients alone, and the intersection table is checked against
  `AttachAdj` alone.
* `AlgebraicGeometry.NumericalType.GenusOne.longIntersection_fork_eq_max` and
  `AlgebraicGeometry.NumericalType.GenusOne.longIntersection_fork_eq_zero`, with their
  double-fork counterparts — the intersection tables of the three unbounded fork families.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-- The weight factors of a Dynkin shape are positive. -/
public lemma DynkinShape.weightFactor_pos {t : ℕ} (d : DynkinShape) (r : Fin t) :
    0 < d.weightFactor r := by
  cases d <;> simp only [DynkinShape.weightFactor] <;>
    first
      | (split_ifs <;> norm_num)
      | norm_num

namespace NumericalType

/-! ### Adjacency along an ordering of the components -/

/-- Adjacency in a Dynkin configuration with one further component attached at the vertex `r₀`,
read along an ordering of all the components: `ι a = some r` puts the `r`-th vertex of the
diagram at position `a`, and `ι a = none` puts the attached component there. Two diagram
vertices are joined when `E` joins them, and the attached component is joined to the attachment
vertex only. -/
public def AttachAdj {t N : ℕ} (ι : Fin N → Option (Fin t)) (E : Fin t → Fin t → Prop)
    (r₀ : Fin t) (a b : Fin N) : Prop :=
  (∃ r s, ι a = some r ∧ ι b = some s ∧ E r s) ∨
    (ι a = none ∧ ι b = some r₀) ∨ (ι a = some r₀ ∧ ι b = none)

/-- Adjacency along an ordering is decidable as soon as the edge relation is, which is what
lets a concrete ordering against a concrete table be checked by `decide`. -/
public instance instDecidableAttachAdj {t N : ℕ} (ι : Fin N → Option (Fin t))
    (E : Fin t → Fin t → Prop) [∀ r s, Decidable (E r s)] (r₀ : Fin t) (a b : Fin N) :
    Decidable (AttachAdj ι E r₀ a b) := by
  unfold AttachAdj
  infer_instance

public lemma attachAdj_some_some {t N : ℕ} (ι : Fin N → Option (Fin t))
    (E : Fin t → Fin t → Prop) (r₀ : Fin t) {a b : Fin N} {r s : Fin t}
    (hia : ι a = some r) (hib : ι b = some s) : AttachAdj ι E r₀ a b ↔ E r s := by
  simp [AttachAdj, hia, hib]

/-- The attached component is adjacent along an ordering only to the attachment vertex. -/
public lemma attachAdj_none_some {t N : ℕ} (ι : Fin N → Option (Fin t))
    (E : Fin t → Fin t → Prop) (r₀ : Fin t) {a b : Fin N} {s : Fin t}
    (hia : ι a = none) (hib : ι b = some s) : AttachAdj ι E r₀ a b ↔ s = r₀ := by
  simp [AttachAdj, hia, hib]

/-- A vertex of the diagram is adjacent along an ordering to the attached component only if it
is the attachment vertex. -/
public lemma attachAdj_some_none {t N : ℕ} (ι : Fin N → Option (Fin t))
    (E : Fin t → Fin t → Prop) (r₀ : Fin t) {a b : Fin N} {r : Fin t}
    (hia : ι a = some r) (hib : ι b = none) : AttachAdj ι E r₀ a b ↔ r = r₀ := by
  simp [AttachAdj, hia, hib]

/-! ### The pendant component -/

/-- The pendant datum of an affine extension whose level is already known: the weight and the
multiplicity of the attached component `l`, in terms of those of the attachment vertex `x` and
of the level `k`, in the two ways the heavier of the two weights can be distributed. The level
appearing in the inhomogeneous equation at the attachment vertex is the level of the pair
`{l, x}`, because the weight factor and the multiplicity there are positive. -/
public lemma pendant_of_affine_system {t : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvl : ∀ r, v r ≠ l) (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (k : ℤ)
    (hmain : 2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)
      = k * d.weightFactor r₀ * T.multiplicity (v r₀)) :
    (T.weight x = k * T.weight l ∧ 2 * T.multiplicity l = k * T.multiplicity x) ∨
      (T.weight l = k * T.weight x ∧ 2 * T.multiplicity l = T.multiplicity x) := by
  obtain ⟨k', -, -, hmain', hpend⟩ := affine_system_of_erase_leaf T hn hminus l x hlx hleaf
    v hvinj hvl hvsurj d w hcfg r₀ hr₀
  have hkk : k' = k := by
    have h : (k' - k) * (d.weightFactor r₀ * T.multiplicity (v r₀)) = 0 := by
      linear_combination hmain - hmain'
    have := (mul_eq_zero.mp h).resolve_right
      (mul_pos (d.weightFactor_pos r₀) (T.multiplicity_pos _)).ne'
    linarith
  rwa [hkk] at hpend

/-! ### The two pendant options -/

/-- At an attachment of level one the weight of the attached component equals the weight at the
attachment vertex and its multiplicity is half of the one there. -/
public lemma pendant_level_one {T : NumericalType} {l x : Fin T.componentCount}
    (hpend : (T.weight x = 1 * T.weight l ∧ 2 * T.multiplicity l = 1 * T.multiplicity x) ∨
      (T.weight l = 1 * T.weight x ∧ 2 * T.multiplicity l = T.multiplicity x)) :
    T.weight l = T.weight x ∧ 2 * T.multiplicity l = T.multiplicity x := by
  rcases hpend with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩

/-- At an attachment of level two in a configuration all of whose weight factors are one, the
weight of the attached component is either half the scale — and then its multiplicity equals the
one at the attachment vertex, and against the halved scale the configuration has weight
coefficient two throughout — or twice the scale, and then its multiplicity is half the one at
the attachment vertex. -/
public lemma pendant_level_two {t : ℕ} (T : NumericalType) (l x : Fin T.componentCount)
    (v : Fin t → Fin T.componentCount) (w a : ℤ)
    (hwv : ∀ r, T.weight (v r) = 1 * w) (hwx : T.weight x = 1 * w)
    (hmx : T.multiplicity x = 2 * a)
    (hpend : (T.weight x = 2 * T.weight l ∧ 2 * T.multiplicity l = 2 * T.multiplicity x) ∨
      (T.weight l = 2 * T.weight x ∧ 2 * T.multiplicity l = T.multiplicity x)) :
    (∃ W, 0 < W ∧ (∀ r, T.weight (v r) = 2 * W) ∧ T.weight l = 1 * W ∧
        T.multiplicity l = 2 * a) ∨
      (T.weight l = 2 * w ∧ T.multiplicity l = 1 * a) := by
  rcases hpend with ⟨hw, hmm⟩ | ⟨hw, hmm⟩
  · exact Or.inl ⟨T.weight l, T.weight_pos l, fun r => by linarith [hwv r], (one_mul _).symm,
      by omega⟩
  · exact Or.inr ⟨by omega, by omega⟩

/-! ### Matching a coefficient table -/

/-- Along an ordering `ι` of a Dynkin configuration `v` with one component `l` attached at `r₀`,
two positions have nonzero intersection exactly when they are adjacent or equal. -/
private lemma intersection_optionElim_ne_zero_iff {t N : ℕ} (T : NumericalType)
    (l : Fin T.componentCount) (v : Fin t → Fin T.componentCount) (d : DynkinShape)
    (r₀ : Fin t) (ι : Fin N → Option (Fin t)) (hιinj : Function.Injective ι)
    (E : Fin t → Fin t → Prop) (hE : ∀ r s, d.Edge r s ↔ E r s)
    (hpair : ∀ r s, T.intersection (v r) (v s) ≠ 0 ↔ (d.Edge r s ∨ r = s))
    (hlr : ∀ r, T.intersection l (v r) ≠ 0 ↔ r = r₀) (hll : T.intersection l l ≠ 0)
    (a b : Fin N) :
    T.intersection ((ι a).elim l v) ((ι b).elim l v) ≠ 0 ↔ (AttachAdj ι E r₀ a b ∨ a = b) := by
  rcases hia : ι a with _ | r
  · rcases hib : ι b with _ | s
    · have hab : a = b := hιinj (by rw [hia, hib])
      show T.intersection l l ≠ 0 ↔ _
      exact ⟨fun _ => Or.inr hab, fun _ => hll⟩
    · have hab : a ≠ b := by
        rintro rfl
        simp [hia] at hib
      rw [attachAdj_none_some ι E r₀ hia hib]
      show T.intersection l (v s) ≠ 0 ↔ _
      rw [hlr s]
      exact ⟨Or.inl, fun h => h.resolve_right hab⟩
  · rcases hib : ι b with _ | s
    · have hab : a ≠ b := by
        rintro rfl
        simp [hia] at hib
      rw [attachAdj_some_none ι E r₀ hia hib]
      show T.intersection (v r) l ≠ 0 ↔ _
      rw [T.intersection_symm, hlr r]
      exact ⟨Or.inl, fun h => h.resolve_right hab⟩
    · rw [attachAdj_some_some ι E r₀ hia hib, ← hE r s]
      show T.intersection (v r) (v s) ≠ 0 ↔ _
      rw [hpair r s]
      refine ⟨fun h => h.imp id fun hrs => hιinj (by rw [hia, hib, hrs]), ?_⟩
      rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr (Option.some_injective _ (hia.symm.trans hib))

/-- A numerical type which is a Dynkin configuration `v` of shape `d` together with one further
component `l` attached at the vertex `r₀` matches a coefficient table as soon as some ordering
`ι` of all of its components realises the table: `ι a = some r` puts the `r`-th vertex of the
diagram at position `a` and `ι a = none` puts `l` there.

The multiplicities and weights enter as coefficient vectors `mv`, `wv` over the vertices of the
diagram together with the two coefficients `mcl`, `wcl` of `l`, so that the three conditions
relating them to the table — `hmc`, `hwc` and the three conditions on the intersection table —
are arithmetic in the coefficients alone, with no numerical type in sight. The intersection
table is checked only against the adjacency `AttachAdj ι E r₀`, where `E` is any relation
spelling out the edges of `d`. -/
public lemma matchesCoefficients_of_erase_leaf {t N : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x) (hcard : N = T.componentCount)
    (ι : Fin N → Option (Fin t)) (hιinj : Function.Injective ι)
    (E : Fin t → Fin t → Prop) (hE : ∀ r s, d.Edge r s ↔ E r s)
    (mv wv : Fin t → ℤ) (mcl wcl m W : ℤ) (hm : 0 < m) (hW : 0 < W)
    (hmv : ∀ r, T.multiplicity (v r) = mv r * m) (hml : T.multiplicity l = mcl * m)
    (hwv : ∀ r, T.weight (v r) = wv r * W) (hwl : T.weight l = wcl * W)
    (mc wc : Fin N → ℤ) (ac : Fin N → Fin N → ℤ)
    (hmc : ∀ a, (ι a).elim mcl mv = mc a) (hwc : ∀ a, (ι a).elim wcl wv = wc a)
    (hdiag : ∀ a, ac a a = -2 * wc a)
    (hedge : ∀ a b, a ≠ b → AttachAdj ι E r₀ a b → ac a b = max (wc a) (wc b))
    (hzero : ∀ a b, a ≠ b → ¬ AttachAdj ι E r₀ a b → ac a b = 0) :
    MatchesCoefficients T N mc wc ac := by
  classical
  have hmul : ∀ a : Fin N, T.multiplicity ((ι a).elim l v) = mc a * m := by
    intro a
    rw [← hmc a]
    rcases hia : ι a with _ | r
    · exact hml
    · exact hmv r
  have hwt : ∀ a : Fin N, T.weight ((ι a).elim l v) = wc a * W := by
    intro a
    rw [← hwc a]
    rcases hia : ι a with _ | r
    · exact hwl
    · exact hwv r
  obtain ⟨hpair, hlr, hll⟩ := intersection_ne_zero_iff_of_erase_leaf T hn hminus l x hlx hleaf
    v hvinj hvl d w hcfg r₀ hr₀
  have hv' : Function.Injective fun a : Fin N => (ι a).elim l v := by
    intro a b hab
    simp only at hab
    rcases hia : ι a with _ | r
    · rcases hib : ι b with _ | s
      · exact hιinj (by rw [hia, hib])
      · rw [hia, hib] at hab
        exact absurd hab.symm (hvl s)
    · rcases hib : ι b with _ | s
      · rw [hia, hib] at hab
        exact absurd hab (hvl r)
      · rw [hia, hib] at hab
        exact hιinj (by rw [hia, hib, hvinj hab])
  exact matchesCoefficients_of_ordering T hcard (fun a => (ι a).elim l v) hv'
    mc wc ac (fun _ => 0) m W hm hW hmul hwt
    (intersection_eq_of_adjacency T hn hminus (fun a => (ι a).elim l v) hv' (AttachAdj ι E r₀)
      (intersection_optionElim_ne_zero_iff T l v d r₀ ι hιinj E hE hpair hlr hll)
      wc ac W hW hwt hdiag hedge hzero)
    (fun a => (hminus _).1)

namespace GenusOne

/-! ### The intersection tables of the unbounded fork families -/

/-- The positions joined in the two single-fork families `forkUp` and `forkDown`: consecutive
positions along the main chain `0, …, n - 2`, together with the branch joining `n - 3` to
`n - 1`. -/
public def ForkAdj (n a b : ℕ) : Prop :=
  ((a + 1 = b ∨ b + 1 = a) ∧ a + 1 < n ∧ b + 1 < n) ∨
    (a + 3 = n ∧ b + 1 = n) ∨ (b + 3 = n ∧ a + 1 = n)

/-- The positions joined in the double-fork family: consecutive positions along the main chain
`2, …, n - 2`, the two prongs `0` and `1` attached to `2`, and the branch joining `n - 3` to
`n - 1`. -/
public def DoubleForkAdj (n a b : ℕ) : Prop :=
  (2 ≤ a ∧ 2 ≤ b ∧ (a + 1 = b ∨ b + 1 = a) ∧ a + 1 < n ∧ b + 1 < n) ∨
    (a + 3 = n ∧ b + 1 = n) ∨ (b + 3 = n ∧ a + 1 = n) ∨
    ((a = 0 ∨ a = 1) ∧ b = 2) ∨ ((b = 0 ∨ b = 1) ∧ a = 2)

/-- Off the diagonal, the intersection coefficient of an unbounded family is the edge coefficient
read with the smaller endpoint first. -/
private lemma longIntersection_eq_longEdge {n : ℕ} (f : LongFamily) (a b : Fin n) (hab : a ≠ b) :
    (a.val < b.val ∧ longIntersection f n a b = longEdge f n a.val b.val) ∨
      (b.val < a.val ∧ longIntersection f n a b = longEdge f n b.val a.val) := by
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  simp only [longIntersection, if_neg hab]
  rcases Nat.lt_or_ge a.val b.val with hlt | hge
  · exact Or.inl ⟨hlt, by rw [min_eq_left hlt.le, max_eq_right hlt.le]⟩
  · exact Or.inr ⟨by omega, by rw [min_eq_right hge, max_eq_left hge]⟩

/-- Along an edge of a single-fork family the intersection coefficient is the larger of the two
endpoint weight coefficients. -/
public lemma longIntersection_fork_eq_max {n : ℕ} (hn : 6 ≤ n) (f : LongFamily)
    (hf : f = .forkUp ∨ f = .forkDown) (a b : Fin n) (hab : a ≠ b)
    (hadj : ForkAdj n a.val b.val) :
    longIntersection f n a b = max (longWeight f n a) (longWeight f n b) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [ForkAdj] at hadj
  rcases longIntersection_eq_longEdge f a b hab with ⟨hlt, h⟩ | ⟨hlt, h⟩ <;> rw [h] <;>
    rcases hf with rfl | rfl <;> simp only [longEdge, longWeight] <;> split_ifs <;> omega

/-- Away from its edges the intersection coefficient of a single-fork family vanishes. -/
public lemma longIntersection_fork_eq_zero {n : ℕ} (hn : 6 ≤ n) (f : LongFamily)
    (hf : f = .forkUp ∨ f = .forkDown) (a b : Fin n) (hab : a ≠ b)
    (hadj : ¬ ForkAdj n a.val b.val) : longIntersection f n a b = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [ForkAdj, not_or, not_and_or] at hadj
  rcases longIntersection_eq_longEdge f a b hab with ⟨hlt, h⟩ | ⟨hlt, h⟩ <;> rw [h] <;>
    rcases hf with rfl | rfl <;> simp only [longEdge] <;> split_ifs <;> omega

/-- Along an edge of the double-fork family the intersection coefficient is the larger of the
two endpoint weight coefficients, both being one. -/
public lemma longIntersection_doubleFork_eq_max {n : ℕ} (hn : 6 ≤ n) (a b : Fin n) (hab : a ≠ b)
    (hadj : DoubleForkAdj n a.val b.val) :
    longIntersection .doubleFork n a b
      = max (longWeight .doubleFork n a) (longWeight .doubleFork n b) := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [DoubleForkAdj] at hadj
  rcases longIntersection_eq_longEdge .doubleFork a b hab with ⟨hlt, h⟩ | ⟨hlt, h⟩ <;> rw [h] <;>
    simp only [longEdge, longWeight] <;> split_ifs <;> omega

/-- Away from its edges the intersection coefficient of the double-fork family vanishes. -/
public lemma longIntersection_doubleFork_eq_zero {n : ℕ} (hn : 6 ≤ n) (a b : Fin n)
    (hab : a ≠ b) (hadj : ¬ DoubleForkAdj n a.val b.val) :
    longIntersection .doubleFork n a b = 0 := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [DoubleForkAdj, not_or, not_and_or] at hadj
  rcases longIntersection_eq_longEdge .doubleFork a b hab with ⟨hlt, h⟩ | ⟨hlt, h⟩ <;> rw [h] <;>
    simp only [longEdge] <;> split_ifs <;> omega

end GenusOne

end NumericalType

end AlgebraicGeometry
