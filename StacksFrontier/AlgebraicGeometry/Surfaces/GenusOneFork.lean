module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkChain
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkD
public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneForkE

/-!
# Minimal numerical types of genus one with a component meeting three or more others

A minimal numerical type of genus one with at least five components, one of which meets three or
more others, cannot have all its components meeting at least two others: the degree count of
`AlgebraicGeometry.NumericalType.neighborCount_eq_two_of_two_le_neighborCount` would make every
degree exactly two. So some component meets exactly one other, and deleting it leaves a Dynkin
configuration on one fewer component together with that component attached at a single vertex —
the affine extension system of
`AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf`.

This file solves that system for every shape at once, assembling the shape-by-shape solutions of
the three preceding files. The component meeting three others constrains the shape and the
attachment vertex: a chain-shaped diagram must be attached at an *interior* vertex, since
otherwise the resulting type is again a chain and no component meets three others. The outcome
is that the shape, the attachment vertex and the level are pinned to seven possibilities, which
are the configurations of cases (22), (23), (24), (29), (30), (31), (32), (33) and (34) of the
source's list:

* type `D`, attached at the first or second vertex of the long arm with level `2` and `1` — the
  forks of cases (23), (24), (29), (30) and the double fork of cases (22) and (31);
* type `D` on `t` vertices attached at one of the two one-vertex arms with `k t = 8`, so
  `t = 4` or `t = 8`;
* type `B` or type `C` attached at the second vertex with level `1` — the forks again;
* type `A` on seven or eight vertices attached at an interior vertex with level `1`, the only
  solutions of `k i (N - i) = 2 N` with `N ≥ 5` — the completed `E₇` and `E₈`;
* the diagrams `E₆`, `E₇` and `E₈` attached at one explicit vertex with level `1` — the
  completed `E₆`, `E₇` and `E₈` of cases (32), (33) and (34).

## Main results

* `AlgebraicGeometry.solve_chain_diophantine` — the only solutions of `k I Q = 2 (I + Q)` with
  `k ∈ {1, 2, 3}`, `I, Q ≥ 2` and `I + Q ≥ 5`.
* `AlgebraicGeometry.NumericalType.exists_leaf_of_three_le_neighborCount` — a component meeting
  exactly one other exists as soon as one meets three or more.
* `AlgebraicGeometry.NumericalType.exists_affine_extension_of_three_le_neighborCount` — the
  seven possibilities.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-! ### The Diophantine condition of a chain -/

/-- The only solutions of `k I Q = 2 (I + Q)` with `k ∈ {1, 2, 3}` and `I, Q ≥ 2` whose sum
`I + Q` is at least five are `k = 1` and `(I, Q) = (3, 6)`, `(4, 4)` or `(6, 3)`. -/
public lemma solve_chain_diophantine {I Q k : ℤ} (hI : 2 ≤ I) (hQ : 2 ≤ Q)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) (hN : 5 ≤ I + Q) (heq : k * I * Q = 2 * (I + Q)) :
    k = 1 ∧ ((I = 3 ∧ Q = 6) ∨ (I = 4 ∧ Q = 4) ∨ (I = 6 ∧ Q = 3)) := by
  rcases hk with rfl | rfl | rfl
  · have h4 : (I - 2) * (Q - 2) = 4 := by linear_combination heq
    have hI3 : 3 ≤ I := by nlinarith
    have hQ3 : 3 ≤ Q := by nlinarith
    have hI6 : I ≤ 6 := by nlinarith
    have hQ6 : Q ≤ 6 := by nlinarith
    refine ⟨rfl, ?_⟩
    interval_cases I <;> interval_cases Q <;> omega
  · exfalso
    have hI2 : I ≤ 2 := by nlinarith
    have hQ2 : Q ≤ 2 := by nlinarith
    omega
  · exfalso
    nlinarith

/-! ### Attachment at an interior vertex of a chain -/

/-- In a chain-shaped diagram, a vertex with two distinct neighbours is interior, and it has no
third neighbour; so if a vertex of the resulting numerical type meets three or more components,
the attachment vertex is that vertex, and it is interior. -/
public lemma chain_attachment_interior {t : ℕ} (d : DynkinShape)
    (hchain : ∀ r s : Fin t, d.Edge r s ↔ (r.val + 1 = s.val ∨ s.val + 1 = r.val))
    (r r₀ a b : Fin t) (hab : a ≠ b) (ha : d.Edge r a) (hb : d.Edge r b)
    (hthird : r = r₀ ∨ ∃ c : Fin t, c ≠ a ∧ c ≠ b ∧ d.Edge r c) :
    1 ≤ r₀.val ∧ r₀.val + 2 ≤ t := by
  have ha' := (hchain r a).mp ha
  have hb' := (hchain r b).mp hb
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have hal := a.isLt
  have hbl := b.isLt
  have hrl := r.isLt
  rcases hthird with h | ⟨c, hca, hcb, hc⟩
  · rw [← h]; omega
  · exfalso
    have hc' := (hchain r c).mp hc
    have hca' : c.val ≠ a.val := fun h => hca (Fin.ext h)
    have hcb' : c.val ≠ b.val := fun h => hcb (Fin.ext h)
    omega

namespace NumericalType

/-! ### Existence of a component meeting exactly one other -/

/-- A minimal numerical type of genus one with at least five components, one of which meets
three or more others, has a component meeting exactly one other: were every degree at least two,
the degree count would make every degree exactly two. -/
public lemma exists_leaf_of_three_le_neighborCount (T : NumericalType) (hmin : IsMinimal T)
    (hgenus : genus T = 1) (hn : 5 ≤ T.componentCount) (i₀ : Fin T.componentCount)
    (hdeg : 3 ≤ neighborCount T i₀) : ∃ l, neighborCount T l = 1 := by
  by_contra hcon
  push Not at hcon
  have hdeg2 : ∀ i, 2 ≤ neighborCount T i := by
    intro i
    have h1 := one_le_neighborCount T (by omega) i
    have h2 := hcon i
    omega
  have h := neighborCount_eq_two_of_two_le_neighborCount T hmin hgenus (by omega) hdeg2 i₀
  omega

/-! ### The seven affine extensions -/

/-- **Stacks Project, Tag 0C8T**, the reduction for a component meeting three or more others.
In a minimal numerical type of genus one with at least five components, one of which meets three
or more others, some component `l` meets exactly one other component `x`; the remaining
components carry a Dynkin configuration `v` of shape `d` and scale `w` with `x = v r₀`, their
multiplicities are annihilated by the weighted Cartan matrix of `d` away from `r₀` and satisfy
`2 (M m)_{r₀} = k wf(r₀) m_{r₀}` there; and the shape, the attachment vertex and the level are
one of seven explicit possibilities. -/
@[stacks 0C8T "the reduction for at least five components one of which meets three or more others — cases (22), (23), (24), (29), (30), (31), (32), (33) and (34): deleting a component that meets exactly one other leaves a Dynkin configuration whose shape, attachment vertex and level are one of seven explicit possibilities"]
public theorem exists_affine_extension_of_three_le_neighborCount (T : NumericalType)
    (hmin : IsMinimal T) (hgenus : genus T = 1) (hn : 5 ≤ T.componentCount)
    (i₀ : Fin T.componentCount) (hdeg : 3 ≤ neighborCount T i₀) :
    ∃ (l x : Fin T.componentCount) (t : ℕ) (v : Fin t → Fin T.componentCount)
      (d : DynkinShape) (w : ℤ) (r₀ : Fin t) (k : ℤ),
      t + 1 = T.componentCount ∧ l ≠ x ∧
        (∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x) ∧
        Function.Injective v ∧ (∀ r, v r ≠ l) ∧ (∀ y, y ≠ l → ∃ r, v r = y) ∧
        IsDynkinConfiguration T v d w ∧ v r₀ = x ∧
        (∀ r, r ≠ r₀ → ∑ s, d.weightedCartan r s * T.multiplicity (v s) = 0) ∧
        2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)
          = k * d.weightFactor r₀ * T.multiplicity (v r₀) ∧
        ((d = .D ∧ ((r₀.val = 0 ∧ k = 2) ∨ (r₀.val = 1 ∧ k = 1) ∨
              ((r₀.val + 1 = t ∨ r₀.val + 2 = t) ∧ k * t = 8))) ∨
          (d = .B ∧ r₀.val = 1 ∧ k = 1) ∨ (d = .C ∧ r₀.val = 1 ∧ k = 1) ∨
          (d = .A ∧ k = 1 ∧ ((t = 7 ∧ r₀.val = 3) ∨ (t = 8 ∧ (r₀.val = 2 ∨ r₀.val = 5)))) ∨
          (d = .E6 ∧ r₀.val = 5 ∧ k = 1) ∨ (d = .E7 ∧ r₀.val = 5 ∧ k = 1) ∨
          (d = .E8 ∧ r₀.val = 0 ∧ k = 1)) := by
  classical
  have hminus : ∀ i, IsMinusTwoIndex T i :=
    forall_isMinusTwoIndex_of_isMinimal_of_genus_eq_one T hmin hgenus (by omega)
  obtain ⟨l, hl⟩ := exists_leaf_of_three_le_neighborCount T hmin hgenus hn i₀ hdeg
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hl
  have hxmem : x ∈ neighbors T l := by rw [hx]; exact Finset.mem_singleton_self x
  have hlx : l ≠ x := ((mem_neighbors_iff T l x).mp hxmem).1
  have hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x := by
    intro y hyl hint
    have hymem : y ∈ neighbors T l :=
      (mem_neighbors_iff T l y).mpr ⟨fun h => hyl h.symm, hint⟩
    rw [hx] at hymem
    exact Finset.mem_singleton.mp hymem
  obtain ⟨t, v, ht1, hvinj, hvl, hvsurj, d, w, hcfg⟩ :=
    exists_dynkinConfiguration_of_erase_leaf T hmin hgenus (by omega) l x hlx hleaf
  obtain ⟨r₀, hr₀⟩ := hvsurj x (Ne.symm hlx)
  obtain ⟨k, hk, hrest, hmain, -⟩ := affine_system_of_erase_leaf T (by omega) hminus l x hlx
    hleaf v hvinj hvl hvsurj d w hcfg r₀ hr₀
  have hpos : ∀ r : Fin t, 0 < T.multiplicity (v r) := fun r => T.multiplicity_pos _
  have hint : ∀ (hchain : ∀ r s : Fin t, d.Edge r s ↔ (r.val + 1 = s.val ∨ s.val + 1 = r.val)),
      1 ≤ r₀.val ∧ r₀.val + 2 ≤ t := by
    intro hchain
    obtain ⟨r, -, a, b, hab, ha, hb, hthird⟩ :=
      exists_two_edge_of_three_le_neighborCount T l x hleaf v hvinj hvsurj d w hcfg r₀ hr₀ i₀ hdeg
    exact chain_attachment_interior d hchain r r₀ a b hab ha hb hthird
  refine ⟨l, x, t, v, d, w, r₀, k, ht1, hlx, hleaf, hvinj, hvl, hvsurj, hcfg, hr₀, hrest,
    hmain, ?_⟩
  cases d with
  | A =>
      obtain ⟨hlo, hhi⟩ := hint (fun _ _ => Iff.rfl)
      obtain ⟨hdio, -⟩ := affine_system_solved_A (by omega) (fun r => T.multiplicity (v r))
        hpos r₀ k hrest hmain
      obtain ⟨hk1, hcases⟩ := solve_chain_diophantine (I := (r₀.val : ℤ) + 1)
        (Q := (t : ℤ) - r₀.val) (by omega) (by omega) hk (by omega) (by linarith [hdio])
      refine Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, hk1, ?_⟩)))
      rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, Or.inr (by omega)⟩
  | B =>
      obtain ⟨hlo, hhi⟩ := hint (fun _ _ => Iff.rfl)
      obtain ⟨h1, h2, -⟩ := affine_system_solved_B (by omega)
        (fun r => T.multiplicity (v r)) hpos r₀ k hlo hhi hrest hmain
      exact Or.inr (Or.inl ⟨rfl, h1, h2⟩)
  | C =>
      obtain ⟨hlo, hhi⟩ := hint (fun _ _ => Iff.rfl)
      obtain ⟨h1, h2, -⟩ := affine_system_solved_C (by omega)
        (fun r => T.multiplicity (v r)) hpos r₀ k hlo hhi hrest hmain
      exact Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2⟩))
  | D =>
      obtain ⟨a, -, hcases⟩ := affine_system_solved_D (show 4 ≤ t from hcfg.1)
        (fun r => T.multiplicity (v r)) hpos r₀ k hrest hmain
      refine Or.inl ⟨rfl, ?_⟩
      rcases hcases with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inl ⟨h1, h2⟩)
      · exact Or.inr (Or.inr ⟨Or.inl h1, h2⟩)
      · exact Or.inr (Or.inr ⟨Or.inr h1, h2⟩)
  | E6 =>
      have ht6 : t = 6 := hcfg.1
      subst ht6
      obtain ⟨h1, h2, -⟩ := affine_system_solved_E6 (fun r => T.multiplicity (v r)) hpos r₀ k
        hrest hmain
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2⟩))))
  | E7 =>
      have ht7 : t = 7 := hcfg.1
      subst ht7
      obtain ⟨h1, h2, -⟩ := affine_system_solved_E7 (fun r => T.multiplicity (v r)) hpos r₀ k
        hrest hmain
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h1, h2⟩)))))
  | E8 =>
      have ht8 : t = 8 := hcfg.1
      subst ht8
      obtain ⟨h1, h2, -⟩ := affine_system_solved_E8 (fun r => T.multiplicity (v r)) hpos r₀ k
        hrest hmain
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h1, h2⟩)))))
  | F4 =>
      obtain ⟨hlo, hhi⟩ := hint (fun _ _ => Iff.rfl)
      have ht4 : t = 4 := hcfg.1
      subst ht4
      exact absurd (not_affine_system_F4 (fun r => T.multiplicity (v r)) hpos r₀ k hlo hhi
        hrest hmain) (fun h => h)
  | G2 =>
      have ht2 : t = 2 := hcfg.1
      omega

end NumericalType

end AlgebraicGeometry
