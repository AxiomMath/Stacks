module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Composing a subinterval inclusion with a coface map

`SimplexCategory.subinterval j l hjl : ⦋l⦌ ⟶ ⦋n⦌` is the inclusion of the subinterval
`{j, …, j + l}` of `⦋n⦌`. Two families of these occur in the Alexander–Whitney map of a pair of
simplicial objects: the *front face* `subinterval 0 a _ : ⦋a⦌ ⟶ ⦋n⦌`, which keeps the first
`a + 1` vertices, and the *back face* `subinterval a b _ : ⦋b⦌ ⟶ ⦋n⦌` with `a + b = n`, which
keeps the last `b + 1` vertices.

This file records how these two families compose with a coface map `δ i : ⦋n⦌ ⟶ ⦋n + 1⦌`. The
answer depends on the position of `i` relative to the cut point `a`: on one side of the cut the
new vertex is absorbed by the inclusion, on the other side it is absorbed by a coface map of the
shorter simplex. Together with the two statements lowering the length of a face by one, these are
the simplicial identities behind the Alexander–Whitney chain map.

## Main results

* `SimplexCategory.subinterval_zero_comp_δ_of_le` and `SimplexCategory.subinterval_comp_δ_of_le`:
  for `i ≤ a` the front face absorbs the coface `δ i` of `⦋a⦌` and the back face is unchanged
  apart from the shift of its starting vertex.
* `SimplexCategory.subinterval_zero_comp_δ_of_lt` and `SimplexCategory.subinterval_comp_δ_of_lt`:
  for `a < i` the front face is unchanged, and the back face absorbs the coface `δ (i - a)` of
  `⦋b⦌`.
* `SimplexCategory.subinterval_zero_self`: the front face of full length is the identity.
* `SimplexCategory.δ_last_comp_subinterval_zero` and `SimplexCategory.δ_zero_comp_subinterval`:
  the last coface map shortens a front face by one vertex, and the zeroth coface map shortens a
  back face by one vertex.
-/

@[expose] public section

open CategoryTheory

open scoped Simplicial

namespace SimplexCategory

/-- The value of a subinterval inclusion at a vertex, as a natural number. -/
public lemma subinterval_apply_val {n : ℕ} (j l : ℕ) (hjl : j + l ≤ n) (i : Fin (l + 1)) :
    ((subinterval j l hjl).toOrderHom i : ℕ) = (i : ℕ) + j := rfl

/-- The value of a coface map at a vertex, as a natural number. -/
public lemma δ_apply_val {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    (((δ i).toOrderHom k : Fin (n + 2)) : ℕ) =
      if (k : ℕ) < (i : ℕ) then (k : ℕ) else (k : ℕ) + 1 :=
  apply_ite Fin.val (k.castSucc < i) k.castSucc k.succ

/-- The front face with as many vertices as the target is the identity. -/
public lemma subinterval_zero_self (n : ℕ) (hn : 0 + n ≤ n) : subinterval 0 n hn = 𝟙 ⦋n⦌ := by
  ext x : 3
  refine Fin.val_injective ?_
  rw [subinterval_apply_val]
  simp

/-- Below the cut the front face absorbs a coface map of its own source: for `i ≤ a` and `j` the
vertex of `⦋a + 1⦌` with the same index as `i`, the composite of the front face `⦋a⦌ ⟶ ⦋n⦌` with
`δ i` is `δ j` followed by the longer front face `⦋a + 1⦌ ⟶ ⦋n + 1⦌`. -/
public lemma subinterval_zero_comp_δ_of_le {n a : ℕ} (hn : 0 + a ≤ n) (hn' : 0 + (a + 1) ≤ n + 1)
    (i : Fin (n + 2)) (j : Fin (a + 2)) (hij : (i : ℕ) = (j : ℕ)) :
    subinterval 0 a hn ≫ δ i = δ j ≫ subinterval 0 (a + 1) hn' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  have hx : (x : ℕ) ≤ a := x.is_le
  rw [δ_apply_val, subinterval_apply_val, subinterval_apply_val, δ_apply_val]
  split_ifs <;> omega

/-- Above the cut the front face is unchanged by a coface map: for `a < i` the composite of the
front face `⦋a⦌ ⟶ ⦋n⦌` with `δ i` is the front face `⦋a⦌ ⟶ ⦋n + 1⦌`. -/
public lemma subinterval_zero_comp_δ_of_lt {n a : ℕ} (hn : 0 + a ≤ n) (hn' : 0 + a ≤ n + 1)
    (i : Fin (n + 2)) (hi : a < (i : ℕ)) :
    subinterval 0 a hn ≫ δ i = subinterval 0 a hn' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  have hx : (x : ℕ) ≤ a := x.is_le
  rw [δ_apply_val, subinterval_apply_val, subinterval_apply_val]
  split_ifs <;> omega

/-- Below the cut the back face is unchanged by a coface map, apart from the shift of its
starting vertex: for `i ≤ a` the composite of the back face `⦋b⦌ ⟶ ⦋n⦌` starting at `a` with
`δ i` is the back face `⦋b⦌ ⟶ ⦋n + 1⦌` starting at `a + 1`. -/
public lemma subinterval_comp_δ_of_le {n a b : ℕ} (hn : a + b ≤ n) (hn' : a + 1 + b ≤ n + 1)
    (i : Fin (n + 2)) (hi : (i : ℕ) ≤ a) :
    subinterval a b hn ≫ δ i = subinterval (a + 1) b hn' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  rw [δ_apply_val, subinterval_apply_val, subinterval_apply_val]
  split_ifs <;> omega

/-- Above the cut the back face absorbs a coface map of its own source: for `a < i` and `k` the
vertex of `⦋b + 1⦌` of index `i - a`, the composite of the back face `⦋b⦌ ⟶ ⦋n⦌` starting at `a`
with `δ i` is `δ k` followed by the longer back face `⦋b + 1⦌ ⟶ ⦋n + 1⦌` starting at `a`. -/
public lemma subinterval_comp_δ_of_lt {n a b : ℕ} (hn : a + b ≤ n) (hn' : a + (b + 1) ≤ n + 1)
    (i : Fin (n + 2)) (k : Fin (b + 2)) (hik : (i : ℕ) = (k : ℕ) + a) :
    subinterval a b hn ≫ δ i = δ k ≫ subinterval a (b + 1) hn' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  rw [δ_apply_val, subinterval_apply_val, subinterval_apply_val, δ_apply_val]
  split_ifs <;> omega

/-- The last coface map of `⦋a + 1⦌` shortens a front face by one vertex. -/
public lemma δ_last_comp_subinterval_zero {m a : ℕ} (hm : 0 + (a + 1) ≤ m) (hm' : 0 + a ≤ m)
    (j : Fin (a + 2)) (hj : (j : ℕ) = a + 1) :
    δ j ≫ subinterval 0 (a + 1) hm = subinterval 0 a hm' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  have hx : (x : ℕ) ≤ a := x.is_le
  rw [subinterval_apply_val, δ_apply_val, subinterval_apply_val,
    if_pos (show (x : ℕ) < (j : ℕ) by omega)]

/-- The zeroth coface map of `⦋b + 1⦌` shortens a back face by one vertex, moving its starting
vertex forward by one. -/
public lemma δ_zero_comp_subinterval {m a b : ℕ} (hm : a + (b + 1) ≤ m) (hm' : a + 1 + b ≤ m)
    (k : Fin (b + 2)) (hk : (k : ℕ) = 0) :
    δ k ≫ subinterval a (b + 1) hm = subinterval (a + 1) b hm' := by
  ext x : 3
  simp only [comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  refine Fin.val_injective ?_
  rw [subinterval_apply_val, δ_apply_val, subinterval_apply_val,
    if_neg (show ¬ (x : ℕ) < (k : ℕ) by omega)]
  omega

end SimplexCategory
