module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKSymbols

/-!
# Products of degree-one symbols generate the Milnor K-groups

The degree-`n` Milnor K-group of a field is by construction the image in the Steinberg quotient
of the degree-`n` part of the tensor algebra on `kˣ`, which is the `n`-th power of the range of
the canonical generator map. So it is generated, as an additive group, by the products

`{u_1, …, u_n} = {u_1} ⋯ {u_n}`

of `n` degree-one symbols. This file defines those products, `milnorKSymbolProd`, and proves the
generation statement: an additive subgroup of the Milnor K-ring containing every symbol product
contains every homogeneous component (`milnorKGrading_le_of_forall_milnorKSymbolProd_mem`).

## Main definitions

* `milnorKSymbolProd` — the symbol `{u_1, …, u_r}` of a list of units.

## Main results

* `milnorKSymbolProd_mem_milnorKGrading` — a product of `r` symbols is homogeneous of degree `r`.
* `milnorKGrading_le_of_forall_milnorKSymbolProd_mem` — the symbol products generate.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public section

universe u

variable {k : Type u} [Field k]

/-- The symbol `{u_1, …, u_r}` in the Milnor K-ring: the product of the degree-one symbols of a
list of units of `k`. It is homogeneous of degree the length of the list. -/
def milnorKSymbolProd (k : Type u) [Field k] (l : List kˣ) : MilnorKRing k :=
  (l.map (milnorKSymbol k)).prod

/-- The symbol of the empty list of units is `1`. -/
@[simp]
theorem milnorKSymbolProd_nil : milnorKSymbolProd k [] = 1 := rfl

/-- `{u, u_1, …, u_r} = {u} * {u_1, …, u_r}`. -/
@[simp]
theorem milnorKSymbolProd_cons (u : kˣ) (l : List kˣ) :
    milnorKSymbolProd k (u :: l) = milnorKSymbol k u * milnorKSymbolProd k l := rfl

/-- The symbol of a one-element list `[u]` is the degree-one symbol `{u}`. -/
@[simp]
theorem milnorKSymbolProd_singleton (u : kˣ) :
    milnorKSymbolProd k [u] = milnorKSymbol k u := by
  rw [milnorKSymbolProd_cons, milnorKSymbolProd_nil, mul_one]

/-- The symbol of a concatenation of lists is the product of their symbols. -/
theorem milnorKSymbolProd_append (l l' : List kˣ) :
    milnorKSymbolProd k (l ++ l') = milnorKSymbolProd k l * milnorKSymbolProd k l' := by
  rw [milnorKSymbolProd, milnorKSymbolProd, milnorKSymbolProd, List.map_append, List.prod_append]

/-- The symbol of a list of `r` units is homogeneous of degree `r`. -/
theorem milnorKSymbolProd_mem_milnorKGrading (l : List kˣ) :
    milnorKSymbolProd k l ∈ milnorKGrading k l.length := by
  induction l with
  | nil => simpa using SetLike.one_mem_graded (A := milnorKGrading k)
  | cons u l ih =>
      rw [milnorKSymbolProd_cons, List.length_cons]
      have hmul := SetLike.mul_mem_graded (milnorKSymbol_mem_milnorKGrading u) ih
      rwa [add_comm] at hmul

/-! ### Generation -/

private theorem mk'_mem_of_mem_milnorKTensorGrading :
    ∀ (n : ℕ) {H : AddSubgroup (MilnorKRing k)},
      (∀ l : List kˣ, milnorKSymbolProd k l ∈ H) →
      ∀ {t : MilnorKTensorAlgebra k}, t ∈ milnorKTensorGrading k n →
        (milnorKSteinbergIdeal k).ringCon.mk' t ∈ H := by
  intro n
  induction n with
  | zero =>
      intro H hH t ht
      rw [milnorKTensorGrading, pow_zero, Submodule.one_eq_range] at ht
      obtain ⟨r, rfl⟩ := ht
      have hval : (milnorKSteinbergIdeal k).ringCon.mk'
          ((Algebra.linearMap ℤ (MilnorKTensorAlgebra k)) r) = r • (1 : MilnorKRing k) := by
        change (milnorKSteinbergIdeal k).ringCon.mk'
          (algebraMap ℤ (MilnorKTensorAlgebra k) r) = _
        rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]
      rw [hval]
      exact zsmul_mem (by simpa using hH []) r
  | succ n ih =>
      intro H hH t ht
      rw [milnorKTensorGrading, pow_succ] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro a ha b hb
        obtain ⟨m, rfl⟩ := hb
        have hmul : (milnorKSteinbergIdeal k).ringCon.mk' (a * TensorAlgebra.ι ℤ m) =
            (milnorKSteinbergIdeal k).ringCon.mk' a *
              milnorKSymbol k (Additive.toMul m) := map_mul _ _ _
        rw [hmul]
        refine ih (H := AddSubgroup.comap
          (AddMonoidHom.mulRight (milnorKSymbol k (Additive.toMul m))) H) ?_ ha
        intro l
        change milnorKSymbolProd k l * milnorKSymbol k (Additive.toMul m) ∈ H
        rw [← milnorKSymbolProd_singleton (Additive.toMul m), ← milnorKSymbolProd_append]
        exact hH _
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb

/-- **The symbol products generate the Milnor K-groups.** An additive subgroup of the Milnor
K-ring which contains every product of degree-one symbols contains every homogeneous
component. -/
theorem milnorKGrading_le_of_forall_milnorKSymbolProd_mem {H : AddSubgroup (MilnorKRing k)}
    (hH : ∀ l : List kˣ, milnorKSymbolProd k l ∈ H) (n : ℕ) : milnorKGrading k n ≤ H := by
  rintro _ ⟨t, ht, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup] at ht
  exact mk'_mem_of_mem_milnorKTensorGrading n hH ht

/-- The class of any element of a degree-`n` Milnor K-group lies in an additive subgroup which
contains every symbol product. -/
theorem coe_mem_of_forall_milnorKSymbolProd_mem {H : AddSubgroup (MilnorKRing k)}
    (hH : ∀ l : List kˣ, milnorKSymbolProd k l ∈ H) {n : ℕ} (α : MilnorKTheory k n) :
    (α : MilnorKRing k) ∈ H :=
  milnorKGrading_le_of_forall_milnorKSymbolProd_mem hH n α.2
