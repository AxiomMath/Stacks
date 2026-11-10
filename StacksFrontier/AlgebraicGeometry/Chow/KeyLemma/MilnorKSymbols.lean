module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NoncommRing
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKTheory

/-!
# Symbols in the Milnor K-ring of a field

`MilnorKRing k` is the quotient of the tensor algebra on `kˣ` by the Steinberg ideal, and its
degree-one part is the image of `kˣ`. The image of a unit `u` is the symbol `{u}`,
`milnorKSymbol k u`. It satisfies the following relations:

* `{u v} = {u} + {v}`, so `u ↦ {u}` is additive on `kˣ` read additively;
* `{u} {v} = 0` whenever `u + v = 1` in `k` (the Steinberg relation);
* `{u} {-u} = 0`;
* `{u} {v} + {v} {u} = 0`, so degree-one symbols anticommute.

The symbol `{-1}` is singled out as `milnorKNegOne k`. It is killed by `2` and is central.

## Main definitions

* `milnorKSymbol` — the symbol `{u} ∈ K^M_*(k)` of a unit `u` of `k`.
* `milnorKNegOne` — the symbol `{-1}`.

## Main results

* `milnorKSymbol_mul_steinberg` — the Steinberg relation `{u} {v} = 0` for `u + v = 1`.
* `milnorKSymbol_mul_neg_self` — `{u} {-u} = 0`.
* `milnorKSymbol_mul_add_mul_comm` — `{u} {v} + {v} {u} = 0`.
* `milnorKNegOne_add_self` — `{-1} + {-1} = 0`.
* `milnorKNegOne_mul_comm` — `{-1}` is central in `K^M_*(k)`.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public section

universe u

variable {k : Type u} [Field k]

/-! ### The quotient map -/

/-- An element of the Milnor tensor algebra dies in the Milnor K-ring exactly when it lies in
the Steinberg ideal. -/
theorem milnorKRing_mk'_eq_zero_iff {z : MilnorKTensorAlgebra k} :
    (milnorKSteinbergIdeal k).ringCon.mk' z = 0 ↔ z ∈ milnorKSteinbergIdeal k := by
  rw [← TwoSidedIdeal.mem_ker, TwoSidedIdeal.ker_ringCon_mk']

/-- Every element of the Milnor K-ring comes from the tensor algebra. -/
theorem milnorKRing_mk'_surjective (k : Type u) [Field k] :
    Function.Surjective (milnorKSteinbergIdeal k).ringCon.mk' :=
  RingCon.mk'_surjective _

/-! ### The degree-one symbol -/

/-- The symbol `{u}` of a unit `u` of `k`: the image in the Milnor K-ring of the degree-one
generator of the tensor algebra attached to `u`. It lies in `K^M_1(k)`. -/
def milnorKSymbol (k : Type u) [Field k] (u : kˣ) : MilnorKRing k :=
  (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ (Additive.ofMul u))

/-- The symbol `{u}` lies in the degree-one part `K^M_1(k)` of the Milnor K-ring. -/
theorem milnorKSymbol_mem_milnorKGrading (u : kˣ) :
    milnorKSymbol k u ∈ milnorKGrading k 1 := by
  refine ⟨TensorAlgebra.ι ℤ (Additive.ofMul u), ?_, rfl⟩
  change TensorAlgebra.ι ℤ (Additive.ofMul u) ∈
    ((LinearMap.range
      (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k)) ^ 1).toAddSubgroup
  simpa only [pow_one, Submodule.mem_toAddSubgroup] using
    LinearMap.mem_range_self
      (TensorAlgebra.ι ℤ : Additive kˣ →ₗ[ℤ] MilnorKTensorAlgebra k) (Additive.ofMul u)

/-- The symbol `{u}` is the image of the degree-one generator `ι u` of the tensor algebra. -/
theorem milnorKSymbol_eq_mk' (u : kˣ) :
    milnorKSymbol k u =
      (milnorKSteinbergIdeal k).ringCon.mk' (TensorAlgebra.ι ℤ (Additive.ofMul u)) := rfl

/-- `{u v} = {u} + {v}`. -/
@[simp]
theorem milnorKSymbol_mul (u v : kˣ) :
    milnorKSymbol k (u * v) = milnorKSymbol k u + milnorKSymbol k v := by
  simp only [milnorKSymbol_eq_mk', ofMul_mul, map_add]

/-- `{1} = 0`. -/
@[simp]
theorem milnorKSymbol_one : milnorKSymbol k 1 = 0 := by
  simp only [milnorKSymbol_eq_mk', ofMul_one, map_zero]

/-- `{u⁻¹} = -{u}`. -/
@[simp]
theorem milnorKSymbol_inv (u : kˣ) : milnorKSymbol k u⁻¹ = -milnorKSymbol k u := by
  rw [eq_neg_iff_add_eq_zero, ← milnorKSymbol_mul, inv_mul_cancel, milnorKSymbol_one]

/-- `{u ^ n} = n • {u}` for every integer `n`. -/
theorem milnorKSymbol_zpow (u : kˣ) (n : ℤ) :
    milnorKSymbol k (u ^ n) = n • milnorKSymbol k u := by
  simp only [milnorKSymbol_eq_mk', ofMul_zpow, map_zsmul]

/-- `{u / v} = {u} - {v}`. -/
theorem milnorKSymbol_div (u v : kˣ) :
    milnorKSymbol k (u / v) = milnorKSymbol k u - milnorKSymbol k v := by
  rw [div_eq_mul_inv, milnorKSymbol_mul, milnorKSymbol_inv, sub_eq_add_neg]

/-! ### The symbol `{-1}` -/

/-- The symbol `{-1} ∈ K^M_1(k)`. It is killed by `2` and is central in the Milnor K-ring. -/
def milnorKNegOne (k : Type u) [Field k] : MilnorKRing k := milnorKSymbol k (-1 : kˣ)

/-- `{-1}` is the symbol of the unit `-1`. -/
theorem milnorKNegOne_eq : milnorKNegOne k = milnorKSymbol k (-1 : kˣ) := rfl

/-- The symbol `{-1}` lies in `K^M_1(k)`. -/
theorem milnorKNegOne_mem_milnorKGrading :
    milnorKNegOne k ∈ milnorKGrading k 1 :=
  milnorKSymbol_mem_milnorKGrading _

/-- `{-1} + {-1} = 0`. -/
theorem milnorKNegOne_add_self : milnorKNegOne k + milnorKNegOne k = 0 := by
  rw [milnorKNegOne_eq, ← milnorKSymbol_mul,
    show ((-1 : kˣ) * (-1 : kˣ) : kˣ) = 1 by ext; simp, milnorKSymbol_one]

/-- `2 • {-1} = 0`. -/
theorem two_nsmul_milnorKNegOne : (2 : ℕ) • milnorKNegOne k = 0 := by
  rw [two_nsmul, milnorKNegOne_add_self]

/-- `{-1} x + {-1} x = 0` for every `x` in the Milnor K-ring. -/
theorem milnorKNegOne_add_self_mul (x : MilnorKRing k) :
    milnorKNegOne k * x + milnorKNegOne k * x = 0 := by
  rw [← add_mul, milnorKNegOne_add_self, zero_mul]

/-- `x {-1} + x {-1} = 0` for every `x` in the Milnor K-ring. -/
theorem mul_milnorKNegOne_add_self (x : MilnorKRing k) :
    x * milnorKNegOne k + x * milnorKNegOne k = 0 := by
  rw [← mul_add, milnorKNegOne_add_self, mul_zero]

/-! ### The Steinberg relation -/

/-- **The Steinberg relation.** If `u + v = 1` for units `u, v` of `k` then `{u} {v} = 0` in the
Milnor K-ring. -/
theorem milnorKSymbol_mul_steinberg {u v : kˣ} (h : (u : k) + (v : k) = 1) :
    milnorKSymbol k u * milnorKSymbol k v = 0 := by
  have hu1 : (u : k) ≠ 1 := fun hu => by simp [hu] at h
  obtain rfl : v = Units.mk0 (1 - (u : k)) (sub_ne_zero.mpr (Ne.symm hu1)) :=
    Units.ext (eq_sub_of_add_eq' h)
  rw [milnorKSymbol_eq_mk', milnorKSymbol_eq_mk', ← map_mul, milnorKRing_mk'_eq_zero_iff]
  refine TwoSidedIdeal.subset_span ⟨⟨(u : k), u.ne_zero, hu1⟩, ?_⟩
  simp only [Units.mk0_val]

/-- `{u} {-u} = 0`. -/
theorem milnorKSymbol_mul_neg_self (u : kˣ) :
    milnorKSymbol k u * milnorKSymbol k (-u) = 0 := by
  by_cases hu1 : (u : k) = 1
  · rw [show u = 1 from Units.ext hu1, milnorKSymbol_one, zero_mul]
  · have hu0 : (u : k) ≠ 0 := u.ne_zero
    have hsub : (1 : k) - (u : k) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    have hinv1 : ((u⁻¹ : kˣ) : k) ≠ 1 := by rwa [Units.val_inv_eq_inv_val, Ne, inv_eq_one]
    have hsubinv : (1 : k) - ((u⁻¹ : kˣ) : k) ≠ 0 := sub_ne_zero.mpr (Ne.symm hinv1)
    have key : ∀ (w : kˣ) (hw : (1 : k) - (w : k) ≠ 0),
        milnorKSymbol k w * milnorKSymbol k (Units.mk0 ((1 : k) - (w : k)) hw) = 0 :=
      fun w hw => milnorKSymbol_mul_steinberg (by simp)
    have h1 := key u hsub
    have h2' : milnorKSymbol k u *
        milnorKSymbol k (Units.mk0 ((1 : k) - ((u⁻¹ : kˣ) : k)) hsubinv) = 0 := by
      have h2 := key u⁻¹ hsubinv
      rwa [milnorKSymbol_inv, neg_mul, neg_eq_zero] at h2
    have hdiv : Units.mk0 ((1 : k) - (u : k)) hsub /
        Units.mk0 ((1 : k) - ((u⁻¹ : kˣ) : k)) hsubinv = -u := by
      refine Units.ext ?_
      rw [Units.val_div_eq_div_val, Units.val_neg, Units.val_mk0, Units.val_mk0,
        div_eq_iff hsubinv, Units.val_inv_eq_inv_val]
      field_simp
      ring
    calc milnorKSymbol k u * milnorKSymbol k (-u)
        = milnorKSymbol k u * (milnorKSymbol k (Units.mk0 ((1 : k) - (u : k)) hsub) -
            milnorKSymbol k (Units.mk0 ((1 : k) - ((u⁻¹ : kˣ) : k)) hsubinv)) := by
          rw [← milnorKSymbol_div, hdiv]
      _ = 0 := by rw [mul_sub, h1, h2', sub_zero]

/-- `{t} {t} + {t} {-1} = 0`. -/
theorem milnorKSymbol_mul_self_add_mul_negOne (t : kˣ) :
    milnorKSymbol k t * milnorKSymbol k t + milnorKSymbol k t * milnorKNegOne k = 0 := by
  have hneg : (-t : kˣ) = (-1 : kˣ) * t := by ext; simp
  have h := milnorKSymbol_mul_neg_self (k := k) t
  rw [hneg, milnorKSymbol_mul, mul_add, ← milnorKNegOne_eq] at h
  rwa [add_comm]

/-- **Degree-one symbols anticommute**: `{u} {v} + {v} {u} = 0`. -/
theorem milnorKSymbol_mul_add_mul_comm (u v : kˣ) :
    milnorKSymbol k u * milnorKSymbol k v + milnorKSymbol k v * milnorKSymbol k u = 0 := by
  have h := milnorKSymbol_mul_self_add_mul_negOne (k := k) (u * v)
  rw [milnorKSymbol_mul] at h
  have hu := milnorKSymbol_mul_self_add_mul_negOne (k := k) u
  have hv := milnorKSymbol_mul_self_add_mul_negOne (k := k) v
  have expand : milnorKSymbol k u * milnorKSymbol k v + milnorKSymbol k v * milnorKSymbol k u =
      ((milnorKSymbol k u + milnorKSymbol k v) * (milnorKSymbol k u + milnorKSymbol k v) +
        (milnorKSymbol k u + milnorKSymbol k v) * milnorKNegOne k) -
      (milnorKSymbol k u * milnorKSymbol k u + milnorKSymbol k u * milnorKNegOne k) -
      (milnorKSymbol k v * milnorKSymbol k v + milnorKSymbol k v * milnorKNegOne k) := by
    noncomm_ring
  rw [expand, h, hu, hv, sub_zero, sub_zero]

/-! ### Centrality of `{-1}` -/

/-- `{-1}` commutes with every degree-one symbol. -/
theorem milnorKNegOne_mul_symbol_comm (u : kˣ) :
    milnorKNegOne k * milnorKSymbol k u = milnorKSymbol k u * milnorKNegOne k := by
  have hanti := milnorKSymbol_mul_add_mul_comm (k := k) (-1 : kˣ) u
  rw [← milnorKNegOne_eq] at hanti
  have htwo := milnorKNegOne_add_self_mul (k := k) (milnorKSymbol k u)
  exact (add_left_cancel (hanti.trans htwo.symm)).symm

/-- **`{-1}` is central in the Milnor K-ring.** -/
theorem milnorKNegOne_mul_comm (x : MilnorKRing k) :
    milnorKNegOne k * x = x * milnorKNegOne k := by
  obtain ⟨t, rfl⟩ := milnorKRing_mk'_surjective k x
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
      have hr : (milnorKSteinbergIdeal k).ringCon.mk'
          ((algebraMap ℤ (MilnorKTensorAlgebra k)) r) = r • (1 : MilnorKRing k) := by
        rw [Algebra.algebraMap_eq_smul_one, map_zsmul, map_one]
      rw [hr, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  | ι y =>
      exact milnorKNegOne_mul_symbol_comm (Additive.toMul y)
  | mul a b ha hb =>
      rw [map_mul, ← mul_assoc, ha, mul_assoc, hb, ← mul_assoc]
  | add a b ha hb =>
      rw [map_add, mul_add, add_mul, ha, hb]
