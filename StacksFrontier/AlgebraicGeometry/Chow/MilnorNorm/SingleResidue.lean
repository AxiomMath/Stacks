module

public import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueSurjectivity

/-!
# A class of `K^M_*(k[X] ⧸ φ)` is the residue of a class with no other residue

Let `k` be a field and `φ ∈ k[X]` monic irreducible. This file completes the surjectivity half of
Milnor's exact sequence for `K^M_*(RatFunc k)`: **every class `α ∈ K^M_i(k[X] ⧸ φ)` is the
residue at `φ` of a class `y ∈ K^M_{i+1}(RatFunc k)` whose residue at every other closed point of
`A¹_k` vanishes** (`Stacks.Chow.exists_isSingleResidueLift`).

`StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.ResidueSurjectivity` produces a class with residue
`α` at `φ` and no residue at the other points of degree at least `deg φ`. The residues left at
the points of smaller degree are removed one degree at a time, from the top down: at a degree
`n < deg φ` only finitely many points carry a residue
(`Stacks.Chow.exists_finset_forall_monicIrreducibleResidue_eq_zero`), and at each such point `χ`
the residue is cancelled by a class whose only residues are at `χ` and at points of degree below
`n`. That class has no residue at `φ`, which has larger degree, so the residue at `φ` is never
disturbed.

Everything is done in a fixed degree, because the norm maps built from it must preserve the
degree. This needs the generation principle for one Milnor K-group by the symbols **of that
length** (`Stacks.Chow.milnorKGrading_le_of_forall_length`), and the fact that the residues lower
the degree by one (`Stacks.Chow.monicIrreducibleResidue_mem_milnorKGrading`).

## Main definitions

* `Stacks.Chow.IsSingleResidueLift` — `y` has residue `α` at `φ` and no other residue.

## Main results

* `Stacks.Chow.milnorKGrading_le_of_forall_length` — the symbols of length `n` generate
  `K^M_n`.
* `Stacks.Chow.monicIrreducibleResidue_mem_milnorKGrading` — `∂_ψ (K^M_{i+1}) ⊆ K^M_i`.
* `Stacks.Chow.exists_monicIrreducibleResidue_eq_of_mem` — the diagonal surjectivity in a fixed
  degree.
* `Stacks.Chow.exists_isSingleResidueLift` — **the lift with a single residue.**
* `Stacks.Chow.exists_isSingleResidueLift_ring` — the same on the whole Milnor K-ring.

## References

* [Stacks Project, Tag 0EAY](https://stacks.math.columbia.edu/tag/0EAY)
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field
attribute [local instance] isDiscreteValuationRing_localizationAtPrime_polynomial

/-! ### Generation of one Milnor K-group by the symbols of its length -/

section Generation

variable {k : Type u} [Field k]

private theorem mk'_mem_of_mem_milnorKTensorGrading_length :
    ∀ (n : ℕ) {H : AddSubgroup (MilnorKRing k)},
      (∀ l : List kˣ, l.length = n → milnorKSymbolProd k l ∈ H) →
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
      exact zsmul_mem (by simpa using hH [] rfl) r
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
        intro l hl
        change milnorKSymbolProd k l * milnorKSymbol k (Additive.toMul m) ∈ H
        rw [← milnorKSymbolProd_singleton (Additive.toMul m), ← milnorKSymbolProd_append]
        exact hH _ (by rw [List.length_append, hl, List.length_singleton])
      · intro a b ha hb
        rw [map_add]
        exact add_mem ha hb

/-- **The symbols of length `n` generate `K^M_n(k)`.** An additive subgroup containing every
symbol `{u_1, …, u_n}` contains the whole degree-`n` Milnor K-group. -/
theorem milnorKGrading_le_of_forall_length {H : AddSubgroup (MilnorKRing k)} {n : ℕ}
    (hH : ∀ l : List kˣ, l.length = n → milnorKSymbolProd k l ∈ H) :
    milnorKGrading k n ≤ H := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [SetLike.mem_coe, Submodule.mem_toAddSubgroup] at ht
  exact mk'_mem_of_mem_milnorKTensorGrading_length n hH ht

/-- A ring homomorphism of fields preserves the degree on Milnor K-theory. -/
theorem milnorKRingMap_mem_milnorKGrading {k' : Type u} [Field k'] (f : k →+* k') {n : ℕ}
    {x : MilnorKRing k} (hx : x ∈ milnorKGrading k n) :
    milnorKRingMap f x ∈ milnorKGrading k' n := by
  have h := (milnorKTransport f n ⟨x, hx⟩).2
  rwa [milnorKTransport_coe] at h

end Generation

variable {k : Type u} [Field k]

/-! ### The residues lower the degree by one -/

/-- **`∂_ψ` maps `K^M_{i+1}(RatFunc k)` into `K^M_i(k[X] ⧸ ψ)`.** -/
theorem monicIrreducibleResidue_mem_milnorKGrading {d : ℕ} (ψ : MonicIrreducibleOfDegree k d)
    {i : ℕ} {y : MilnorKRing (RatFunc k)} (hy : y ∈ milnorKGrading (RatFunc k) (i + 1)) :
    monicIrreducibleResidue ψ y ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly ψ}) i := by
  rw [monicIrreducibleResidue_apply]
  exact milnorKRingMap_mem_milnorKGrading _
    (dvrMilnorShiftMap_shift_mem (irreducible_algebraMap_self (p := poly ψ)) i hy)

/-- **`∂_∞` maps `K^M_{i+1}(RatFunc k)` into `K^M_i(k)`.** -/
theorem infinityResidueRing_mem_milnorKGrading {i : ℕ} {y : MilnorKRing (RatFunc k)}
    (hy : y ∈ milnorKGrading (RatFunc k) (i + 1)) :
    infinityResidueRing k y ∈ milnorKGrading k i := by
  rw [← coe_infinityResidue i ⟨y, hy⟩]
  exact (infinityResidue i ⟨y, hy⟩).2

/-! ### The diagonal surjectivity in a fixed degree -/

/-- **Every class of `K^M_i(k[X] ⧸ φ)` is the residue at `φ` of a class of `K^M_{i+1}(RatFunc k)`
whose residue vanishes at every other closed point of degree at least `deg φ`.** -/
theorem exists_monicIrreducibleResidue_eq_of_mem {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1))
    {i : ℕ} {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) i) :
    ∃ y ∈ milnorKGrading (RatFunc k) (i + 1), monicIrreducibleResidue φ y = α ∧
      ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → e + 1 ≤ d' →
        monicIrreducibleResidue ψ y = 0 := by
  refine milnorKGrading_le_of_forall_length
    (H := { carrier := {β | ∃ y ∈ milnorKGrading (RatFunc k) (i + 1),
              monicIrreducibleResidue φ y = β ∧
              ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → e + 1 ≤ d' →
                monicIrreducibleResidue ψ y = 0}
            zero_mem' := ⟨0, zero_mem _, map_zero _, fun _ _ _ _ ↦ map_zero _⟩
            add_mem' := by
              rintro β γ ⟨y, hyi, hy, hy0⟩ ⟨z, hzi, hz, hz0⟩
              exact ⟨y + z, add_mem hyi hzi, by rw [map_add, hy, hz], fun d' ψ hne hle ↦ by
                rw [map_add, hy0 d' ψ hne hle, hz0 d' ψ hne hle, add_zero]⟩
            neg_mem' := by
              rintro β ⟨y, hyi, hy, hy0⟩
              exact ⟨-y, neg_mem hyi, by rw [map_neg, hy], fun d' ψ hne hle ↦ by
                rw [map_neg, hy0 d' ψ hne hle, neg_zero]⟩ }) ?_ hα
  intro m hm
  obtain ⟨l, hl1, hl2⟩ := exists_unitList_of_polyRep φ m
  refine ⟨unitSymbolProd (RatFunc k) l *
    milnorKSymbol (RatFunc k) (dvrFracUniformizer (RatFunc k)
      (irreducible_algebraMap_self (p := poly φ))), ?_, ?_, ?_⟩
  · refine SetLike.mul_mem_graded ?_ (milnorKSymbol_mem_milnorKGrading _)
    have hlen : l.length = i := by
      rw [← hm, ← List.length_map (f := fun w ↦ Units.map
        ((quotientRingEquivResidueField (Ideal.span {poly φ})).symm :
          (Ideal.span {poly φ}).ResidueField →* (Polynomial k ⧸ Ideal.span {poly φ}))
        (Units.map (residue (Localization.AtPrime (Ideal.span {poly φ}))).toMonoidHom w)), hl2]
    simpa only [unitSymbolProd, List.length_map, hlen] using
      milnorKSymbolProd_mem_milnorKGrading
        (l.map (Units.map (algebraMap (Localization.AtPrime (Ideal.span {poly φ}))
          (RatFunc k) : Localization.AtPrime (Ideal.span {poly φ}) →* RatFunc k)))
  · rw [monicIrreducibleResidue_unitSymbolProd_mul_uniformizer φ l, hl2]
  · obtain ⟨y, hy, hy0⟩ := exists_monicIrreducibleResidue_eq_milnorKSymbolProd φ m
    intro d' ψ hne hle
    refine monicIrreducibleResidue_eq_zero_of_mem_milnorKNotDvdFiltration ψ ?_
    rw [unitSymbolProd, hl1, dvrFracUniformizer_irreducible_algebraMap_self (ne_zero φ),
      ← milnorKSymbolProd_singleton (polyUnit (ne_zero φ)), ← milnorKSymbolProd_append]
    refine milnorKSymbolProd_mem_milnorKNotDvdFiltration fun v hv ↦ ?_
    rcases List.mem_append.mp hv with hv' | hv'
    · obtain ⟨u, -, rfl⟩ := List.mem_map.mp hv'
      refine ⟨polyRep (monic φ) (ne_one φ) u, polyRep_ne_zero (monic φ) (ne_one φ) u,
        fun hdvd ↦ ?_, rfl⟩
      have hle' := Polynomial.natDegree_le_of_dvd hdvd (polyRep_ne_zero (monic φ) (ne_one φ) u)
      have hlt := natDegree_polyRep_lt (monic φ) (ne_one φ) u
      have h1 := natDegree_eq ψ
      have h2 := natDegree_eq φ
      omega
    · rw [List.mem_singleton.mp hv']
      refine ⟨poly φ, ne_zero φ, fun hdvd ↦ hne ?_, rfl⟩
      exact Polynomial.eq_of_monic_of_associated (monic ψ) (monic φ)
        ((irreducible ψ).associated_of_dvd (irreducible φ) hdvd)

/-! ### Removing the residues of smaller degree -/

/-- **`y` is a lift of `α` with a single residue:** its residue at `φ` is `α` and its residue at
every other closed point of `A¹_k` vanishes. -/
def IsSingleResidueLift {d : ℕ} (φ : MonicIrreducibleOfDegree k d)
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) (y : MilnorKRing (RatFunc k)) : Prop :=
  monicIrreducibleResidue φ y = α ∧
    ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ →
      monicIrreducibleResidue ψ y = 0

/-- There is no monic irreducible polynomial of degree zero. -/
theorem MonicIrreducibleOfDegree.isEmpty_zero : IsEmpty (MonicIrreducibleOfDegree k 0) :=
  ⟨fun ψ ↦ by
    have h := natDegree_pos_of_monic_irreducible (monic ψ) (irreducible ψ)
    rw [natDegree_eq ψ] at h
    exact Nat.lt_irrefl 0 h⟩

/-- **One step of the descent:** a class of `K^M_{i+1}(RatFunc k)` whose residues away from `φ`
live in degree below `n + 1 ≤ deg φ` is corrected, without changing its residue at `φ`, into one
whose residues away from `φ` live in degree below `n`. -/
theorem exists_descent_step {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1)) {i n : ℕ}
    (hn : n < e + 1) {y : MilnorKRing (RatFunc k)} (hyi : y ∈ milnorKGrading (RatFunc k) (i + 1))
    (hy : ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → n + 1 ≤ d' →
      monicIrreducibleResidue ψ y = 0) :
    ∃ y' ∈ milnorKGrading (RatFunc k) (i + 1),
      monicIrreducibleResidue φ y' = monicIrreducibleResidue φ y ∧
      ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → n ≤ d' →
        monicIrreducibleResidue ψ y' = 0 := by
  classical
  rcases n with _ | n
  · -- there is nothing of degree zero
    refine ⟨y, hyi, rfl, fun d' ψ hne _ ↦ ?_⟩
    rcases d' with _ | d'
    · exact (MonicIrreducibleOfDegree.isEmpty_zero.false ψ).elim
    · exact hy _ ψ hne (by omega)
  obtain ⟨S, hS⟩ := exists_finset_forall_monicIrreducibleResidue_eq_zero y
  -- the points of degree `n + 1` carrying a residue
  let T : Finset (MonicIrreducibleOfDegree k (n + 1)) :=
    S.subtype (fun p : Polynomial k ↦ p.Monic ∧ Irreducible p ∧ p.natDegree = n + 1)
  have hT : ∀ χ : MonicIrreducibleOfDegree k (n + 1), χ ∉ T → monicIrreducibleResidue χ y = 0 :=
    fun χ hχ ↦ hS _ χ fun h ↦ hχ ((Finset.mem_subtype (p := fun p : Polynomial k ↦
      p.Monic ∧ Irreducible p ∧ p.natDegree = n + 1)).mpr h)
  -- the correcting classes
  have hz : ∀ χ : MonicIrreducibleOfDegree k (n + 1), ∃ z ∈ milnorKGrading (RatFunc k) (i + 1),
      monicIrreducibleResidue χ z = monicIrreducibleResidue χ y ∧
      ∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly χ → n + 1 ≤ d' →
        monicIrreducibleResidue ψ z = 0 := fun χ ↦
    exists_monicIrreducibleResidue_eq_of_mem χ (monicIrreducibleResidue_mem_milnorKGrading χ hyi)
  choose z hzi hzχ hz0 using hz
  have hφχ : ∀ χ : MonicIrreducibleOfDegree k (n + 1), poly φ ≠ poly χ := fun χ h ↦ by
    have h1 := natDegree_eq φ
    have h2 := natDegree_eq χ
    rw [h] at h1
    omega
  refine ⟨y - ∑ χ ∈ T, z χ, sub_mem hyi (sum_mem fun χ _ ↦ hzi χ), ?_, ?_⟩
  · rw [map_sub, map_sum, Finset.sum_eq_zero fun χ _ ↦ hz0 χ _ φ (hφχ χ) (by omega), sub_zero]
  · intro d' ψ hne hle
    rcases Nat.lt_or_ge (n + 1) d' with hlt | hge
    · rw [map_sub, map_sum, hy d' ψ hne hlt, Finset.sum_eq_zero fun χ _ ↦ hz0 χ d' ψ
        (fun h ↦ by have h1 := natDegree_eq ψ; have h2 := natDegree_eq χ; rw [h] at h1; omega)
        (by omega), sub_zero]
    · obtain rfl : d' = n + 1 := by omega
      rw [map_sub, map_sum]
      by_cases hψ : ψ ∈ T
      · rw [Finset.sum_eq_single_of_mem ψ hψ fun χ _ hχ ↦ hz0 χ _ ψ
          (fun h ↦ hχ (poly_injective h).symm) le_rfl, hzχ, sub_self]
      · rw [hT ψ hψ, Finset.sum_eq_zero fun χ hχ ↦ hz0 χ _ ψ
          (fun h ↦ hψ ((poly_injective h) ▸ hχ)) le_rfl, sub_zero]

/-- The descent, iterated: a class whose residues away from `φ` live in degree below `n ≤ deg φ`
is corrected, without changing its residue at `φ`, into a lift with a single residue. -/
theorem exists_isSingleResidueLift_of_le {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1))
    {i : ℕ} : ∀ n : ℕ, n ≤ e + 1 → ∀ y ∈ milnorKGrading (RatFunc k) (i + 1),
      (∀ (d' : ℕ) (ψ : MonicIrreducibleOfDegree k d'), poly ψ ≠ poly φ → n ≤ d' →
        monicIrreducibleResidue ψ y = 0) →
      ∃ y' ∈ milnorKGrading (RatFunc k) (i + 1),
        IsSingleResidueLift φ (monicIrreducibleResidue φ y) y' := by
  intro n
  induction n with
  | zero => exact fun _ y hyi hy ↦ ⟨y, hyi, rfl, fun d' ψ hne ↦ hy d' ψ hne (Nat.zero_le _)⟩
  | succ n ih =>
      intro hn y hyi hy
      obtain ⟨y', hy'i, hy'φ, hy'0⟩ := exists_descent_step φ (by omega) hyi hy
      obtain ⟨y'', hy''i, hy''⟩ := ih (by omega) y' hy'i hy'0
      exact ⟨y'', hy''i, hy'φ ▸ hy''⟩

/-- **Stacks 0EAY, the surjectivity half of Milnor's exact sequence: every class
`α ∈ K^M_i(k[X] ⧸ φ)` is the residue at `φ` of a class of `K^M_{i+1}(RatFunc k)` whose residue at
every other closed point of `A¹_k` vanishes.** -/
theorem exists_isSingleResidueLift {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1)) {i : ℕ}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})}
    (hα : α ∈ milnorKGrading (Polynomial k ⧸ Ideal.span {poly φ}) i) :
    ∃ y ∈ milnorKGrading (RatFunc k) (i + 1), IsSingleResidueLift φ α y := by
  obtain ⟨y, hyi, hyφ, hy0⟩ := exists_monicIrreducibleResidue_eq_of_mem φ hα
  obtain ⟨y', hy'i, hy'⟩ := exists_isSingleResidueLift_of_le φ (e + 1) le_rfl y hyi hy0
  exact ⟨y', hy'i, hyφ ▸ hy'⟩

/-- **The lift with a single residue, on the whole Milnor K-ring.** -/
theorem exists_isSingleResidueLift_ring {e : ℕ} (φ : MonicIrreducibleOfDegree k (e + 1))
    (α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})) :
    ∃ y : MilnorKRing (RatFunc k), IsSingleResidueLift φ α y :=
  mem_of_forall_milnorKSymbolProd_mem
    (H := { carrier := {β | ∃ y : MilnorKRing (RatFunc k), IsSingleResidueLift φ β y}
            zero_mem' := ⟨0, map_zero _, fun _ _ _ ↦ map_zero _⟩
            add_mem' := by
              rintro β γ ⟨y, hy, hy0⟩ ⟨z, hz, hz0⟩
              exact ⟨y + z, by rw [map_add, hy, hz], fun d' ψ hne ↦ by
                rw [map_add, hy0 d' ψ hne, hz0 d' ψ hne, add_zero]⟩
            neg_mem' := by
              rintro β ⟨y, hy, hy0⟩
              exact ⟨-y, by rw [map_neg, hy], fun d' ψ hne ↦ by
                rw [map_neg, hy0 d' ψ hne, neg_zero]⟩ })
    (fun m ↦ by
      obtain ⟨y, -, hy⟩ := exists_isSingleResidueLift φ (milnorKSymbolProd_mem_milnorKGrading m)
      exact ⟨y, hy⟩) α

/-- **Two lifts with a single residue differ by a class killed by every residue**, hence by a
class of `L_0`, which `∂_∞` kills. -/
theorem infinityResidueRing_eq_of_isSingleResidueLift {d : ℕ} {φ : MonicIrreducibleOfDegree k d}
    {α : MilnorKRing (Polynomial k ⧸ Ideal.span {poly φ})} {y y' : MilnorKRing (RatFunc k)}
    (hy : IsSingleResidueLift φ α y) (hy' : IsSingleResidueLift φ α y') :
    infinityResidueRing k y = infinityResidueRing k y' := by
  rw [← sub_eq_zero, ← map_sub]
  refine infinityResidueRing_eq_zero_of_mem_milnorKPolyFiltration_zero
    (mem_milnorKPolyFiltration_zero_of_forall_monicIrreducibleResidue_eq_zero fun e ψ ↦ ?_)
  by_cases h : poly ψ = poly φ
  · exact monicIrreducibleResidue_eq_zero_of_poly_eq h.symm
      (by rw [map_sub, hy.1, hy'.1, sub_self])
  · rw [map_sub, hy.2 _ ψ h, hy'.2 _ ψ h, sub_self]

end Stacks.Chow

end
