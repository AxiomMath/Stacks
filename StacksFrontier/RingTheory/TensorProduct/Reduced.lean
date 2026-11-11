module

public import StacksCore.Tactic.StacksAttribute
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# A limit argument for tensor products of algebras

Let `k` be a field and let `R`, `S` be `k`-algebras. Any element of `R ⊗[k] S` is a finite sum of
pure tensors, hence lies in the image of `R' ⊗[k] S'` for suitable finitely generated subalgebras
`R' ⊆ R`, `S' ⊆ S`. Over a field every module is flat, so the induced map `R' ⊗[k] S' → R ⊗[k] S`
is injective, and pulling back along it transports each of the properties of being nonreduced, of
containing a nonzero zerodivisor and of containing a nontrivial idempotent from `R ⊗[k] S` down to
`R' ⊗[k] S'`.

Two reducedness statements are also proved: a subalgebra of a reduced commutative ring is reduced,
and `k ⊗[k] S` is reduced whenever the `k`-algebra `S` is reduced.

## Main results

* `not_isReduced_of_not_isReduced`: if `R ⊗[k] S` is not reduced, then neither is `R' ⊗[k] S'` for
  some finitely generated subalgebras `R' ⊆ R`, `S' ⊆ S`.
* `exists_zerodivisor_of_exists_zerodivisor`: if `R ⊗[k] S` contains a nonzero zerodivisor, then so
  does `R' ⊗[k] S'` for some finitely generated subalgebras `R' ⊆ R`, `S' ⊆ S`.
* `exists_idempotent_of_exists_idempotent`: if `R ⊗[k] S` contains a nontrivial idempotent, then so
  does `R' ⊗[k] S'` for some finitely generated subalgebras `R' ⊆ R`, `S' ⊆ S`.
* `isReduced_subalgebra`: a subalgebra of a reduced commutative ring is reduced.
* `isReduced_tensorProduct_baseField_left`: `k ⊗[k] S` is reduced for `S` a reduced `k`-algebra.
-/

@[expose] public section

open TensorProduct

variable {k R S : Type*} [Field k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- The algebra map `R' ⊗[k] S' → R ⊗[k] S` induced by the inclusions of two subalgebras of
`k`-algebras is injective. -/
theorem map_val_injective (R' : Subalgebra k R) (S' : Subalgebra k S) :
    Function.Injective ⇑(Algebra.TensorProduct.map R'.val S'.val) := by
  have hcoe : ∀ z : R' ⊗[k] S',
      Algebra.TensorProduct.map R'.val S'.val z
        = TensorProduct.map R'.val.toLinearMap S'.val.toLinearMap z := by
    intro z
    rw [← TensorProduct.AlgebraTensorModule.map_eq, ← Algebra.TensorProduct.toLinearMap_map]
    rfl
  have hRi : Function.Injective ⇑R'.val.toLinearMap := by
    simp only [AlgHom.coe_toLinearMap, Subalgebra.coe_val]; exact Subtype.val_injective
  have hSi : Function.Injective ⇑S'.val.toLinearMap := by
    simp only [AlgHom.coe_toLinearMap, Subalgebra.coe_val]; exact Subtype.val_injective
  intro a b hab
  refine TensorProduct.map_injective_of_flat_flat R'.val.toLinearMap S'.val.toLinearMap
    hRi hSi ?_
  rw [← hcoe, ← hcoe]; exact hab

/-- A pure tensor `a ⊗ₜ b` whose factors are generators of the adjoined subalgebras lies in the
range of the induced map. -/
theorem tmul_mem_range (FR : Finset R) (FS : Finset S) {a : R} {b : S}
    (ha : a ∈ FR) (hb : b ∈ FS) :
    a ⊗ₜ[k] b ∈
      (Algebra.TensorProduct.map (Algebra.adjoin k (FR : Set R)).val
        (Algebra.adjoin k (FS : Set S)).val).range := by
  refine ⟨⟨a, Algebra.subset_adjoin ha⟩ ⊗ₜ[k] ⟨b, Algebra.subset_adjoin hb⟩, ?_⟩
  simp [Algebra.TensorProduct.map_tmul]

/-- A finite sum of pure tensors whose factors are generators of the adjoined subalgebras lies in
the range of the induced map. -/
theorem sum_tmul_mem_range (FR : Finset R) (FS : Finset S) (G : Finset (R × S))
    (hG : ∀ p ∈ G, p.1 ∈ FR ∧ p.2 ∈ FS) :
    (∑ p ∈ G, p.1 ⊗ₜ[k] p.2) ∈
      (Algebra.TensorProduct.map (Algebra.adjoin k (FR : Set R)).val
        (Algebra.adjoin k (FS : Set S)).val).range :=
  Subalgebra.sum_mem _ fun p hp => tmul_mem_range FR FS (hG p hp).left (hG p hp).right

/-- A finite sum of pure tensors with factors from a finset `G'` comes from the tensor product of
the subalgebras generated by the factors of `G'`. -/
private theorem exists_map_val_eq_sum_tmul [DecidableEq R] [DecidableEq S] {G G' : Finset (R × S)}
    (hG : G ⊆ G') :
    ∃ z : Algebra.adjoin k ((G'.image Prod.fst : Finset R) : Set R) ⊗[k]
        Algebra.adjoin k ((G'.image Prod.snd : Finset S) : Set S),
      Algebra.TensorProduct.map (Algebra.adjoin k ((G'.image Prod.fst : Finset R) : Set R)).val
        (Algebra.adjoin k ((G'.image Prod.snd : Finset S) : Set S)).val z
        = ∑ p ∈ G, p.1 ⊗ₜ[k] p.2 :=
  sum_tmul_mem_range _ _ G fun _ hp =>
    ⟨Finset.mem_image_of_mem _ (hG hp), Finset.mem_image_of_mem _ (hG hp)⟩

/-- **Stacks 00I3** (part 1). If `R ⊗[k] S` is nonreduced, then there exist finitely generated
subalgebras `R' ⊆ R`, `S' ⊆ S` such that `R' ⊗[k] S'` is not reduced. -/
@[stacks 00I3 "nonreduced"]
theorem not_isReduced_of_not_isReduced (h : ¬ IsReduced (R ⊗[k] S)) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S), R'.FG ∧ S'.FG ∧
      ¬ IsReduced (R' ⊗[k] S') := by
  classical
  rw [isReduced_iff, not_forall] at h
  obtain ⟨z, hz⟩ := h
  rw [Classical.not_imp] at hz
  obtain ⟨⟨n, hzn⟩, hz0⟩ := hz
  obtain ⟨G, rfl⟩ := TensorProduct.exists_finset z
  set FR := G.image Prod.fst
  set FS := G.image Prod.snd
  obtain ⟨z', hz'⟩ := exists_map_val_eq_sum_tmul (k := k) (Finset.Subset.refl G)
  refine ⟨Algebra.adjoin k (FR : Set R), Algebra.adjoin k (FS : Set S),
    Subalgebra.fg_adjoin_finset FR, Subalgebra.fg_adjoin_finset FS, ?_⟩
  rw [isReduced_iff, not_forall]
  exact ⟨z', Classical.not_imp.mpr ⟨⟨n, map_val_injective _ _ (by rwa [map_pow, hz', map_zero])⟩,
    fun h0 => hz0 (by rw [← hz', h0, map_zero])⟩⟩

/-- **Stacks 00I3** (part 2). If `R ⊗[k] S` contains a nonzero zerodivisor, then there exist
finitely generated subalgebras `R' ⊆ R`, `S' ⊆ S` such that `R' ⊗[k] S'` contains a nonzero
zerodivisor. -/
@[stacks 00I3 "zerodivisor"]
theorem exists_zerodivisor_of_exists_zerodivisor
    (h : ∃ x : R ⊗[k] S, x ≠ 0 ∧ ∃ y : R ⊗[k] S, y ≠ 0 ∧ x * y = 0) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S), R'.FG ∧ S'.FG ∧
      ∃ x : R' ⊗[k] S', x ≠ 0 ∧ ∃ y : R' ⊗[k] S', y ≠ 0 ∧ x * y = 0 := by
  classical
  obtain ⟨x, hx0, y, hy0, hxy⟩ := h
  obtain ⟨Gx, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨Gy, rfl⟩ := TensorProduct.exists_finset y
  set G := Gx ∪ Gy
  set FR := G.image Prod.fst
  set FS := G.image Prod.snd
  obtain ⟨x', hx'⟩ := exists_map_val_eq_sum_tmul (k := k) (Finset.subset_union_left (s₂ := Gy))
  obtain ⟨y', hy'⟩ := exists_map_val_eq_sum_tmul (k := k) (Finset.subset_union_right (s₁ := Gx))
  exact ⟨Algebra.adjoin k (FR : Set R), Algebra.adjoin k (FS : Set S),
    Subalgebra.fg_adjoin_finset FR, Subalgebra.fg_adjoin_finset FS,
    x', fun h0 => hx0 (by rw [← hx', h0, map_zero]),
    y', fun h0 => hy0 (by rw [← hy', h0, map_zero]),
    map_val_injective _ _ (by rwa [map_mul, hx', hy', map_zero])⟩

/-- **Stacks 00I3** (part 3). If `R ⊗[k] S` contains a nontrivial idempotent, then there exist
finitely generated subalgebras `R' ⊆ R`, `S' ⊆ S` such that `R' ⊗[k] S'` contains a nontrivial
idempotent. -/
@[stacks 00I3 "idempotent"]
theorem exists_idempotent_of_exists_idempotent
    (h : ∃ e : R ⊗[k] S, e * e = e ∧ e ≠ 0 ∧ e ≠ 1) :
    ∃ (R' : Subalgebra k R) (S' : Subalgebra k S), R'.FG ∧ S'.FG ∧
      ∃ e : R' ⊗[k] S', e * e = e ∧ e ≠ 0 ∧ e ≠ 1 := by
  classical
  obtain ⟨e, hee, he0, he1⟩ := h
  obtain ⟨G, rfl⟩ := TensorProduct.exists_finset e
  set FR := G.image Prod.fst
  set FS := G.image Prod.snd
  obtain ⟨e', he'⟩ := exists_map_val_eq_sum_tmul (k := k) (Finset.Subset.refl G)
  exact ⟨Algebra.adjoin k (FR : Set R), Algebra.adjoin k (FS : Set S),
    Subalgebra.fg_adjoin_finset FR, Subalgebra.fg_adjoin_finset FS, e',
    map_val_injective _ _ (by rwa [map_mul, he']),
    fun h0 => he0 (by rw [← he', h0, map_zero]), fun h0 => he1 (by rw [← he', h0, map_one])⟩

open scoped TensorProduct

/-- The tensor product `k ⊗[k] S` of `k` with a reduced `k`-algebra `S` is reduced. For the
tensor product of two reduced algebras over a perfect field (Stacks 00I4) see
`PerfectField.isReduced_tensorProduct`. -/
theorem isReduced_tensorProduct_baseField_left (k : Type*) [Field k] (S : Type*)
    [CommRing S] [Algebra k S] [IsReduced S] : IsReduced (k ⊗[k] S) :=
  isReduced_of_injective
    (Algebra.TensorProduct.lid k S).toAlgHom.toRingHom
    (Algebra.TensorProduct.lid k S).injective

