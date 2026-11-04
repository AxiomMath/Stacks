module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernWhitney.GradedCapRing

/-!
# Intertwining graded cap families

Let `G, H : ℤ → Type*` be families of abelian groups, for instance the Chow groups of two schemes,
and let `Φ_k : G_k ⟶ H_{k-q}` be a family of homomorphisms lowering the degree by `q`, for
instance capping with a bivariant class of degree `q`. A graded cap family `a` on `G` and a
graded cap family `b` on `H` are *intertwined* by `Φ` when

  `Φ_{k-i} ∘ a_k^i = b_{k-q}^i ∘ Φ_k`

for all `k` and all indices `i`, the two sides being compared in `H_{k-i-q} = H_{k-q-i}`.

The pairs intertwined by `Φ` are closed under the ring operations of graded cap families and
under the formal inversion `Stacks.Chow.gradedRightInv`. This is what carries the identity
`c ∩ (x ∩ α) = x ∩ (c ∩ α)` of Stacks 02UA (2) from the Chern classes of finite locally free
modules to products and inverses of their total Chern classes, as in the proof of Stacks 0FAC.

## Main definitions

* `Stacks.Chow.GradedCapFamily.Intertwines` — the relation `Φ ∘ a = b ∘ Φ`.

## Main results

* `Stacks.Chow.GradedCapFamily.Intertwines.mul` — closure under products.
* `Stacks.Chow.GradedCapFamily.Intertwines.gradedRightInv` — closure under formal inversion.

## References

* [Stacks Project, Tag 0FAC](https://stacks.math.columbia.edu/tag/0FAC)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
-/

@[expose] public noncomputable section

open Finset

namespace Stacks.Chow

universe v w

variable {G : ℤ → Type v} [∀ k, AddCommGroup (G k)] {H : ℤ → Type w} [∀ k, AddCommGroup (H k)]

/-! ### Transports -/

/-- A graded cap family takes heterogeneously equal arguments in equal degrees to heterogeneously
equal values. -/
theorem GradedCapFamily.apply_heq (a : GradedCapFamily G) {k k' : ℤ} (hk : k = k') (i : ℕ)
    {x : G k} {x' : G k'} (hx : x ≍ x') : a k i x ≍ a k' i x' := by
  subst hk
  cases hx
  rfl

variable (q : ℤ) (Φ : ∀ k : ℤ, G k →+ H (k - q))

/-- A degree-lowering family takes heterogeneously equal arguments in equal degrees to
heterogeneously equal values. -/
theorem degreeFamily_heq {k k' : ℤ} (hk : k = k') {x : G k} {x' : G k'} (hx : x ≍ x') :
    Φ k x ≍ Φ k' x' := by
  subst hk
  cases hx
  rfl

/-! ### The relation -/

/-- **`Φ` intertwines `a` and `b`**: `Φ_{k-i}(a_k^i x) = b_{k-q}^i(Φ_k x)` for all `k`, `i` and
`x ∈ G_k`, the two sides compared along `k - q - i = k - i - q`. -/
def GradedCapFamily.Intertwines (a : GradedCapFamily G) (b : GradedCapFamily H) : Prop :=
  ∀ (k : ℤ) (i : ℕ) (x : G k),
    Φ (k - i) (a k i x) = gradedDegreeCast H (by ring) (b (k - q) i (Φ k x))

namespace GradedCapFamily.Intertwines

variable {q Φ}

/-- The relation, read as a heterogeneous equality. -/
theorem iff_heq {a : GradedCapFamily G} {b : GradedCapFamily H} :
    a.Intertwines q Φ b ↔ ∀ (k : ℤ) (i : ℕ) (x : G k), Φ (k - i) (a k i x) ≍ b (k - q) i (Φ k x) :=
  ⟨fun h k i x ↦ (heq_of_eq (h k i x)).trans (gradedDegreeCast_heq _ _),
    fun h k i x ↦ eq_of_heq ((h k i x).trans (gradedDegreeCast_heq _ _).symm)⟩

/-- If `Φ` intertwines `a` and `b`, then `Φ_{k-i}(a_k^i x) ≍ b_{k-q}^i(Φ_k x)` for all `k`, `i`
and `x ∈ G_k`. -/
theorem heq {a : GradedCapFamily G} {b : GradedCapFamily H} (h : a.Intertwines q Φ b) (k : ℤ)
    (i : ℕ) (x : G k) : Φ (k - i) (a k i x) ≍ b (k - q) i (Φ k x) :=
  iff_heq.1 h k i x

/-- `Φ` intertwines the units. -/
theorem one : (1 : GradedCapFamily G).Intertwines q Φ (1 : GradedCapFamily H) := by
  intro k i x
  rcases eq_or_ne i 0 with rfl | hi
  · refine eq_of_heq ?_
    rw [gradedCap_one_apply_zero, gradedCap_one_apply_zero]
    exact (degreeFamily_heq q Φ (by simp) (gradedDegreeCast_heq _ _)).trans
      ((gradedDegreeCast_heq _ _).trans (gradedDegreeCast_heq _ _)).symm
  · rw [gradedCap_one_of_ne hi, gradedCap_one_of_ne hi, AddMonoidHom.zero_apply,
      AddMonoidHom.zero_apply, map_zero, map_zero]

/-- `Φ` intertwines the zero families. -/
theorem zero : (0 : GradedCapFamily G).Intertwines q Φ (0 : GradedCapFamily H) := by
  intro k i x
  simp only [Pi.zero_apply, AddMonoidHom.zero_apply, map_zero]

/-- Intertwined pairs add. -/
theorem add {a a' : GradedCapFamily G} {b b' : GradedCapFamily H} (h : a.Intertwines q Φ b)
    (h' : a'.Intertwines q Φ b') : (a + a').Intertwines q Φ (b + b') := by
  intro k i x
  simp only [Pi.add_apply, AddMonoidHom.add_apply, map_add, h k i x, h' k i x]

/-- Intertwined pairs negate. -/
theorem neg {a : GradedCapFamily G} {b : GradedCapFamily H} (h : a.Intertwines q Φ b) :
    (-a).Intertwines q Φ (-b) := by
  intro k i x
  simp only [Pi.neg_apply, AddMonoidHom.neg_apply, map_neg, h k i x]

/-- Intertwined pairs subtract. -/
theorem sub {a a' : GradedCapFamily G} {b b' : GradedCapFamily H} (h : a.Intertwines q Φ b)
    (h' : a'.Intertwines q Φ b') : (a - a').Intertwines q Φ (b - b') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact h.add h'.neg

/-- Finite sums of intertwined pairs are intertwined. -/
theorem sum {ι : Type*} (s : Finset ι) {a : ι → GradedCapFamily G} {b : ι → GradedCapFamily H}
    (h : ∀ t ∈ s, (a t).Intertwines q Φ (b t)) :
    (∑ t ∈ s, a t).Intertwines q Φ (∑ t ∈ s, b t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : (0 : GradedCapFamily G).Intertwines q Φ 0)
  | insert t s ht ih =>
    rw [Finset.sum_insert ht, Finset.sum_insert ht]
    exact (h t (Finset.mem_insert_self t s)).add
      (ih fun t' ht' ↦ h t' (Finset.mem_insert_of_mem ht'))

/-- The convolution step: if `Φ y ≍ z`, then `Φ (a^{m-j} y) ≍ b^{m-j} z` up to degree transports. -/
private theorem intertwines_heq_step {a : GradedCapFamily G} {b : GradedCapFamily H}
    (h : a.Intertwines q Φ b) {k : ℤ} {j m : ℕ} (hjm : j ≤ m) {y : G (k - j)} {z : H (k - q - j)}
    (hyz : Φ (k - j) y ≍ z) :
    Φ (k - m) (gradedDegreeCast G (by omega) (a (k - j) (m - j) y)) ≍
      gradedDegreeCast H (show k - q - m = k - m - q by ring)
        (gradedDegreeCast H (show k - q - j - ((m - j : ℕ) : ℤ) = k - q - m by omega)
          (b (k - q - j) (m - j) z)) := by
  refine (degreeFamily_heq q Φ (by omega) (gradedDegreeCast_heq _ _)).trans ?_
  refine (h.heq (k - j) (m - j) y).trans ?_
  refine HEq.trans ?_ ((gradedDegreeCast_heq _ _).trans (gradedDegreeCast_heq _ _)).symm
  exact b.apply_heq (by ring) (m - j) hyz

/-- **Intertwined pairs multiply.** The summands of the two convolutions correspond one to one:
`Φ ∘ a^{m-j} ∘ a'^j = b^{m-j} ∘ Φ ∘ a'^j = b^{m-j} ∘ b'^j ∘ Φ`. -/
theorem mul {a a' : GradedCapFamily G} {b b' : GradedCapFamily H} (h : a.Intertwines q Φ b)
    (h' : a'.Intertwines q Φ b') : (a * a').Intertwines q Φ (b * b') := by
  intro k m x
  rw [gradedCap_mul_apply, gradedCap_mul_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [convolveTerm_of_le _ _ _ hjm, convolveTerm_of_le _ _ _ hjm, capTo_def, capTo_def]
  exact eq_of_heq (intertwines_heq_step h hjm (h'.heq k j x))

/-- Integer multiples of intertwined pairs are intertwined. -/
theorem zsmul {a : GradedCapFamily G} {b : GradedCapFamily H} (h : a.Intertwines q Φ b)
    (n : ℤ) : (n • a).Intertwines q Φ (n • b) := by
  intro k i x
  simp only [Pi.smul_apply, AddMonoidHom.smul_apply, map_zsmul, h k i x]

/-- **Intertwined pairs invert.** The formal inverses `Stacks.Chow.gradedRightInv` are defined by
the same recursion on the index on both sides. -/
theorem gradedRightInv {a : GradedCapFamily G} {b : GradedCapFamily H}
    (h : a.Intertwines q Φ b) :
    (Stacks.Chow.gradedRightInv a).Intertwines q Φ (Stacks.Chow.gradedRightInv b) := by
  intro k m
  induction m using Nat.strong_induction_on generalizing k with
  | _ m ih =>
    intro x
    rw [gradedRightInv_apply, gradedRightInv_apply, AddMonoidHom.sub_apply,
      AddMonoidHom.sub_apply, map_sub, map_sub, one k m x, AddMonoidHom.finsetSum_apply,
      AddMonoidHom.finsetSum_apply, map_sum, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    exact eq_of_heq (intertwines_heq_step h j.isLt.le
      ((heq_of_eq (ih j j.isLt k x)).trans (gradedDegreeCast_heq _ _)))

/-- Homogeneous components of intertwined pairs are intertwined. -/
theorem homComponent {a : GradedCapFamily G} {b : GradedCapFamily H} (h : a.Intertwines q Φ b)
    (i : ℕ) :
    (Stacks.Chow.homComponent i a).Intertwines q Φ (Stacks.Chow.homComponent i b) := by
  intro k j x
  rw [Stacks.Chow.homComponent_apply, Stacks.Chow.homComponent_apply]
  split_ifs
  · exact h k j x
  · simp

end GradedCapFamily.Intertwines

end Stacks.Chow

end
