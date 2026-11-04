module

public import StacksFrontier.AlgebraicGeometry.Surfaces.GenusOneCycle
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine extension system

A minimal numerical type of genus one with at least five components, one of which meets exactly
one other, is a Dynkin configuration on all but that component together with the component
itself, attached at a single vertex. This file turns that geometric picture into a closed linear
system in the Dynkin data alone, which is the input the remaining half of the classification
needs.

Write `t` for the number of remaining components, `d` for the shape of the Dynkin configuration
they carry, `w` for its scale, `r₀` for the vertex the deleted component `l` is attached to, and
`M` for the *weighted Cartan matrix* of `d`: twice the weight factor on the diagonal, minus the
larger of the two weight factors along an edge, zero elsewhere. The intersection matrix of the
configuration is `-w · M`, so the balance relation `∑ⱼ aᵢⱼmⱼ = 0` of the numerical type reads

* `(M m)_r = 0` for every vertex `r ≠ r₀`, and
* `w · (M m)_{r₀} = a_{x l} · m_l` at the attachment vertex,

while the balance relation at `l` itself reads `a_{l x} · m_x = 2 w_l m_l`. The pair `{l, x}` is
a proper pair of minus-two indices, so `a_{lx}² = k · w_l · w_x` with `k ∈ {1, 2, 3}`, and
eliminating `m_l`, `w_l`, `w` and `a_{lx}` between the three relations leaves the single
inhomogeneous equation

`2 · (M m)_{r₀} = k · (weight factor at r₀) · m_{r₀}`.

That is `AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf`: a system in the shape
`d`, the vertex `r₀`, the integer `k ∈ {1, 2, 3}` and the positive integer vector `m` only — no
numerical type, no weights, no scale. Solving it is a finite computation: `M = diag(wf) · C` for
the Cartan matrix `C` of `d`, so `m` is forced to be the `r₀`-th column of `C⁻¹` up to a scalar,
and the equation at `r₀` says exactly `(C⁻¹)_{r₀r₀} = 2 / k`, equivalently
`k · det(C ∖ r₀) = 2 · det C`.

## Main definitions

* `AlgebraicGeometry.DynkinShape.weightedCartan` — the weighted Cartan matrix of a shape.

## Main results

* `AlgebraicGeometry.NumericalType.intersection_eq_weightedCartan` — the intersection matrix of
  a Dynkin configuration is `-w` times the weighted Cartan matrix of its shape.
* `AlgebraicGeometry.NumericalType.affine_system_of_erase_leaf` — the affine extension system.

## Implementation notes

The system is stated with the multiplicities of the ambient numerical type substituted in, so it
is a statement about that numerical type rather than a free-standing predicate; what makes it
usable is that every other datum of the numerical type has been eliminated from it.

## References

* [Stacks Project, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T)
-/

@[expose] public section

open scoped BigOperators

namespace AlgebraicGeometry

/-- The weighted Cartan matrix of a Dynkin shape: twice the weight factor on the diagonal,
minus the larger of the two weight factors along an edge, and zero elsewhere. It is `-1/w`
times the intersection matrix of a Dynkin configuration of shape `d` and scale `w`. -/
@[sga "3 XXI 7.4.6"]
public noncomputable def DynkinShape.weightedCartan {t : ℕ} (d : DynkinShape)
    (r s : Fin t) : ℤ := by
  classical
  exact if r = s then 2 * d.weightFactor r
    else if d.Edge r s then -max (d.weightFactor r) (d.weightFactor s) else 0

namespace NumericalType

/-- The intersection matrix of a Dynkin configuration is `-w` times the weighted Cartan matrix
of its shape. -/
public lemma intersection_eq_weightedCartan {t : ℕ} (T : NumericalType)
    (v : Fin t → Fin T.componentCount) (d : DynkinShape) (w : ℤ)
    (hcfg : IsDynkinConfiguration T v d w) (r s : Fin t) :
    T.intersection (v r) (v s) = -(d.weightedCartan r s) * w := by
  classical
  rw [hcfg.2.2.2.1 r s]
  unfold DynkinShape.weightedCartan
  split_ifs <;> ring

/-- The balance relation at any component, split into the term at `l` and the sum over a
parametrisation `v` of the remaining components. -/
private lemma intersection_mul_multiplicity_split {t : ℕ} (T : NumericalType)
    (l : Fin T.componentCount) {v : Fin t → Fin T.componentCount} (hvinj : Function.Injective v)
    (hvl : ∀ r, v r ≠ l) (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y) (i : Fin T.componentCount) :
    T.intersection i l * T.multiplicity l +
      ∑ s, T.intersection i (v s) * T.multiplicity (v s) = 0 := by
  classical
  have himg : Finset.univ.image v = Finset.univ.erase l := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    exact ⟨by rintro ⟨r, rfl⟩; exact hvl r, hvsurj y⟩
  rw [← Finset.sum_image (f := fun j => T.intersection i j * T.multiplicity j)
    (fun a _ b _ h => hvinj h), himg, Finset.add_sum_erase _
      (fun j => T.intersection i j * T.multiplicity j) (Finset.mem_univ l)]
  exact T.intersection_mul_multiplicity i

/-- A component `l` meeting only `x = v r₀` meets no other vertex `v s` of the configuration. -/
private lemma intersection_eq_zero_of_ne_of_leaf {t : ℕ} (T : NumericalType)
    {l x : Fin T.componentCount} (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    {v : Fin t → Fin T.componentCount} (hvinj : Function.Injective v) (hvl : ∀ r, v r ≠ l)
    {r₀ : Fin t} (hr₀ : v r₀ = x) {s : Fin t} (hs : s ≠ r₀) : T.intersection l (v s) = 0 := by
  by_contra h
  exact hs (hvinj ((hleaf (v s) (hvl s) h).trans hr₀.symm))

/-- The balance relation at a vertex of a Dynkin configuration on all components but `l`, in
terms of the weighted Cartan matrix. -/
private lemma intersection_mul_multiplicity_eq_weightedCartan {t : ℕ} (T : NumericalType)
    (l : Fin T.componentCount) {v : Fin t → Fin T.componentCount} (hvinj : Function.Injective v)
    (hvl : ∀ r, v r ≠ l) (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y) {d : DynkinShape} {w : ℤ}
    (hcfg : IsDynkinConfiguration T v d w) (r : Fin t) :
    T.intersection (v r) l * T.multiplicity l =
      w * ∑ s, d.weightedCartan r s * T.multiplicity (v s) := by
  have h := intersection_mul_multiplicity_split T l hvinj hvl hvsurj (v r)
  have h2 : ∑ s, T.intersection (v r) (v s) * T.multiplicity (v s)
      = -(w * ∑ s, d.weightedCartan r s * T.multiplicity (v s)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [intersection_eq_weightedCartan T v d w hcfg r s]
    ring
  rw [h2] at h
  linarith

/-- A component `l` meeting no component other than `x` meets `x` positively. -/
private lemma intersection_pos_of_leaf (T : NumericalType) (hn : 2 < T.componentCount)
    {l x : Fin T.componentCount} (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x) : 0 < T.intersection l x := by
  refine (T.intersection_nonneg l x hlx).lt_of_ne fun h => ?_
  have h₁ : 1 ≤ (neighbors T l).card := one_le_neighborCount T (by omega) l
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (neighbors T l).card by omega)
  rw [mem_neighbors_iff] at hy
  rw [hleaf y (Ne.symm hy.1) hy.2] at hy
  exact hy.2 h.symm

/-- **The affine extension system.** Let `l` be a component of a numerical type all of whose
indices are minus-two indices, meeting exactly one other component `x`, and let the remaining
components carry the Dynkin configuration `v` of shape `d` and scale `w`, with `x = v r₀`. Then
for some `k ∈ {1, 2, 3}` the multiplicities are annihilated by the weighted Cartan matrix of `d`
away from `r₀` and satisfy the single inhomogeneous equation
`2 (M m)_{r₀} = k · wf(r₀) · m_{r₀}` at `r₀`. Every other datum of the numerical type — the
weights, the scale, the intersection numbers and the multiplicity of `l` — has been eliminated
from that system; the same `k` is the level of the pair `{l, x}`, which recovers the weight and
the multiplicity of `l` from those of `x` in the two ways the heavier of the two weights can be
distributed. -/
public theorem affine_system_of_erase_leaf {t : ℕ} (T : NumericalType)
    (hn : 2 < T.componentCount) (hminus : ∀ i, IsMinusTwoIndex T i)
    (l x : Fin T.componentCount) (hlx : l ≠ x)
    (hleaf : ∀ y, y ≠ l → T.intersection l y ≠ 0 → y = x)
    (v : Fin t → Fin T.componentCount) (hvinj : Function.Injective v)
    (hvl : ∀ r, v r ≠ l) (hvsurj : ∀ y, y ≠ l → ∃ r, v r = y)
    (d : DynkinShape) (w : ℤ) (hcfg : IsDynkinConfiguration T v d w)
    (r₀ : Fin t) (hr₀ : v r₀ = x) :
    ∃ k : ℤ, (k = 1 ∨ k = 2 ∨ k = 3) ∧
      (∀ r, r ≠ r₀ → ∑ s, d.weightedCartan r s * T.multiplicity (v s) = 0) ∧
      2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)
        = k * d.weightFactor r₀ * T.multiplicity (v r₀) ∧
      ((T.weight x = k * T.weight l ∧ 2 * T.multiplicity l = k * T.multiplicity x) ∨
        (T.weight l = k * T.weight x ∧ 2 * T.multiplicity l = T.multiplicity x)) := by
  have hwpos : 0 < w := hcfg.2.1
  have hwl : 0 < T.weight l := T.weight_pos l
  -- the components split into `l` and the vertices of the configuration
  -- the row of the balance relation at a vertex of the configuration
  have hrow := intersection_mul_multiplicity_eq_weightedCartan T l hvinj hvl hvsurj hcfg
  -- away from the attachment vertex the deleted component contributes nothing
  have hrest : ∀ r : Fin t, r ≠ r₀ →
      ∑ s, d.weightedCartan r s * T.multiplicity (v s) = 0 := by
    intro r hr
    have h := hrow r
    rw [T.intersection_symm, intersection_eq_zero_of_ne_of_leaf T hleaf hvinj hvl hr₀ hr,
      zero_mul] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hwpos.ne'
  -- the balance relation at the deleted component
  have hlrow : T.intersection l x * T.multiplicity x = 2 * T.weight l * T.multiplicity l := by
    have h := intersection_mul_multiplicity_split T l hvinj hvl hvsurj l
    have h2 : ∑ s, T.intersection l (v s) * T.multiplicity (v s)
        = T.intersection l x * T.multiplicity x := by
      rw [← hr₀]
      exact Finset.sum_eq_single r₀ (fun s _ hs => by
        rw [intersection_eq_zero_of_ne_of_leaf T hleaf hvinj hvl hr₀ hs, zero_mul])
        (fun hc => absurd (Finset.mem_univ r₀) hc)
    rw [h2, (hminus l).2] at h
    linarith
  -- the deleted component really does meet `x`
  obtain ⟨k, hk, hk2, hopt⟩ := weight_pair_level T hn l x (hminus l) (hminus x)
    (intersection_pos_of_leaf T hn hlx hleaf)
  refine ⟨k, hk, hrest, ?_, ?_⟩
  · have e1 : T.intersection l x * T.multiplicity l =
        w * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s) := by
      rw [T.intersection_symm l x, ← hr₀]
      exact hrow r₀
    have hwx : T.weight x = d.weightFactor r₀ * w := by
      rw [← hr₀]
      exact hcfg.2.2.1 r₀
    have hcancel : (T.weight l * w) * (2 * ∑ s, d.weightedCartan r₀ s * T.multiplicity (v s)) =
        (T.weight l * w) * (k * d.weightFactor r₀ * T.multiplicity x) := by
      linear_combination (-2 * T.weight l) * e1 + (-(T.intersection l x)) * hlrow +
        T.multiplicity x * hk2 + (k * T.weight l * T.multiplicity x) * hwx
    rw [hr₀]
    exact mul_left_cancel₀ (mul_ne_zero hwl.ne' hwpos.ne') hcancel
  · -- the balance relation at `l` turns the level into the multiplicity of `l`
    rcases hopt with ⟨hw, hi⟩ | ⟨hw, hi⟩
    · refine Or.inl ⟨hw, ?_⟩
      have h : T.weight l * (k * T.multiplicity x - 2 * T.multiplicity l) = 0 := by
        linear_combination hlrow - T.multiplicity x * hi
      have := (mul_eq_zero.mp h).resolve_left hwl.ne'
      linarith
    · refine Or.inr ⟨hw, ?_⟩
      have hkpos : 0 < k := by omega
      have h : (k * T.weight x) * (T.multiplicity x - 2 * T.multiplicity l) = 0 := by
        linear_combination hlrow - T.multiplicity x * hi + 2 * T.multiplicity l * hw
      have := (mul_eq_zero.mp h).resolve_left (mul_pos hkpos (T.weight_pos x)).ne'
      linarith

end NumericalType

end AlgebraicGeometry
