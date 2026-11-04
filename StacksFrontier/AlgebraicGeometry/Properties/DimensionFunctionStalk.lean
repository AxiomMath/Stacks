module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# The dimension of a local ring read off a dimension function

Let `X` be a locally Noetherian scheme with a dimension function `δ`
(`TopologicalSpace.DimensionFunction`, [Stacks, Tag 02I8]). For a point `x` of `X`, the Krull
dimension of `𝒪_{X,x}` is the largest value of `δ ξ - δ x` over the generalizations `ξ` of `x`,
and it is attained at the generic point of an irreducible component through `x`.

## Main results

* `AlgebraicGeometry.DimensionFunction.exists_ltSeries_of_specializes` — along a specialization
  `y ⤳ x` there is a chain of strict generalizations from `x` to `y` of length `δ y - δ x`.
* `AlgebraicGeometry.DimensionFunction.length_le_sub` — a chain of strict generalizations has
  length at most the increase of `δ` along it.
* `AlgebraicGeometry.DimensionFunction.exists_genericPoint_ringKrullDim_stalk_eq` — at every
  point `x` there is a generic point `ξ ⤳ x` of an irreducible component maximizing `δ` among
  the generalizations of `x`, and `dim 𝒪_{X,x} = δ ξ - δ x`.

## Implementation notes

The order on the points of a scheme is the specialization order of Mathlib, `a ≤ b ↔ b ⤳ a`, so
a strict chain upwards from `x` is a chain of strict generalizations, and its supremum length is
`Order.coheight x`, which is `dim 𝒪_{X,x}` by `AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`.

## References

* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public section

open TopologicalSpace

universe u

namespace AlgebraicGeometry.DimensionFunction

variable {X : Scheme.{u}} (δ : TopologicalSpace.DimensionFunction X)

/-- A dimension function is strictly monotone for the specialization order of a scheme. -/
theorem strictMono : StrictMono (δ : X → ℤ) := fun _ _ hab =>
  δ.strictAnti_specializes (Scheme.le_iff_specializes.mp hab.le) (ne_of_gt hab)

/-- A dimension function does not decrease along a specialization `y ⤳ x`: `δ x ≤ δ y`. -/
private theorem le_of_specializes {x y : X} (h : y ⤳ x) : δ x ≤ δ y := by
  by_cases hyx : y = x
  · rw [hyx]
  · exact (δ.strictAnti_specializes h hyx).le

/-- A chain of strict generalizations has length at most the increase of a dimension function
along it. -/
theorem length_le_sub (p : LTSeries X) : (p.length : ℤ) ≤ δ p.last - δ p.head := by
  have h : δ p.head + p.length ≤ δ p.last :=
    LTSeries.head_add_length_le_int (p.map δ (strictMono δ))
  omega

/-- Along a specialization `y ⤳ x` there is a chain of strict generalizations from `x` to `y`
whose length is `δ y - δ x`. -/
theorem exists_ltSeries_of_specializes {x y : X} (h : y ⤳ x) :
    ∃ p : LTSeries X, p.head = x ∧ p.last = y ∧ (p.length : ℤ) = δ y - δ x := by
  suffices H : ∀ (n : ℕ) (y : X), y ⤳ x → (δ y - δ x).toNat ≤ n →
      ∃ p : LTSeries X, p.head = x ∧ p.last = y ∧ (p.length : ℤ) = δ y - δ x from
    H _ y h le_rfl
  have base : ∃ p : LTSeries X, p.head = x ∧ p.last = x ∧ (p.length : ℤ) = δ x - δ x :=
    ⟨RelSeries.singleton _ x, rfl, rfl, by simp⟩
  intro n
  induction n with
  | zero =>
    intro y hy hle
    by_cases hyx : y = x
    · exact hyx ▸ base
    · have := δ.strictAnti_specializes hy hyx
      omega
  | succ k ih =>
    intro y hy hle
    by_cases hyx : y = x
    · exact hyx ▸ base
    · obtain ⟨z, hz, hzx⟩ := δ.exists_isImmediateSpecialization hy hyx
      have hstep := δ.step_immediate hz
      have := le_of_specializes δ hzx
      obtain ⟨p, hph, hpl, hpn⟩ := ih z hzx (by omega)
      have hlt : p.last < y := by
        rw [hpl]
        refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hz.1) fun hyz => hz.2.1 ?_
        exact (hz.1.antisymm (Scheme.le_iff_specializes.mp hyz)).eq
      refine ⟨p.snoc y hlt, by simp [hph], by simp, ?_⟩
      simp only [RelSeries.snoc_length, Nat.cast_add, Nat.cast_one, hpn]
      omega

/-- Every generalization of `x` is bounded by `δ x + dim 𝒪_{X,x}`. -/
theorem sub_le_coheight {x y : X} (h : y ⤳ x) :
    (((δ y - δ x).toNat : ℕ) : ℕ∞) ≤ Order.coheight x := by
  obtain ⟨p, hph, -, hpn⟩ := exists_ltSeries_of_specializes δ h
  have hn : (δ y - δ x).toNat = p.length := by omega
  exact hn ▸ Order.length_le_coheight (x := x) (p := p) hph.symm.le

/-- **The dimension of a local ring from a dimension function.** On a locally Noetherian scheme
with a dimension function `δ`, every point `x` has a generalization `ξ` which is the generic
point of an irreducible component, at which `δ` is largest among all generalizations of `x`, and
`dim 𝒪_{X,x} = δ ξ - δ x`. -/
theorem exists_genericPoint_ringKrullDim_stalk_eq [IsLocallyNoetherian X] (x : X) :
    ∃ ξ ∈ genericPoints X, ξ ⤳ x ∧ (∀ η : X, η ⤳ x → δ η ≤ δ ξ) ∧
      ∃ d : ℕ, ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) ∧ (d : ℤ) = δ ξ - δ x := by
  have hfin : ringKrullDim (X.presheaf.stalk x) < ⊤ := ringKrullDim_lt_top
  rw [ringKrullDim_stalk_eq_coheight] at hfin
  have hfin' : Order.coheight x ≠ ⊤ := fun h => by simp [h] at hfin
  set d : ℕ := (Order.coheight x).toNat with hd
  have hcd : Order.coheight x = (d : ℕ∞) := (ENat.natCast_toNat hfin').symm
  obtain ⟨p, hph, hpl⟩ := Order.exists_series_of_le_coheight x (n := d) hcd.ge
  have hmax : IsMax p.last := by
    intro z hz
    by_contra hne
    have := Order.length_le_coheight (x := x) (p := p.snoc z (lt_of_le_not_ge hz hne))
      (by simp [hph])
    rw [hcd, RelSeries.snoc_length, hpl] at this
    exact absurd (ENat.natCast_le_natCast.mp this) (by omega)
  have hξx : p.last ⤳ x := Scheme.le_iff_specializes.mp (hph ▸ p.head_le_last)
  have hlen := length_le_sub δ p
  rw [hph, hpl] at hlen
  have hle : ∀ η : X, η ⤳ x → δ η - δ x ≤ d := fun η hη => by
    have := ENat.natCast_le_natCast.mp (hcd ▸ sub_le_coheight δ hη)
    have := le_of_specializes δ hη
    omega
  exact ⟨p.last, (mem_genericPoints_iff_isMax X _).mpr hmax, hξx,
    fun η hη => by have := hle η hη; omega, d,
    by rw [ringKrullDim_stalk_eq_coheight, hcd]; rfl, by have := hle _ hξx; omega⟩

end AlgebraicGeometry.DimensionFunction

end
