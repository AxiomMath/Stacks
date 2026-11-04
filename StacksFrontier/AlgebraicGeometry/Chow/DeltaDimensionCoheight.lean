module

public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureStalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolComparison.Arrows
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# The δ-dimension of a point and the dimension of its local ring

Let `(S, δ)` be as in Situation 02QL and let `X` be locally of finite type over `S`, with the
dimension function `δ_X = δ_{X/S}` of Stacks 02JW. For a point `x ∈ X` and an integer `e` such that
every generalization of `x` has `δ_X ≤ e`, and some generalization of `x` has `δ_X = e`,

  `δ_X(x) = e - dim 𝒪_{X,x}`.

Indeed `dim 𝒪_{X,x}` is the length of the longest chain of generalizations of `x` (Stacks 02IZ),
`δ_X` increases by at least one along each step, and along a specialization `η ⤳ x` the drop
`δ_X(η) - δ_X(x)` is the dimension of the local ring at `x` of `closure {η}` (Stacks 02JW), which
is at most `dim 𝒪_{X,x}`.

## Main results

* `Stacks.Chow.relativeDimension_head_add_length_le` — `δ_X` grows by at least the length along a
  chain of generalizations.
* `Stacks.Chow.exists_coheight_eq_and_relativeDimension_add_le` — `δ_X(x) + dim 𝒪_{X,x} ≤ e`.
* `Stacks.Chow.relativeDimension_sub_le_coheight` — `δ_X(η) - δ_X(x) ≤ dim 𝒪_{X,x}`.
* `Stacks.Chow.relativeDimension_eq_sub_ringKrullDim_stalk` — `δ_X(x) = e - dim 𝒪_{X,x}`.

## References

* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- Along a chain of generalizations `x_0 < x_1 < ⋯ < x_l` in the specialization order, `δ_X`
grows by at least `l`. -/
theorem relativeDimension_head_add_length_le (q : LTSeries X) :
    relativeDimension C.dimensionFunction p q.head + q.length ≤
      relativeDimension C.dimensionFunction p q.last := by
  have key : ∀ i : ℕ, ∀ hi : i ≤ q.length,
      relativeDimension C.dimensionFunction p (q 0) + i ≤
        relativeDimension C.dimensionFunction p (q ⟨i, Nat.lt_succ_of_le hi⟩) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have h1 := ih (Nat.le_of_succ_le hi)
      have hstep : q ⟨i, Nat.lt_succ_of_le (Nat.le_of_succ_le hi)⟩ <
          q ⟨i + 1, Nat.lt_succ_of_le hi⟩ := q.step ⟨i, hi⟩
      have hsp : q ⟨i + 1, Nat.lt_succ_of_le hi⟩ ⤳
          q ⟨i, Nat.lt_succ_of_le (Nat.le_of_succ_le hi)⟩ := hstep.1
      have hne : q ⟨i + 1, Nat.lt_succ_of_le hi⟩ ≠
          q ⟨i, Nat.lt_succ_of_le (Nat.le_of_succ_le hi)⟩ := fun h => hstep.2 (h ▸ hsp)
      have h2 := relativeDimension_lt_of_specializes C p hsp hne
      push_cast
      omega
  exact key q.length le_rfl

/-- **`δ_X(x) + dim 𝒪_{X,x} ≤ e`** when every generalization of `x` has `δ_X ≤ e`; in particular
the local ring has finite dimension. -/
theorem exists_coheight_eq_and_relativeDimension_add_le (x : X) (e : ℤ)
    (he : ∀ y : X, y ⤳ x → relativeDimension C.dimensionFunction p y ≤ e) :
    ∃ n : ℕ, coheight x = n ∧ relativeDimension C.dimensionFunction p x + n ≤ e := by
  have hle : coheight x ≤ ((e - relativeDimension C.dimensionFunction p x).toNat : ℕ∞) := by
    refine coheight_le fun q hq => ?_
    have h1 := relativeDimension_head_add_length_le C p q
    have h2 := he q.last (by
      have : q.head ≤ q.last := q.head_le_last
      rw [hq] at this
      exact this)
    rw [hq] at h1
    exact_mod_cast (by omega : q.length ≤ (e - relativeDimension C.dimensionFunction p x).toNat)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, coheight x = n :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top _) hle) |>.imp fun _ h => h.symm
  refine ⟨n, hn, ?_⟩
  rw [hn] at hle
  have := ENat.coe_le_coe.mp hle
  have hx := he x (specializes_refl x)
  omega

omit [LocallyOfFiniteType p] in
private theorem nontrivial_stalk (Y : Scheme.{u}) (y : Y) : Nontrivial (Y.presheaf.stalk y) :=
  inferInstance

/-- **`δ_X(η) - δ_X(x) ≤ dim 𝒪_{X,x}`** along a specialization `η ⤳ x`: the drop is the dimension
of the local ring at `x` of `closure {η}` (Stacks 02JW), a quotient of `𝒪_{X,x}`. -/
theorem relativeDimension_sub_le_coheight {η x : X} (h : η ⤳ x) {n : ℕ}
    (hn : coheight x = n) :
    relativeDimension C.dimensionFunction p η - relativeDimension C.dimensionFunction p x ≤ n := by
  have hsurj := (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({η} : Set X))).subschemeι.stalkMap_surjective
    ⟨x, specializes_iff_mem_closure.mp h⟩
  have hdim := ringKrullDim_le_of_surjective _ hsurj
  have hpt : (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({η} : Set X))).subschemeι
      ⟨x, specializes_iff_mem_closure.mp h⟩ = x := rfl
  rw [ringKrullDim_stalk_eq_coheight ((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({η} : Set X))).subschemeι
      ⟨x, specializes_iff_mem_closure.mp h⟩), hpt, hn] at hdim
  have := nontrivial_stalk (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({η} : Set X))).subscheme
    ⟨x, specializes_iff_mem_closure.mp h⟩
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := ((Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({η} : Set X))).subscheme.presheaf.stalk
    ⟨x, specializes_iff_mem_closure.mp h⟩))
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.coe_ne_bot h0)
  have hdn : d ≤ n := by rw [← hd] at hdim; exact_mod_cast hdim
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.coe_ne_top n) hdn)
  have hm : m ≤ n := by exact_mod_cast hdn
  have key := relativeDimension_sub_eq_of_ringKrullDim_pointClosureStalk_eq
    C.isUniversallyCatenary C.dimensionFunction p h (n := m) hd.symm
  omega

end Stacks.Chow

end
