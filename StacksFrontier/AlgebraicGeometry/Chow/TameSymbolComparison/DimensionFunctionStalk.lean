module

public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbolGeneral.Arrows
public import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence

/-!
# A dimension function computes the dimensions of the local rings of closures of points

Let `X` be a scheme and `δ` a dimension function on `X` (strictly decreasing along proper
specializations, dropping by exactly one along immediate specializations). For a point `x` and a
point `y` in the closure of `x`, the local ring of `W = closure {x}` at `y` has dimension
`δ(x) - δ(y)` (`Stacks.Chow.ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub`).

Indeed that dimension is the coheight of `y` in `W` (Stacks 02IZ). By induction on `δ(x) - δ(y)`:
every proper generization of `y` in `W` has smaller `δ`-drop to `x`, which bounds the coheight
from above; and since the coheight is finite, a proper generization of `y` of maximal coheight is
an immediate one, where `δ` drops by exactly one, which bounds it from below.

## Main results

* `Stacks.Chow.coheight_pointClosure_eq_dimensionFunction_sub`.
* `Stacks.Chow.ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub`.

## References

* [Stacks Project, Tag 02I8](https://stacks.math.columbia.edu/tag/02I8)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable {X : Scheme.{u}} (δ : DimensionFunction X) (x : X)

/-- The generic point of `closure {x}`, read in `X`, is `x`. -/
theorem subschemeι_genericPoint_integralComponentAt :
    (integralComponentAt x).subschemeι (genericPoint (integralComponentAt x).subscheme) = x :=
  genericPointOf_integralComponentAt x

/-- Specialization in `closure {x}` is specialization in `X`. -/
theorem specializes_pointClosure_iff (a b : (integralComponentAt x).subscheme) :
    a ⤳ b ↔ (integralComponentAt x).subschemeι a ⤳ (integralComponentAt x).subschemeι b :=
  (integralComponentAt x).subschemeι.isClosedEmbedding.isInducing.specializes_iff.symm

/-- A cover in the specialization order of `closure {x}` is an immediate specialization in `X`. -/
theorem isImmediateSpecialization_of_covBy {a b : (integralComponentAt x).subscheme}
    (h : a ⋖ b) :
    IsImmediateSpecialization ((integralComponentAt x).subschemeι b)
      ((integralComponentAt x).subschemeι a) := by
  set ι := (integralComponentAt x).subschemeι
  refine ⟨(specializes_pointClosure_iff x b a).mp (Scheme.le_iff_specializes.mp h.1.le),
    fun he ↦ h.1.ne (ι.isClosedEmbedding.injective he).symm, fun c hbc hca ↦ ?_⟩
  have hcW : c ∈ Set.range ι.base := by
    have hb : ι b ∈ closure ({x} : Set X) := by
      rw [← coe_support_integralComponentAt, ← (integralComponentAt x).range_subschemeι]
      exact ⟨b, rfl⟩
    have hc : c ∈ closure ({x} : Set X) :=
      closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp
        ((specializes_iff_mem_closure.mpr hb).trans hbc)))
        isClosed_closure (subset_closure rfl)
    rw [← coe_support_integralComponentAt, ← (integralComponentAt x).range_subschemeι] at hc
    exact hc
  obtain ⟨c', rfl⟩ := hcW
  have h1 : a ≤ c' := Scheme.le_iff_specializes.mpr ((specializes_pointClosure_iff x c' a).mpr hca)
  have h2 : c' ≤ b := Scheme.le_iff_specializes.mpr ((specializes_pointClosure_iff x b c').mpr hbc)
  by_cases h1' : c' ≤ a
  · exact Or.inr (congrArg _ (scheme_eq_of_le_of_le h1' h1))
  by_cases h2' : b ≤ c'
  · exact Or.inl (congrArg _ (scheme_eq_of_le_of_le h2 h2'))
  exact absurd (lt_of_le_not_ge h2 h2') (h.2 (lt_of_le_not_ge h1 h1'))

/-- **The coheight of a point of `closure {x}` is the drop of the dimension function.** -/
theorem coheight_pointClosure_eq_dimensionFunction_sub (z : (integralComponentAt x).subscheme) :
    Order.coheight z = ((δ x - δ ((integralComponentAt x).subschemeι z)).toNat : ℕ∞) := by
  set ι := (integralComponentAt x).subschemeι
  have hle : ∀ w : (integralComponentAt x).subscheme, δ (ι w) ≤ δ x := fun w ↦ by
    have hsp : x ⤳ ι w := by
      have := (specializes_pointClosure_iff x _ w).mp
        ((genericPoint_spec (integralComponentAt x).subscheme).specializes trivial)
      rwa [subschemeι_genericPoint_integralComponentAt x] at this
    by_cases he : x = ι w
    · exact le_of_eq (congrArg δ.toFun he).symm
    · exact (δ.strictAnti_specializes hsp he).le
  have hlt : ∀ a b : (integralComponentAt x).subscheme, a < b → δ (ι a) < δ (ι b) := fun a b h ↦
    δ.strictAnti_specializes ((specializes_pointClosure_iff x b a).mp
      (Scheme.le_iff_specializes.mp h.le)) (fun he ↦ h.ne (ι.isClosedEmbedding.injective he).symm)
  suffices key : ∀ d : ℕ, ∀ z : (integralComponentAt x).subscheme, δ x - δ (ι z) = d →
      Order.coheight z = d by
    have := hle z
    exact key _ z (Int.toNat_of_nonneg (by omega)).symm
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro z hz
    have hup : Order.coheight z ≤ d := by
      refine Order.coheight_le_coe_iff.mpr fun y hy ↦ ?_
      have h1 := hlt z y hy
      have h2 := hle y
      have hd : ((δ x - δ (ι y)).toNat) < d := by omega
      rw [ih _ hd y (Int.toNat_of_nonneg (by omega)).symm]
      exact_mod_cast hd
    refine le_antisymm hup ?_
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [hd0]; exact bot_le
    -- a proper generization of `z` of maximal coheight is a cover of `z`
    have hne : ¬ IsMax z := by
      intro hmax
      have htop : z = genericPoint (integralComponentAt x).subscheme :=
        scheme_eq_of_le_of_le le_top (hmax le_top)
      rw [htop, subschemeι_genericPoint_integralComponentAt] at hz
      omega
    obtain ⟨y₀, hy₀⟩ := not_isMax_iff.mp hne
    have hfin : ∀ y, z < y → ∃ n : ℕ, Order.coheight y = n ∧ n < d := fun y hy ↦ by
      have h1 := hlt z y hy
      have h2 := hle y
      have hd : ((δ x - δ (ι y)).toNat) < d := by omega
      exact ⟨_, ih _ hd y (Int.toNat_of_nonneg (by omega)).symm, hd⟩
    classical
    have hex : ∃ n : ℕ, ∃ y, z < y ∧ Order.coheight y = (d - 1 - n : ℕ) := by
      obtain ⟨n, hn, hnd⟩ := hfin y₀ hy₀
      exact ⟨d - 1 - n, y₀, hy₀, by rw [hn]; exact_mod_cast (by omega : n = d - 1 - (d - 1 - n))⟩
    let n₀ := Nat.find hex
    obtain ⟨y, hy, hyc⟩ := Nat.find_spec hex
    have hcov : z ⋖ y := by
      refine ⟨hy, fun w hzw hwy ↦ ?_⟩
      obtain ⟨m, hm, hmd⟩ := hfin w hzw
      have hlt' := Order.coheight_add_one_le hwy
      rw [hm, hyc] at hlt'
      have hmle : d - 1 - n₀ + 1 ≤ m := by exact_mod_cast hlt'
      have hmin := Nat.find_min' hex ⟨w, hzw, by
        rw [hm]; exact_mod_cast (by omega : m = d - 1 - (d - 1 - m))⟩
      omega
    have hstep := δ.step_immediate (isImmediateSpecialization_of_covBy x hcov)
    have hdy : (δ x - δ (ι y)).toNat = d - 1 := by
      have hz' : δ.toFun x - δ.toFun (ι z) = (d : ℤ) := hz
      have hs' : δ.toFun (ι y) = δ.toFun (ι z) + 1 := hstep
      omega
    have hcy := ih _ (by omega) y (Int.toNat_of_nonneg (by have := hle y; omega)).symm
    have := Order.coheight_add_one_le hy
    rw [hcy, hdy] at this
    calc (d : ℕ∞) = ((d - 1 : ℕ) : ℕ∞) + 1 := by
          rw [← Nat.cast_add_one]; congr 1; omega
      _ ≤ _ := this

/-- **The local ring of `closure {x}` at a point `y` has dimension `δ(x) - δ(y)`.** -/
theorem ringKrullDim_pointClosureStalk_eq_dimensionFunction_sub {y : X}
    (h : y ∈ closure ({x} : Set X)) :
    ringKrullDim ((integralComponentAt x).subscheme.presheaf.stalk (pointClosurePoint x h)) =
      ((δ x - δ y).toNat : WithBot ℕ∞) := by
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight,
    coheight_pointClosure_eq_dimensionFunction_sub δ x, subschemeι_pointClosurePoint]
  rfl

end Stacks.Chow

end
