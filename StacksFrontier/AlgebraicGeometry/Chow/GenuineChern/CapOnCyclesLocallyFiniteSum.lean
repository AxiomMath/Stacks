module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.CapOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# Clause (2) of Stacks 02U5 for arbitrary representatives

Let `ℰ` be a finite locally free module of rank `r` on `X`, locally of finite type over the base
of chapter 42, and let `α = ∑ n_t [W_t]` be a `k`-cycle, presented by a locally finite family of
integral closed subschemes `i_t : W_t ⟶ X` of delta-dimension `k`. Clause (2) of
[Stacks, Tag 02U5] sets

  `c_j(ℰ) ∩ α = ∑ n_t c_j(ℰ) ∩ [W_t]`,

where by clause (1) the term `c_j(ℰ) ∩ [W_t]` is `i_{t,*}(c_j(i_t^*ℰ) ∩ [W_t])`, with the class
`c_j(i_t^*ℰ) ∩ [W_t] ∈ A_{k-j}(W_t)` of [Stacks, Tag 02U0]. The sum is locally finite, so it is
read by choosing cycles `γ_t` on `W_t` representing these classes: the cycle
`∑ n_t i_{t,*} γ_t` is defined, and its class does not depend on the choice, because the
differences of two choices are rationally equivalent to zero on the members `W_t` of a locally
finite family, and such a locally finite sum is rationally equivalent to zero
([Stacks, Tag 02RZ]).

This file proves clause (2) in that form, for every choice of representatives.

## Main results

* `Stacks.Chow.GenuineChern.exists_cycle_finsum_properPushforward` — the locally finite sum
  `∑ n_t i_{t,*} γ_t` of cycles on the members of a locally finite family is a cycle.
* `Stacks.Chow.GenuineChern.mk_properPushforward_eq_chernCapOnCycles` — the pushforward of a
  representative of `c_j(i^*ℰ) ∩ [W]` represents `c_j(ℰ) ∩ [W]`.
* `Stacks.Chow.GenuineChern.chernCapOnCycles_locallyFiniteSum` — **Stacks 02U5, clause (2)**.

## References

* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- At a point `x`, only the finitely many members of a locally finite family of closed
subschemes containing `x` contribute to a sum of pushforwards of cycles living on them. -/
theorem finite_support_properPushforward_apply {J : Type u} (W : J → X.IdealSheafData)
    (hLocal : LocallyFinite fun t ↦ ((W t).support : Set X)) {d : ℤ}
    (c : ∀ t, CycleGroup C ((W t).subschemeι ≫ sX) d) (n : J → ℤ) (x : X) :
    (Function.support fun t ↦
      n t * (properPushforward C _ sX (W t).subschemeι rfl d (c t)).1 x).Finite := by
  refine (hLocal.point_finite x).subset fun t ht ↦ ?_
  have h := support_properPushforward_subset C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl d
    (c t) (right_ne_zero_of_mul ht)
  rwa [(W t).range_subschemeι] at h

/-- Proper pushforward along a closed subscheme is compatible with integer scalar
multiplication, pointwise. -/
private theorem properPushforward_zsmul_apply (W : X.IdealSheafData) (d : ℤ) (m : ℤ)
    (c : CycleGroup C (W.subschemeι ≫ sX) d) (x : X) :
    (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl d (m • c)).1 x =
      m * (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl d c).1 x := by
  have h := map_zsmul (properPushforwardHom C (W.subschemeι ≫ sX) sX W.subschemeι rfl d) m c
  simp only [properPushforwardHom_apply] at h
  rw [h]
  simp

/-- **The locally finite sum is a cycle.** For a locally finite family of closed subschemes
`i_t : W_t ⟶ X`, cycles `γ_t ∈ Z_d(W_t)` and integers `n_t`, the coefficientwise sum
`∑ n_t i_{t,*} γ_t` is a `d`-cycle on `X`. -/
theorem exists_cycle_finsum_properPushforward {J : Type u} (W : J → X.IdealSheafData)
    (hLocal : LocallyFinite fun t ↦ ((W t).support : Set X)) {d : ℤ}
    (γ : ∀ t, CycleGroup C ((W t).subschemeι ≫ sX) d) (n : J → ℤ) :
    ∃ β : CycleGroup C sX d, ∀ x : X, β.1 x = ∑ᶠ t : J, n t *
      (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl d (γ t)).1 x := by
  set P : J → CycleGroup C sX d := fun t ↦
    properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl d (n t • γ t) with hP
  have hPx (t : J) (x : X) : (P t).1 x = n t *
      (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl d (γ t)).1 x :=
    properPushforward_zsmul_apply C sX (W t) d (n t) (γ t) x
  have hloc : LocallyFiniteSupport fun x ↦ ∑ᶠ t : J, (P t).1 x :=
    locallyFiniteSupport_finsum (fun t ↦ ((W t).support : Set X)) hLocal
      (fun t x ↦ (P t).1 x) (fun t ↦ (P t).1.locallyFiniteSupport) fun t x hx ↦ by
        have h := support_properPushforward_subset C ((W t).subschemeι ≫ sX) sX
          (W t).subschemeι rfl d (n t • γ t) hx
        rwa [(W t).range_subschemeι] at h
  refine ⟨⟨{ toFun := fun x ↦ ∑ᶠ t : J, (P t).1 x,
              supportWithinDomain' := by simp,
              supportLocallyFiniteWithinDomain' := fun x _ ↦ hloc x }, ?_⟩,
    fun x ↦ finsum_congr fun t ↦ hPx t x⟩
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  obtain ⟨t, ht⟩ : ∃ t : J, (P t).1 x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  exact (mem_cyclesOfDimension_iff_forall_point C sX d _).1 (P t).2 x ht

variable (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **The terms of clause (2) of Stacks 02U5.** If a cycle `γ` on an integral closed subscheme
`i : W ⟶ X` of delta-dimension `k` represents `c_j(i^*ℰ) ∩ [W]`, the class of Stacks 02U0, then
`i_* γ` represents `c_j(ℰ) ∩ [W]`. -/
theorem mk_properPushforward_eq_chernCapOnCycles (k : ℤ) (j : Fin (r + 1))
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = (k : EInt))
    (γ : CycleGroup C (W.subschemeι ≫ sX) (k - (j : ℤ)))
    (hγ : haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E r
      QuotientAddGroup.mk' (rationalEquivalences C (W.subschemeι ≫ sX) (k - (j : ℤ))) γ =
        chernClassFundamentalOfRank ((Scheme.Modules.pullback W.subschemeι).obj E) r C
          (W.subschemeι ≫ sX) k j) :
    QuotientAddGroup.mk' (rationalEquivalences C sX (k - (j : ℤ)))
        (properPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl (k - (j : ℤ)) γ) =
      chernCapOnCycles C sX E r k j (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) := by
  rw [chernCapOnCycles_integral_cycle C sX E r k j W hW hDim, ← hγ, properChowPushforward_mk]

/-- **Stacks 02U5, clause (2).** Let `α = ∑ n_t [W_t]` be a `k`-cycle, presented by a locally
finite family of integral closed subschemes `i_t : W_t ⟶ X` of delta-dimension `k`, and let
`γ_t` be any cycle on `W_t` representing `c_j(i_t^*ℰ) ∩ [W_t]`, the class of Stacks 02U0. Then

1. `i_{t,*} γ_t` represents `c_j(ℰ) ∩ [W_t]` for every `t`;
2. the locally finite sum `∑ n_t i_{t,*} γ_t` is a cycle on `X`;
3. every cycle `β` with these coefficients represents `c_j(ℰ) ∩ α`;

that is, `c_j(ℰ) ∩ α = ∑ n_t c_j(ℰ) ∩ [W_t]`, independently of the representatives. -/
@[stacks 02U5 "clause (2)"]
theorem chernCapOnCycles_locallyFiniteSum (k : ℤ) (j : Fin (r + 1)) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ t, IsIntegral (W t).subscheme)
    (hDim : ∀ t, schemeDeltaDimension C ((W t).subschemeι ≫ sX) = (k : EInt))
    (hLocal : LocallyFinite fun t ↦ ((W t).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ t : J, n t *
      (cycleAssociatedToClosedSubscheme C sX (W t).subschemeι k).1 x)
    (γ : ∀ t, CycleGroup C ((W t).subschemeι ≫ sX) (k - (j : ℤ)))
    (hγ : ∀ t, haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (W t).subschemeι E r
      QuotientAddGroup.mk' (rationalEquivalences C ((W t).subschemeι ≫ sX) (k - (j : ℤ))) (γ t) =
        chernClassFundamentalOfRank ((Scheme.Modules.pullback (W t).subschemeι).obj E) r C
          ((W t).subschemeι ≫ sX) k j) :
    (∀ t, QuotientAddGroup.mk' (rationalEquivalences C sX (k - (j : ℤ)))
        (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl (k - (j : ℤ))
          (γ t)) =
      chernCapOnCycles C sX E r k j (cycleAssociatedToClosedSubscheme C sX (W t).subschemeι k)) ∧
    (∃ β : CycleGroup C sX (k - (j : ℤ)), ∀ x : X, β.1 x = ∑ᶠ t : J, n t *
      (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl (k - (j : ℤ))
        (γ t)).1 x) ∧
    ∀ β : CycleGroup C sX (k - (j : ℤ)), (∀ x : X, β.1 x = ∑ᶠ t : J, n t *
      (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl (k - (j : ℤ))
        (γ t)).1 x) →
      chernCapOnCycles C sX E r k j α = QuotientAddGroup.mk β := by
  refine ⟨fun t ↦ mk_properPushforward_eq_chernCapOnCycles C sX E r k j (W t) (hW t) (hDim t)
    (γ t) (hγ t), exists_cycle_finsum_properPushforward C sX W hLocal γ n, fun β hβ ↦ ?_⟩
  obtain ⟨β₀, hβ₀, hβ₀x⟩ := chernCapOnCycles_finsum C sX E r k j W hW hDim hLocal n α hα
  rw [hβ₀]
  -- The representatives the operation itself uses.
  set ρ : ∀ t, CycleGroup C ((W t).subschemeι ≫ sX) (k - (j : ℤ)) := fun t ↦
    chernClassComponentCycleOn C sX E r
      (fun g ↦ AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r) k j
      (chernCycleRule C r) (W t) (hW t) (hDim t)
  have hdiff (t : J) :
      γ t - ρ t ∈ rationalEquivalences C ((W t).subschemeι ≫ sX) (k - (j : ℤ)) := by
    have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (W t).subschemeι E r
    have h : QuotientAddGroup.mk' (rationalEquivalences C ((W t).subschemeι ≫ sX) (k - (j : ℤ)))
        (ρ t) = QuotientAddGroup.mk' _ (γ t) :=
      (mk_chernCycleRule C r ((W t).subschemeι ≫ sX) (hW t) _ k (hDim t) j).trans (hγ t).symm
    have h' := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at h'
  refine QuotientAddGroup.eq.2 ?_
  refine (mem_rationalEquivalences C sX _ _).2
    (rationallyEquivalentToZero_finsum_of_closedSupports C sX (k - (j : ℤ)) W hLocal
      (fun t ↦ n t • (γ t - ρ t))
      (fun t ↦ (rationalEquivalences C _ _).zsmul_mem (hdiff t) (n t)) fun x ↦ ?_)
  have hfγ := finite_support_properPushforward_apply C sX W hLocal γ n x
  have hfρ := finite_support_properPushforward_apply C sX W hLocal ρ n x
  have hsum := finsum_sub_distrib hfγ hfρ
  have hρx : ∀ x : X, β₀.1 x = ∑ᶠ t : J, n t *
      (properPushforward C ((W t).subschemeι ≫ sX) sX (W t).subschemeι rfl (k - (j : ℤ))
        (ρ t)).1 x := hβ₀x
  have hlhs : (-β₀ + β).1 x = β.1 x - β₀.1 x := by
    rw [neg_add_eq_sub]
    rfl
  rw [hlhs, hβ x, hρx x, ← hsum]
  refine finsum_congr fun t ↦ ?_
  rw [properPushforward_zsmul_apply, properPushforward_sub]
  simp [mul_sub]

end Stacks.Chow.GenuineChern

end
