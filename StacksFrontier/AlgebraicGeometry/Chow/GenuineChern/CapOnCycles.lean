module

public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.ChernClassesOfRank
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.CapProduct
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Intersecting a cycle with the Chern classes of Stacks 02U0

Let `ℰ` be a finite locally free module of rank `r` on `X`, locally of finite type over the base
of chapter 42. [Stacks, Tag 02U5] defines `c_j(ℰ) ∩ - : Z_k(X) ⟶ A_{k-j}(X)` on an integral closed
subscheme `i : W ⟶ X` of delta-dimension `k` as `i_*(c_j(i^*ℰ) ∩ [W])`, with the classes of
[Stacks, Tag 02U0], and extends it coefficientwise. `Stacks.Chow.chernClassCap` is that extension
for an arbitrary cycle-valued datum `Stacks.Chow.ChernClassCycleRule`; this file supplies the
datum the source means: on an integral `T` and a module `F` of rank `r` on it, a cycle
representing `c_j(F) ∩ [T]`, the class `Stacks.Chow.chernClassFundamentalOfRank` read off the
projective space bundle formula.

## Main definitions

* `Stacks.Chow.GenuineChern.chernCycleRule` — the datum of Stacks 02U0, as a cycle rule.
* `Stacks.Chow.GenuineChern.chernCapOnCycles` — `c_j(ℰ) ∩ - : Z_k(X) ⟶ A_{k-j}(X)` of
  Stacks 02U5.

## Main results

* `Stacks.Chow.GenuineChern.mk_chernCycleRule` — the rule computes the classes of Stacks 02U0:
  its value is a representative, so the choice of representative is immaterial.
* `Stacks.Chow.GenuineChern.chernCapOnCycles_integral_cycle` — clause (1) of Stacks 02U5 on Chow
  groups: `c_j(ℰ) ∩ [W] = i_*(c_j(i^*ℰ) ∩ [W])`.
* `Stacks.Chow.GenuineChern.chernCapOnCycles_finsum` — clause (2), on a locally finite
  presentation, at the level of cycles.
* `Stacks.Chow.GenuineChern.chernCapOnCycles_sum` — clause (2) on Chow groups, on a finite
  presentation `α = ∑ n_t [W_t]`.
* `Stacks.Chow.GenuineChern.firstChernCapOnCycles` — `c₁(ℰ) ∩ -`, zero in rank zero.

## References

* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U0](https://stacks.math.columbia.edu/tag/02U0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow.GenuineChern

variable (C : ChowSituation.{u})

/-- A representative cycle of a Chow class. -/
def chowRep {T : Scheme.{u}} (pT : T ⟶ C.S) [LocallyOfFiniteType pT] {d : ℤ}
    (x : chowGroup C pT d) : CycleGroup C pT d :=
  Function.surjInv (QuotientAddGroup.mk'_surjective (rationalEquivalences C pT d)) x

/-- The class of the chosen representative cycle is the class itself. -/
@[simp]
theorem mk_chowRep {T : Scheme.{u}} (pT : T ⟶ C.S) [LocallyOfFiniteType pT] {d : ℤ}
    (x : chowGroup C pT d) :
    QuotientAddGroup.mk' (rationalEquivalences C pT d) (chowRep C pT x) = x :=
  Function.surjInv_eq _ x

/-- **The datum of Stacks 02U0 as a cycle rule.** On an integral `T` of delta-dimension `d` and a
module `F` of rank `r` on `T`, a cycle representing `c_j(F) ∩ [T]`, the class
`Stacks.Chow.chernClassFundamentalOfRank` of Stacks 02U0. -/
def chernCycleRule (r : ℕ) : ChernClassCycleRule C r :=
  fun pT _ _ F _ d _ j ↦ chowRep C pT (chernClassFundamentalOfRank F r C pT d j)

/-- **The rule computes the classes of Stacks 02U0**: the class of the cycle the rule assigns is
`c_j(F) ∩ [T]`, so the choice of representative is immaterial. -/
theorem mk_chernCycleRule (r : ℕ) {T : Scheme.{u}} (pT : T ⟶ C.S) [LocallyOfFiniteType pT]
    (hT : IsIntegral T) (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F r] (d : ℤ)
    (hd : schemeDeltaDimension C pT = (d : EInt)) (j : Fin (r + 1)) :
    QuotientAddGroup.mk' (rationalEquivalences C pT _) (chernCycleRule C r pT hT F d hd j) =
      chernClassFundamentalOfRank F r C pT d j :=
  mk_chowRep C pT _

/-- In rank `n + 1` the class of the cycle the rule assigns is
`Stacks.Chow.chernClassFundamental`. -/
theorem mk_chernCycleRule_succ (n : ℕ) {T : Scheme.{u}} (pT : T ⟶ C.S) [LocallyOfFiniteType pT]
    (hT : IsIntegral T) (F : T.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (n + 1)] (d : ℤ)
    (hd : schemeDeltaDimension C pT = (d : EInt)) (j : Fin (n + 1 + 1)) :
    QuotientAddGroup.mk' (rationalEquivalences C pT _)
        (chernCycleRule C (n + 1) pT hT F d hd j) =
      chernClassFundamental F n C pT d j := by
  rw [mk_chernCycleRule, chernClassFundamentalOfRank_succ]

variable {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r]

/-- **Stacks 02U5.** Intersection with the `j`-th Chern class of a finite locally free module of
rank `r`, `c_j(ℰ) ∩ - : Z_k(X) ⟶ A_{k-j}(X)`, for the Chern classes of Stacks 02U0: the
coefficientwise extension of `[W] ↦ i_*(c_j(i^*ℰ) ∩ [W])`. -/
@[stacks 02U5 "the operation"]
def chernCapOnCycles (k : ℤ) (j : Fin (r + 1)) :
    CycleGroup C sX k →+ chowGroup C sX (k - (j : ℤ)) :=
  chernClassCap C sX E r (fun g ↦ AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r) k j
    (chernCycleRule C r)

/-- **Stacks 02U5, clause (1)**, on Chow groups: for an integral closed subscheme
`i : W ⟶ X` of delta-dimension `k`, `c_j(ℰ) ∩ [W] = i_*(c_j(i^*ℰ) ∩ [W])`, with the class
`c_j(i^*ℰ) ∩ [W]` of Stacks 02U0. -/
@[stacks 02U5 "clause (1)"]
theorem chernCapOnCycles_integral_cycle (k : ℤ) (j : Fin (r + 1)) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ sX) = (k : EInt)) :
    chernCapOnCycles C sX E r k j (cycleAssociatedToClosedSubscheme C sX W.subschemeι k) =
      haveI := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E r
      properChowPushforward C (W.subschemeι ≫ sX) sX W.subschemeι rfl (k - (j : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (chernClassFundamentalOfRank ((Scheme.Modules.pullback W.subschemeι).obj E) r C
          (W.subschemeι ≫ sX) k j) := by
  unfold chernCapOnCycles
  rw [chernClassCap_integral_cycle C sX E r _ k j _ W hW hDim]
  have := AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback W.subschemeι E r
  rw [← mk_chernCycleRule C r (W.subschemeι ≫ sX) hW _ k hDim j, properChowPushforward_mk]
  rfl

/-- **Stacks 02U5, clause (2)**, at the level of cycles: on a locally finite presentation
`α = ∑ n_t [W_t]` by integral closed subschemes of delta-dimension `k`, `c_j(ℰ) ∩ α` is the class
of `∑ n_t i_{t,*}(c_j(i_t^*ℰ) ∩ [W_t])`, for representatives of the classes of Stacks 02U0. -/
@[stacks 02U5 "clause (2)"]
theorem chernCapOnCycles_finsum (k : ℤ) (j : Fin (r + 1)) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ t, IsIntegral (W t).subscheme)
    (hDim : ∀ t, schemeDeltaDimension C ((W t).subschemeι ≫ sX) = (k : EInt))
    (hLocal : LocallyFinite fun t ↦ ((W t).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ t : J, n t *
      (cycleAssociatedToClosedSubscheme C sX (W t).subschemeι k).1 x) :
    ∃ β : CycleGroup C sX (k - (j : ℤ)),
      chernCapOnCycles C sX E r k j α = QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ t : J, n t *
        (chernClassComponentCycle C sX E r
          (fun g ↦ AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r) k j
          (chernCycleRule C r) (W t) (hW t) (hDim t)).1 x :=
  chernClassCap_finsum C sX E r _ k j _ W hW hDim hLocal n α hα

/-- **Stacks 02U5, clause (2)**, on a finite presentation: if `α = ∑ n_t [W_t]` with each `W_t`
integral of delta-dimension `k`, then `c_j(ℰ) ∩ α = ∑ n_t (c_j(ℰ) ∩ [W_t])`. -/
theorem chernCapOnCycles_sum (k : ℤ) (j : Fin (r + 1)) {J : Type u} [Fintype J]
    (W : J → X.IdealSheafData) (hW : ∀ t, IsIntegral (W t).subscheme)
    (hDim : ∀ t, schemeDeltaDimension C ((W t).subschemeι ≫ sX) = (k : EInt)) (n : J → ℤ)
    (α : CycleGroup C sX k)
    (hα : ∀ x : X, α.1 x = ∑ᶠ t : J, n t *
      (cycleAssociatedToClosedSubscheme C sX (W t).subschemeι k).1 x) :
    chernCapOnCycles C sX E r k j α =
      ∑ t : J, n t • chernCapOnCycles C sX E r k j
        (cycleAssociatedToClosedSubscheme C sX (W t).subschemeι k) := by
  obtain ⟨β, hβ, hβx⟩ :=
    chernCapOnCycles_finsum C sX E r k j W hW hDim (locallyFinite_of_finite _) n α hα
  have hsum : β = ∑ t : J, n t • chernClassComponentCycle C sX E r
      (fun g ↦ AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback g E r) k j
      (chernCycleRule C r) (W t) (hW t) (hDim t) := by
    apply Subtype.ext
    ext x
    rw [hβx x, finsum_eq_sum_of_fintype]
    simp
  refine hβ.trans ?_
  rw [hsum, QuotientAddGroup.mk_sum]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [QuotientAddGroup.mk_zsmul]
  exact congrArg (n t • ·)
    (chernClassCap_integral_cycle C sX E r _ k j _ (W t) (hW t) (hDim t)).symm

/-- **Stacks 02U5 at `j = 1`.** Intersection with the first Chern class of a finite locally free
module of constant rank `r`, `c₁(ℰ) ∩ - : Z_d(X) ⟶ A_{d-1}(X)`: the operation
`Stacks.Chow.GenuineChern.chernCapOnCycles` at `j = 1` in positive rank, and zero in rank zero,
where the total Chern class is `1`. -/
def firstChernCapOnCycles {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) :
    (r : ℕ) → [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] →
      (d : ℤ) → CycleGroup C sX d →+ chowGroup C sX (d - 1)
  | 0, _, _ => 0
  | n + 1, _, d => (chowGroupCast C sX (by simp)).toAddMonoidHom.comp
      (chernCapOnCycles C sX E (n + 1) d ⟨1, by omega⟩)

/-- In rank zero `c₁(ℰ) ∩ -` is the zero map. -/
theorem firstChernCapOnCycles_zero {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E 0]
    (d : ℤ) : firstChernCapOnCycles C sX E 0 d = 0 :=
  rfl

/-- In positive rank `c₁(ℰ) ∩ -` is intersection with the Chern class at `j = 1`, read in degree
`d - 1`. -/
theorem firstChernCapOnCycles_succ {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] (d : ℤ)
    (α : CycleGroup C sX d) :
    firstChernCapOnCycles C sX E (n + 1) d α =
      chowGroupCast C sX (by simp) (chernCapOnCycles C sX E (n + 1) d ⟨1, by omega⟩ α) :=
  rfl

end Stacks.Chow.GenuineChern

end
