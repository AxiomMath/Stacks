module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IteratedChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.PicardFirstChernShift
public import StacksFrontier.AlgebraicGeometry.Chow.VoevodskyNilpotence.Hinge

/-!
# Flat pullback and powers of a first Chern class shift operator

`Stacks.Chow.firstChernShift` turns `c₁(𝒩) ∩ -` into a degree-raising endomorphism of the graded
product of the Chow groups, and `Stacks.Chow.evalChowGraded α j` reads an operator off on the
class `α` in degree `j`, so that `evalChowGraded α j (c₁(𝒩)^j)` is `c₁(𝒩)^j ∩ α`. For
`f : X' ⟶ X` flat of relative dimension `r`, Stacks 02SS iterated gives

  `f^*(c₁(𝒩)^j ∩ α) = c₁(f^*𝒩)^j ∩ f^*α`.

The two sides lie in `A_{(e-j)+r}(X')` and `A_{(e+r)-j}(X')`, equal integers but different
terms, so the identity is stated as a heterogeneous equality.

## Main results

* `Stacks.Chow.evalChowGraded_zero_heq` — reading in degree zero returns the class itself.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension_evalChowGraded_firstChernShift_pow` — the
  identity above.
* `Stacks.Chow.isOfFinAddOrder_of_heq` — a class heterogeneously equal to a torsion class, in an
  equal degree, is torsion.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Stacks.AlgebraicGeometry.AmpleLimit

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-- Reading an operator of the form `a ^ 0` in degree zero returns the class it is evaluated
on. -/
theorem evalChowGraded_zero_heq {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (e : ℤ)
    (α : chowGroup C p e) (a : AddMonoid.End (ChowGradedProduct C p e)) :
    evalChowGraded C p e α 0 (a ^ 0) ≍ α := by
  change (a ^ 0) (chowGradedUnit C p e α) 0 ≍ α
  rw [pow_zero]
  change chowGroupDegreeCast C p _ (AddMonoidHom.id _) α ≍ α
  rw [chowGroupDegreeCast_apply]
  exact chowGroupCast_heq C p _ α

/-- A class heterogeneously equal to a torsion class, in an equal degree, is torsion. -/
theorem isOfFinAddOrder_of_heq {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    {d₁ d₂ : ℤ} (hd : d₁ = d₂) {x : chowGroup C p d₁} {y : chowGroup C p d₂} (hxy : x ≍ y)
    (hx : IsOfFinAddOrder x) : IsOfFinAddOrder y := by
  subst hd; cases hxy; exact hx

variable {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
  (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r)

/-- **Flat pullback commutes with powers of a first Chern class.** For `f` flat of relative
dimension `r`, an invertible `𝒩` on `X` and `α ∈ A_e(X)`,

  `f^*(c₁(𝒩)^j ∩ α) = c₁(f^*𝒩)^j ∩ f^*α`,

the left side in `A_{(e-j)+r}(X')` and the right side in `A_{(e+r)-j}(X')`. This is Stacks 02SS,
`Stacks.Chow.flatPullbackChowOfRelativeDimension_invCap_capOnChow`, applied `j` times. -/
theorem flatPullbackChowOfRelativeDimension_evalChowGraded_firstChernShift_pow (N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (hN : InvertibleChernCapDescends C sX N)
    (hN' : InvertibleChernCapDescends C sX' ((Scheme.Modules.pullback f).obj N))
    (e : ℤ) (α : chowGroup C sX e) (j : ℕ) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf (e - j)
        (evalChowGraded C sX e α j (firstChernShift C sX e N hN ^ j)) ≍
      evalChowGraded C sX' (e + r) (flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf e α)
        j (firstChernShift C sX' (e + r) ((Scheme.Modules.pullback f).obj N) hN' ^ j) := by
  induction j with
  | zero =>
    refine (flatPullbackChowOfRelativeDimension_heq C sX' sX f hbase r hf (by simp)
      (evalChowGraded_zero_heq C sX e α _)).trans ?_
    exact (evalChowGraded_zero_heq C sX' (e + r) _ _).symm
  | succ j ih =>
    rw [pow_succ', pow_succ', evalChowGraded_firstChernShift_mul,
      evalChowGraded_firstChernShift_mul]
    have hj : e - (j : ℤ) = e - ((j + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    have hj' : e + (r : ℤ) - (j : ℤ) = e + r - ((j + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    set E := evalChowGraded C sX e α j (firstChernShift C sX e N hN ^ j)
    set E' := evalChowGraded C sX' (e + r) (flatPullbackChowOfRelativeDimension C sX' sX f hbase
      r hf e α) j (firstChernShift C sX' (e + r) ((Scheme.Modules.pullback f).obj N) hN' ^ j)
    have hdeg : e - ((j + 1 : ℕ) : ℤ) + 1 + (r : ℤ) = e - ((j + 1 : ℕ) : ℤ) + r + 1 := by ring
    rw [firstChernCapStep_eq_invCap_capOnChow C sX e N hN j E (chowGroupCast C sX hj E)
        (chowGroupCast_heq C sX hj E).symm,
      firstChernCapStep_eq_invCap_capOnChow C sX' (e + r) _ hN' j E'
        (chowGroupCast C sX' hj' E') (chowGroupCast_heq C sX' hj' E').symm,
      flatPullbackChowOfRelativeDimension_invCap_capOnChow C sX' sX f hbase r hf N _ _
        (chowGroupCast C sX' hdeg (flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf _
          (chowGroupCast C sX hj E))) (chowGroupCast_heq C sX' hdeg _).symm]
    refine capOnChow_heq C sX' _ (by push_cast; ring) ?_
    refine (chowGroupCast_heq C sX' hdeg _).trans ?_
    refine (flatPullbackChowOfRelativeDimension_heq C sX' sX f hbase r hf hj.symm
      (chowGroupCast_heq C sX hj E)).trans ?_
    exact ih.trans (chowGroupCast_heq C sX' hj' E').symm

end Stacks.Chow

end
