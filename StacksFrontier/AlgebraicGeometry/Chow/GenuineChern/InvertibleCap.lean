module

public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FlatPullbackChern
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence

/-!
# The first Chern class of an invertible module, on Chow groups

`Stacks.Chow.firstChernClassCapChow C k p L : A_{k+1}(X) ⟶ A_k(X)` is intersection with the first
Chern class of an invertible module `L`, Stacks 02TI. This file proves, on Chow groups:

* it depends only on the isomorphism class of `L`;
* it is additive in `L` (Stacks 02SP);
* it commutes with flat pullback (Stacks 02SS);
* it commutes with pushforward along a closed immersion (Stacks 02SU for a closed immersion);
* capping a pulled-back class with the module of a relative effective Cartier divisor is
  pushing forward from the divisor (Stacks 02TR).

## References

* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u})

/-- The cap operator of an invertible module acts by `firstChernClassCapChow`. -/
theorem capOnChow_invertibleChernCapOperator {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (hfactors : ∀ k : ℤ, FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L)) (k : ℤ) (x : chowGroup C p (k + 1)) :
    (invertibleChernCapOperator C p L hfactors).capOnChow C p k x =
      firstChernClassCapChow C k p L x := rfl

/-- **The first Chern class cap depends only on the isomorphism class of the module.** -/
theorem firstChernClassCapChow_congr {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (k : ℤ) {L N : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (e : L ≅ N) (x : chowGroup C p (k + 1)) :
    firstChernClassCapChow C k p L x = firstChernClassCapChow C k p N x := by
  induction x using QuotientAddGroup.induction_on with
  | H α => exact firstChernClassCapOfInvertible_congr C p k L N e α

/-- **Stacks 02SP on Chow groups.** `c₁(L) ∩ x + c₁(N) ∩ x = c₁(L ⊗ N) ∩ x`. -/
theorem firstChernClassCapChow_tensorObj {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (k : ℤ) (L N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (x : chowGroup C p (k + 1)) :
    firstChernClassCapChow C k p L x + firstChernClassCapChow C k p N x =
      firstChernClassCapChow C k p (Scheme.Modules.tensorObj L N) x := by
  induction x using QuotientAddGroup.induction_on with
  | H α => exact firstChernClassCapOfInvertible_tensorObj C p k L N α

/-- The flat pullback of a class of a cycle is the class of the pullback cycle, up to a transport
of degrees. -/
private theorem flatPullbackChow_mk_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d) (k m : ℤ) (h : k + (d : ℤ) = m)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd k)
    (a : CycleGroup C sY k) :
    flatPullbackChow C sX sY f hf d hd k hfac (QuotientAddGroup.mk' _ a) ≍
      QuotientAddGroup.mk' (rationalEquivalences C sX m) (h ▸ flatPullback C sX sY f hf d hd k a) :=
  by
  rw [flatPullbackChow_mk, ← chowGroupCast_mk]
  exact (chowGroupCast_heq C sX _ _).symm

/-- **Stacks 02SS on Chow groups.** Flat pullback carries `c₁(L) ∩ -` to `c₁(f^*L) ∩ -`. -/
theorem flatPullbackChow_firstChernClassCapChow_heq {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sY = sX) (d : ℕ)
    (hd : AlgebraicGeometry.RelativeDimension f d)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX sY f hf d hd k)
    (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (L' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
    (eL : L' ≅ (Scheme.Modules.pullback f).obj L)
    (e : ℤ) (y : chowGroup C sY (e + 1)) (y' : chowGroup C sX (e + (d : ℤ) + 1))
    (hy : y' ≍ flatPullbackChow C sX sY f hf d hd (e + 1) (hfac (e + 1)) y) :
    flatPullbackChow C sX sY f hf d hd e (hfac e) (firstChernClassCapChow C e sY L y) ≍
      firstChernClassCapChow C (e + (d : ℤ)) sX L' y' := by
  subst hf
  rw [firstChernClassCapChow_congr C (f ≫ sY) (e + (d : ℤ)) eL]
  induction y using QuotientAddGroup.induction_on with
  | H α =>
    have h1 := flatPullbackChow_firstChernClassCapOfInvertible_of_invertible C sY f d hd e L
      (hfac e) α
    change flatPullbackChow C (f ≫ sY) sY f rfl d hd e (hfac e)
      (firstChernClassCapOfInvertible C sY e L α) ≍ _
    rw [h1]
    change firstChernClassCapChow C (e + (d : ℤ)) (f ≫ sY) ((Scheme.Modules.pullback f).obj L)
      (QuotientAddGroup.mk' _ _) ≍ _
    congr 1
    exact chowGroup_eq_of_heq C (f ≫ sY)
      ((flatPullbackChow_mk_heq C (f ≫ sY) sY f rfl d hd (e + 1) _ _ (hfac _) α).symm.trans
        hy.symm)

/-- **Stacks 02SU for a closed immersion, on Chow groups.** `ι_*(c₁(L') ∩ x) = c₁(L) ∩ ι_*x` for
`L' ≅ ι^*L`. -/
theorem properChowPushforward_firstChernClassCapChow_of_isClosedImmersion {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (ι : X ⟶ Y) [IsClosedImmersion ι] (hι : ι ≫ sY = sX) (L : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (L' : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
    (eL : L' ≅ (Scheme.Modules.pullback ι).obj L) (k : ℤ) (x : chowGroup C sX (k + 1)) :
    properChowPushforward C sX sY ι hι k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY ι hι k)
        (firstChernClassCapChow C k sX L' x) =
      firstChernClassCapChow C k sY L (properChowPushforward C sX sY ι hι (k + 1)
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY ι hι _) x) := by
  have := isInvertible_presheaf_modulePullback L ι
  rw [firstChernClassCapChow_congr C sX k eL]
  induction x using QuotientAddGroup.induction_on with
  | H α =>
    exact properChowPushforward_firstChernClassCapOfInvertible C sX sY ι hι k L α

/-- **Stacks 02TR on Chow groups.** For `p : X ⟶ Y` flat of relative dimension `r + 1` and
`D = Z(s)` a relative effective Cartier divisor cut out by a section `s` of an invertible `L`,
`c₁(L) ∩ p^*α = i_*((p|_D)^*α)` for every `α ∈ CH_{k+1}(Y)`. -/
theorem firstChernClassCapChow_flatPullbackChow_eq_divisor {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX) (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    [Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))
    (hq : AlgebraicGeometry.RelativeDimension
      ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) r)
    (α : chowGroup C sY (k + 1)) (y : chowGroup C sX (k + 1 + (r : ℤ) + 1))
    (hy : y ≍ flatPullbackChow C sX sY p hbase (r + 1) hp (k + 1)
      (flatPullbackFactorsThroughRationalEquivalence_general C sX sY p hbase (r + 1) hp _) α) :
    firstChernClassCapChow C (k + 1 + (r : ℤ)) sX L y =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (flatPullbackChow C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r hq (k + 1)
          (flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ _ r hq _) α) := by
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    have h := firstChernClassCapOfInvertible_flatPullback_divisor C sX sY p hbase r hp k L s hD hq
      (by push_cast; ring) a
    have hy' : y = QuotientAddGroup.mk' (rationalEquivalences C sX (k + 1 + (r : ℤ) + 1))
        ((show k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1 by push_cast; ring) ▸
          flatPullback C sX sY p hbase (r + 1) hp (k + 1) a) := by
      exact chowGroup_eq_of_heq C sX
        (hy.trans (flatPullbackChow_mk_heq C sX sY p hbase (r + 1) hp (k + 1) _ _ _ a))
    rwa [hy']

end Stacks.Chow

end
