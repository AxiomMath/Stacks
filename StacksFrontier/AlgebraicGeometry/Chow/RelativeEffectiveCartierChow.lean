module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.GysinFirstChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.InvertibleCap
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.DivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.RankZero
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeEffectiveCartierRelativeDimension

/-!
# Gysin pullback of a flat pullback along a relative effective Cartier divisor

Let `(S, δ)` be as in Situation 02QL, let `X`, `Y` be locally of finite type over `S`, let
`p : X ⟶ Y` be flat of relative dimension `r`, let `i : D ⟶ X` be a relative effective Cartier
divisor on `X/Y` (Stacks 062T) and let `ℒ = 𝒪_X(D)`. [Stacks, Tag 02TR] asserts that for every
`α ∈ CH_{k+1}(Y)`

  `i^* p^* α = (p|_D)^* α`  in  `CH_{k+r}(D)`  and  `c₁(ℒ) ∩ p^* α = i_*((p|_D)^* α)`  in
  `CH_{k+r}(X)`.

Here `i^*` is the Gysin map of Stacks 02TO (`Stacks.Chow.gysinChowOfInvertible`) for the
canonical section `1_D` of `𝒪_X(D)`, whose zero scheme is `D` (Stacks 01X0,
`Stacks.Divisors.zeroScheme_canonicalSection`), `p^*` and `(p|_D)^*` are flat pullback on Chow
groups (Stacks 02S1, `Stacks.Chow.flatPullbackChowOfRelativeDimension`), `c₁(ℒ) ∩ −` is the
operation of Stacks 02TI (`Stacks.Chow.firstChernClassCapChow`) and `i_*` is proper pushforward
(Stacks 0GU8). The relative dimension of `p|_D` is `r - 1`
(`Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor`).

## Main results

* `Stacks.Chow.gysinChowOfInvertible_canonicalSection_flatPullbackChow` — **Stacks 02TR, first
  equality**, for `p` of relative dimension `r + 1`.
* `Stacks.Chow.firstChernClassCapChow_divisorSheaf_flatPullbackChow` — **Stacks 02TR, second
  equality**, for `p` of relative dimension `r + 1`.
* `Stacks.Chow.gysinChowOfInvertible_canonicalSection_flatPullbackChow_of_relativeDimension_zero`
  and `Stacks.Chow.firstChernClassCapChow_divisorSheaf_flatPullbackChow_of_relativeDimension_zero`
  — **Stacks 02TR for `p` of relative dimension `0`**: then `D` is empty, so `CH_k(D) = 0` and
  both equalities say that `i^* p^* α` and `c₁(ℒ) ∩ p^* α` vanish.
* `Stacks.Chow.gysinChowOfInvertible_flatPullbackChow_eq_divisor` and
  `Stacks.Chow.firstChernClassCapChow_flatPullbackChow_eq_divisor'` — the two equalities for a
  divisor presented as the zero scheme of a section of an arbitrary invertible module.

## References

* [Stacks Project, Tag 02TR](https://stacks.math.columbia.edu/tag/02TR)
* [Stacks Project, Tag 062T](https://stacks.math.columbia.edu/tag/062T)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [LocallyOfFiniteType p] [Flat p] (hbase : p ≫ sY = sX)

/-! ### A divisor presented as the zero scheme of a section -/

section Presentation

variable (r : ℕ) (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (k : ℤ) (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : L.sections)
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))))

/-- `k + 1 + (r + 1) = (k + 1 + r) + 1` in `ℤ`, with `r + 1` cast from `ℕ`. -/
theorem degree_flatPullback_succ (k : ℤ) (r : ℕ) :
    k + 1 + ((r + 1 : ℕ) : ℤ) = k + 1 + (r : ℤ) + 1 := by
  push_cast
  ring

include hD in
/-- **Stacks 02TR, first equality, for a divisor `D = Z(s)` presented by a section.** For
`p : X ⟶ Y` flat of relative dimension `r + 1` and `D = Z(s)` a relative effective Cartier
divisor on `X/Y`, `i^* p^* α = (p|_D)^* α` in `A_{k+1+r}(D)` for every `α ∈ A_{k+1}(Y)`. -/
theorem gysinChowOfInvertible_flatPullbackChow_eq_divisor (α : chowGroup C sY (k + 1)) :
    haveI : Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) := hD.2
    gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) L (s.eval (.op ⊤))
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      flatPullbackChowOfRelativeDimension C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r
        (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
          p r hp _ hD) (k + 1) α := by
  have : Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) := hD.2
  induction α using QuotientAddGroup.induction_on with
  | H a =>
    rw [show ((a : CycleGroup C sY (k + 1)) : chowGroup C sY (k + 1)) =
        QuotientAddGroup.mk' (rationalEquivalences C sY (k + 1)) a from rfl,
      flatPullbackChowOfRelativeDimension_mk, flatPullbackChowOfRelativeDimension_mk,
      chowGroupCast_mk]
    exact gysinHomomorphismOfInvertible_flatPullback_divisor C sX sY p hbase r hp k L s hD
      (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
        p r hp _ hD) (degree_flatPullback_succ k r) a

include hD in
/-- **Stacks 02TR, second equality, for a divisor `D = Z(s)` presented by a section.** In the
situation of `Stacks.Chow.gysinChowOfInvertible_flatPullbackChow_eq_divisor`,
`c₁(L) ∩ p^* α = i_*((p|_D)^* α)` in `A_{k+1+r}(X)`. -/
theorem firstChernClassCapChow_flatPullbackChow_eq_divisor' (α : chowGroup C sY (k + 1)) :
    haveI : Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) := hD.2
    firstChernClassCapChow C (k + 1 + (r : ℤ)) sX L
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      properChowPushforward C
        ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sX
        (Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (flatPullbackChowOfRelativeDimension C
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ sX) sY
          ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r
          (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
            p r hp _ hD) (k + 1) α) := by
  have : Flat ((Stacks.Divisors.zeroScheme X L (s.eval (.op ⊤))).subschemeι ≫ p) := hD.2
  exact firstChernClassCapChow_flatPullbackChow_eq_divisor C sX sY p hbase r hp k L s hD
    (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
      p r hp _ hD) α _ (chowGroupCast_heq C sX _ _)

end Presentation

/-! ### Stacks 02TR -/

section Divisor

variable (D : X.IdealSheafData) (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p D)
    (k : ℤ)

/-- **Stacks 01X0**: the zero scheme `Stacks.Divisors.zeroScheme` of the canonical section of
`𝒪_X(D)` is `D`. -/
theorem zeroScheme_divisorSheafGlobalSection [Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) = D :=
  Stacks.Divisors.zeroScheme_canonicalSection D

omit [LocallyOfFiniteType p] [Flat p] in
/-- The zero scheme of the canonical section of `𝒪_X(D)` is a relative effective Cartier divisor
when `D` is: it is `D`, by Stacks 01X0. -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme_divisorSheaf
    [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (hD : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p D) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)) := by
  rwa [zeroScheme_divisorSheafGlobalSection D]

/-- The first equality of Stacks 02TR, for any closed subscheme `E` equal to the zero scheme of
the canonical section; the case `E = D` is
`Stacks.Chow.gysinChowOfInvertible_canonicalSection_flatPullbackChow`. -/
private theorem gysinChowOfInvertible_canonicalSection_flatPullbackChow_aux
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (E : X.IdealSheafData)
    (hE : Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) = E)
    (hErel : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p E)
    (α : chowGroup C sY (k + 1)) :
    haveI : Flat (E.subschemeι ≫ p) := hErel.2
    hE ▸ gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      flatPullbackChowOfRelativeDimension C (E.subschemeι ≫ sX) sY (E.subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r
        (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
          p r hp E hErel) (k + 1) α := by
  subst hE
  exact gysinChowOfInvertible_flatPullbackChow_eq_divisor C sX sY p hbase r hp k
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.canonicalSection' D) hErel α

/-- **Stacks 02TR, first equality.** Let `p : X ⟶ Y` be flat of relative dimension `r + 1`
between schemes locally of finite type over the base, let `i : D ⟶ X` be a relative effective
Cartier divisor on `X/Y` and let `i^*` be the Gysin map of the canonical section of `𝒪_X(D)`,
whose zero scheme is `D` (Stacks 01X0). Then `p|_D` is flat of relative dimension `r` and

  `i^* p^* α = (p|_D)^* α`  in  `CH_{k+1+r}(D)`  for every  `α ∈ CH_{k+1}(Y)`. -/
@[stacks 02TR "first equality i^* p^* α = (p|_D)^* α, for p of relative dimension r + 1 \
(relative dimension 0 is `gysinChowOfInvertible_canonicalSection_flatPullbackChow_of_\
relativeDimension_zero`)"]
theorem gysinChowOfInvertible_canonicalSection_flatPullbackChow (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (α : chowGroup C sY (k + 1)) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
    haveI : Flat (D.subschemeι ≫ p) := hD.2
    zeroScheme_divisorSheafGlobalSection D ▸
      gysinChowOfInvertible C sX (k + 1 + (r : ℤ)) (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      flatPullbackChowOfRelativeDimension C (D.subschemeι ≫ sX) sY (D.subschemeι ≫ p)
        (by rw [Category.assoc, hbase]) r
        (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
          p r hp D hD) (k + 1) α := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
  exact gysinChowOfInvertible_canonicalSection_flatPullbackChow_aux C sX sY p hbase D k r hp D
    (zeroScheme_divisorSheafGlobalSection D) hD α

/-- The second equality of Stacks 02TR, for any closed subscheme `E` equal to the zero scheme of
the canonical section; the case `E = D` is
`Stacks.Chow.firstChernClassCapChow_divisorSheaf_flatPullbackChow`. -/
private theorem firstChernClassCapChow_divisorSheaf_flatPullbackChow_aux
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (E : X.IdealSheafData)
    (hE : Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) = E)
    (hErel : Stacks.Divisors.IsRelativeEffectiveCartierDivisor p E)
    (α : chowGroup C sY (k + 1)) :
    haveI : Flat (E.subschemeι ≫ p) := hErel.2
    firstChernClassCapChow C (k + 1 + (r : ℤ)) sX (Stacks.Divisors.divisorSheaf D)
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      properChowPushforward C (E.subschemeι ≫ sX) sX E.subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (flatPullbackChowOfRelativeDimension C (E.subschemeι ≫ sX) sY (E.subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r
          (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
            p r hp E hErel) (k + 1) α) := by
  subst hE
  exact firstChernClassCapChow_flatPullbackChow_eq_divisor' C sX sY p hbase r hp k
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.canonicalSection' D) hErel α

/-- **Stacks 02TR, second equality.** In the situation of
`Stacks.Chow.gysinChowOfInvertible_canonicalSection_flatPullbackChow`, with `ℒ = 𝒪_X(D)`,

  `c₁(ℒ) ∩ p^* α = i_*((p|_D)^* α)`  in  `CH_{k+1+r}(X)`  for every  `α ∈ CH_{k+1}(Y)`. -/
@[stacks 02TR "second equality c_1(O_X(D)) ∩ p^* α = i_*((p|_D)^* α), for p of relative \
dimension r + 1 (relative dimension 0 is `firstChernClassCapChow_divisorSheaf_flatPullbackChow_\
of_relativeDimension_zero`)"]
theorem firstChernClassCapChow_divisorSheaf_flatPullbackChow (r : ℕ)
    (hp : AlgebraicGeometry.RelativeDimension p (r + 1)) (α : chowGroup C sY (k + 1)) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
    haveI : Flat (D.subschemeι ≫ p) := hD.2
    firstChernClassCapChow C (k + 1 + (r : ℤ)) sX (Stacks.Divisors.divisorSheaf D)
        (chowGroupCast C sX (degree_flatPullback_succ k r)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase (r + 1) hp (k + 1) α)) =
      properChowPushforward C (D.subschemeι ≫ sX) sX D.subschemeι rfl (k + 1 + (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)
        (flatPullbackChowOfRelativeDimension C (D.subschemeι ≫ sX) sY (D.subschemeι ≫ p)
          (by rw [Category.assoc, hbase]) r
          (Stacks.Divisors.relativeDimension_subschemeι_comp_of_isRelativeEffectiveCartierDivisor
            p r hp D hD) (k + 1) α) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
  exact firstChernClassCapChow_divisorSheaf_flatPullbackChow_aux C sX sY p hbase D k r hp D
    (zeroScheme_divisorSheafGlobalSection D) hD α

/-- If `p` has relative dimension `0`, every Chow group of a relative effective Cartier divisor
`E` on `X/Y` is trivial, since `E` is empty. -/
private theorem subsingleton_chowGroup_subschemeι_of_relativeDimension_zero
    {Z : Scheme.{u}} (q : X ⟶ Z) [LocallyOfFiniteType q]
    (hq : AlgebraicGeometry.RelativeDimension q 0)
    (E : X.IdealSheafData) (hE : Stacks.Divisors.IsRelativeEffectiveCartierDivisor q E) :
    Subsingleton (chowGroup C (E.subschemeι ≫ sX) k) := by
  have : IsEmpty E.subscheme :=
    Stacks.Divisors.isEmpty_subscheme_of_isRelativeEffectiveCartierDivisor_of_relativeDimension_zero
      q hq E hE
  exact subsingleton_chowGroup_of_isEmpty C _ k

/-- **Stacks 02TR in relative dimension zero, first equality.** If `p` has relative dimension `0`
then a relative effective Cartier divisor `D` on `X/Y` is empty, so `CH_k(D) = 0` and
`i^* p^* α = 0` for every `α ∈ CH_{k+1}(Y)`. -/
@[stacks 02TR "first equality, for p of relative dimension 0: D is empty, so CH_k(D) = 0 and \
i^* p^* α = 0"]
theorem gysinChowOfInvertible_canonicalSection_flatPullbackChow_of_relativeDimension_zero
    (hp : AlgebraicGeometry.RelativeDimension p 0) (α : chowGroup C sY (k + 1)) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
    (zeroScheme_divisorSheafGlobalSection D ▸
      gysinChowOfInvertible C sX k (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)
        (chowGroupCast C sX (show k + 1 + ((0 : ℕ) : ℤ) = k + 1 by simp)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase 0 hp (k + 1) α)) :
        chowGroup C (D.subschemeι ≫ sX) k) = 0 := by
  have := subsingleton_chowGroup_subschemeι_of_relativeDimension_zero C sX k p hp D hD
  exact Subsingleton.elim _ _

/-- **Stacks 02TR in relative dimension zero, second equality.** If `p` has relative dimension `0`
then a relative effective Cartier divisor `D` on `X/Y` is empty, so `i_*((p|_D)^* α) = 0` and
`c₁(𝒪_X(D)) ∩ p^* α = 0` for every `α ∈ CH_{k+1}(Y)`. -/
@[stacks 02TR "second equality, for p of relative dimension 0: D is empty, so \
c_1(O_X(D)) ∩ p^* α = i_*(0) = 0"]
theorem firstChernClassCapChow_divisorSheaf_flatPullbackChow_of_relativeDimension_zero
    (hp : AlgebraicGeometry.RelativeDimension p 0) (α : chowGroup C sY (k + 1)) :
    haveI : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
    firstChernClassCapChow C k sX (Stacks.Divisors.divisorSheaf D)
        (chowGroupCast C sX (show k + 1 + ((0 : ℕ) : ℤ) = k + 1 by simp)
          (flatPullbackChowOfRelativeDimension C sX sY p hbase 0 hp (k + 1) α)) = 0 := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := hD.1
  rw [← GenuineChern.properChowPushforward_gysinChowOfInvertible C sX k
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheafGlobalSection D)
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C _ sX _ rfl _)]
  have := subsingleton_chowGroup_subschemeι_of_relativeDimension_zero C sX k p hp _
    (isRelativeEffectiveCartierDivisor_zeroScheme_divisorSheaf p D hD)
  rw [Subsingleton.elim (gysinChowOfInvertible C sX k _ _ _) 0, map_zero]

end Divisor

end Stacks.Chow

end
