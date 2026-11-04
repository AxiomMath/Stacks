module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.DominantPrimeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.GeneralRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.LocalizationSurjectivity

/-!
# Transporting a prime cycle

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The *prime cycle* of a
point `x` of a scheme `X` locally of finite type over `S` is the cycle of Stacks 02QU attached to
the integral closed subscheme `Stacks.Chow.integralComponentAt x`, the reduced induced structure
on the closure of `x`. In degree `k` it is the cycle with coefficient one at `x` and zero
elsewhere when `x` has relative dimension `k`, and the zero cycle otherwise; so the prime cycles
are a basis of the group of `k`-cycles, and a homomorphism between cycle groups is pinned down by
its values on them.

This file records how the two cycle-level transport maps of chapter 42 act on a prime cycle. The
pullback of a cycle along a closed immersion (`Stacks.Chow.cyclePullbackAlongClosedImmersion`,
which reads off the coefficient at the image point) carries the prime cycle of `i x'` to the
prime cycle of `x'`; and flat pullback (Stacks 02RB) along an isomorphism, which has relative
dimension zero, carries the prime cycle of `e a` to the prime cycle of `a`. Both are proved
coefficientwise from the two coefficient formulas of Stacks 02QU, using that a closed immersion
preserves relative dimension and that the flat-pullback multiplicity along the identity is one.

The remaining two results concern the generic point of an integral scheme. There the prime cycle
is the fundamental cycle, because both are the cycle with coefficient one at the generic point;
combined with the fact that flat pullback carries a fundamental cycle to a fundamental cycle,
this exhibits the class of the prime cycle of the generic point of the total space of a flat
morphism as a flat pullback. That is the generator the surjectivity argument for an affine bundle
needs: it reduces a class on the total space to a class on the base.

## Main results

All four live in the `Stacks.Chow` namespace, and their names are abbreviated to the part after
that prefix here.

* `cyclePullbackAlongClosedImmersion_cycleAssociatedToClosedSubscheme_integralComponentAt`
  -- pullback along a closed immersion carries a prime cycle to a prime cycle.
* `flatPullback_cycleAssociatedToClosedSubscheme_integralComponentAt_of_isIso`
  -- flat pullback along an isomorphism carries a prime cycle to a prime cycle.
* `cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint_eq_fundamentalCycle`
  -- on an integral scheme of delta-dimension `k` the prime cycle of the generic point is the
  fundamental cycle in degree `k`.
* `mem_range_flatPullbackChow_cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint`
  -- the class of the prime cycle of the generic point of the total space of a flat morphism is a
  flat pullback, namely of the fundamental class of the base.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Pullback of a prime cycle along a closed immersion -/

/-- **A prime cycle pulls back along a closed immersion to a prime cycle.** For a closed
immersion `i : X' ⟶ X` over the base and a point `x'` of `X'`, the pullback of the prime cycle of
`i x'` in degree `k` is the prime cycle of `x'` in degree `k`.

Both sides are compared coefficientwise at a point `z` of `X'`. Away from `x'` both vanish, since
`i` is injective, so `i z` differs from `i x'`. At `x'` both are the coefficient of a prime cycle
at its own point, hence one if the relative dimension is `k` and zero otherwise; and the relative
dimension of `x'` over the base is that of `i x'` by
`Stacks.Chow.relativeDimension_comp_closedImmersion`. -/
theorem cyclePullbackAlongClosedImmersion_cycleAssociatedToClosedSubscheme_integralComponentAt
    (C : ChowSituation.{u}) {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (i : X' ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ sX = sX') (k : ℤ) (x' : X') :
    cyclePullbackAlongClosedImmersion C sX' sX i hi k
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt (i.base x')).subschemeι k) =
      cycleAssociatedToClosedSubscheme C sX' (integralComponentAt x').subschemeι k := by
  have hdim : ∀ z : X', relativeDimension C.dimensionFunction sX' z =
      relativeDimension C.dimensionFunction sX (i.base z) := by
    intro z
    rw [← hi, relativeDimension_comp_closedImmersion]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [cyclePullbackAlongClosedImmersion_apply]
  by_cases hz : z = x'
  · subst hz
    by_cases hk : relativeDimension C.dimensionFunction sX' z = k
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C sX (i.base z)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sX (i.base z)
            ((hdim z).symm.trans hk)),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C sX' z
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sX' z hk)]
    · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C sX _ k
          (fun h ↦ hk ((hdim z).trans h)),
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C sX' _ k hk]
  · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX k (i.base x')
        (fun h ↦ hz (i.isClosedEmbedding.injective h)),
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX' k x' hz]

/-! ### Flat pullback of a prime cycle along an isomorphism -/

/-- **A prime cycle pulls back along an isomorphism to a prime cycle.** An isomorphism `e` is
flat and locally of finite type of relative dimension zero
(`Stacks.Chow.relativeDimension_of_isIso`), so Stacks 02RB applies to it in degree `k + 0`; the
flat pullback of the prime cycle of `e a` is then the prime cycle of `a`.

Coefficientwise, the flat-pullback multiplicity of `e` at a point `z` agrees with that of the
identity of the source, by `Stacks.Chow.flatPullbackWeight_eq_of_isIso` applied to the square
`e ≫ e⁻¹ = 𝟙 ≫ 𝟙`, hence is one at a point of relative dimension `k` and zero elsewhere
(`Stacks.Chow.flatPullbackWeight_id`). The cycle factor is the coefficient of the prime cycle of
`e a` at `e z`, which is one exactly when `z = a` because `e` is injective on points. -/
theorem flatPullback_cycleAssociatedToClosedSubscheme_integralComponentAt_of_isIso
    (C : ChowSituation.{u}) {A A' : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (sA' : A' ⟶ C.S) [LocallyOfFiniteType sA'] (e : A ⟶ A') [IsIso e] (he : e ≫ sA' = sA)
    (k : ℤ) (a : A) :
    flatPullback C sA sA' e he 0 (relativeDimension_of_isIso e) k
        (cycleAssociatedToClosedSubscheme C sA' (integralComponentAt (e.base a)).subschemeι k) =
      cycleAssociatedToClosedSubscheme C sA (integralComponentAt a).subschemeι
        (k + ((0 : ℕ) : ℤ)) := by
  have h0 : k + ((0 : ℕ) : ℤ) = k := by simp
  have hdim : ∀ z : A, relativeDimension C.dimensionFunction sA z =
      relativeDimension C.dimensionFunction sA' (e.base z) := by
    intro z
    rw [← he]
    exact relativeDimension_comp_closedImmersion C.dimensionFunction e sA' z
  have hweight : ∀ (j : ℤ) (z : A), flatPullbackWeight C sA e j z =
      flatPullbackWeight C sA (𝟙 A) j z := by
    intro j z
    have h := flatPullbackWeight_eq_of_isIso C sA sA (inv e) (𝟙 A) (Category.id_comp sA) e
      (𝟙 A) (by simp) j z
    simpa using h
  have hinj : Function.Injective e.base := e.isClosedEmbedding.injective
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [flatPullback_apply, hweight]
  by_cases hz : z = a
  · subst hz
    by_cases hk : relativeDimension C.dimensionFunction sA z = k
    · rw [flatPullbackWeight_id C sA (k + ((0 : ℕ) : ℤ)) z (hk.trans h0.symm),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C sA' (e.base z)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sA' (e.base z)
            ((hdim z).symm.trans hk)),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C sA z
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sA z
            (hk.trans h0.symm)), one_mul]
    · rw [flatPullbackWeight_eq_zero_of_relativeDimension_ne C sA (𝟙 A)
          (k + ((0 : ℕ) : ℤ)) z (fun h ↦ hk (h.trans h0)),
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C sA _
          (k + ((0 : ℕ) : ℤ)) (fun h ↦ hk (h.trans h0)),
        mul_zero]
  · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sA' k (e.base a)
        (fun h ↦ hz (hinj h)),
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sA (k + ((0 : ℕ) : ℤ)) a hz,
      zero_mul]

/-! ### The prime cycle of a generic point is the fundamental cycle -/

/-- **The fundamental cycle is the prime cycle of the generic point.** On an integral scheme `X`
locally of finite type over the base and of delta-dimension `k`, the prime cycle of the generic
point of `X` in degree `k` is the fundamental cycle `[X]_k`.

Both sides are the cycle with coefficient one at the generic point of `X` and zero elsewhere:
apply `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_single` to the integral closed subscheme
`Stacks.Chow.integralComponentAt (genericPoint X)`, whose generic point maps to `genericPoint X`,
and to the identity of `X`, whose source is integral by hypothesis. The relative dimension of the
generic point is `k` because `X` is irreducible. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint_eq_fundamentalCycle
    (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X]
    {k : ℤ} (hk : schemeDeltaDimension C p = (k : EInt)) :
    cycleAssociatedToClosedSubscheme C p (integralComponentAt (genericPoint X)).subschemeι k =
      fundamentalCycle C p k := by
  classical
  let _ : IsIntegral (integralComponentAt (genericPoint X)).subscheme :=
    isIntegral_integralComponentAt _
  have hgen : relativeDimension C.dimensionFunction p (genericPoint X) = k :=
    WithBotTop.coe_injective ((schemeDeltaDimension_eq_genericPoint C p).symm.trans hk)
  have hsub : (integralComponentAt (genericPoint X)).subschemeι.base
      (genericPoint (integralComponentAt (genericPoint X)).subscheme) = genericPoint X := by
    simpa [genericPointOf] using genericPointOf_integralComponentAt (genericPoint X)
  refine Subtype.ext ?_
  rw [cycleAssociatedToClosedSubscheme_eq_single C p
      (integralComponentAt (genericPoint X)).subschemeι k (by rw [hsub]; exact hgen),
    fundamentalCycle,
    cycleAssociatedToClosedSubscheme_eq_single C p (𝟙 X) k (by simpa using hgen), hsub]
  simp

/-! ### The prime cycle of the generic point of a flat total space is a flat pullback -/

/-- **The class of the prime cycle of the generic point of the total space of a flat morphism is
a flat pullback.** Let `f : X ⟶ Y` be flat and locally of finite type of relative dimension `r`,
with `X` and `Y` integral, `Y` of delta-dimension `k` and `X` of delta-dimension `k + r`. Then
the class in `A_{k+r}(X)` of the prime cycle of the generic point of `X` is in the range of
`f^* : A_k(Y) ⟶ A_{k+r}(X)`.

The witness is the fundamental class `[Y]_k`: flat pullback carries it to the fundamental cycle
`[X]_{k+r}` by `Stacks.Chow.flatPullback_fundamentalCycle`, and that cycle is the prime cycle of
the generic point of `X` by
`Stacks.Chow.cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint_eq_fundamentalCycle`
above. -/
theorem mem_range_flatPullbackChow_cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] [IsIntegral X] [IsIntegral Y]
    (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) {k : ℤ}
    (hk : schemeDeltaDimension C sY = (k : EInt))
    (hX : schemeDeltaDimension C (f ≫ sY) = ((k + (r : ℤ) : ℤ) : EInt)) :
    (QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sY) (k + (r : ℤ)))
        (cycleAssociatedToClosedSubscheme C (f ≫ sY)
          (integralComponentAt (genericPoint X)).subschemeι (k + (r : ℤ)))) ∈
      (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k).range := by
  refine ⟨fundamentalChowClass C sY k, ?_⟩
  rw [fundamentalChowClass, flatPullbackChowOfRelativeDimension_mk,
    flatPullback_fundamentalCycle C (f ≫ sY) sY f rfl r hf k (le_of_eq hk),
    cycleAssociatedToClosedSubscheme_integralComponentAt_genericPoint_eq_fundamentalCycle C
      (f ≫ sY) hX]

end Stacks.Chow

end
