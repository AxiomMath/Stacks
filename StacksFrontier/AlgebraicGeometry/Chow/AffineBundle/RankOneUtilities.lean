module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.DevissageOfTrivial
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.TrivialBundle
public import StacksFrontier.AlgebraicGeometry.Chow.BoundedDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.AlgebraicFieldExtension
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.CycleCoefficientSupport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Utilities for the rank-one step of Stacks 02TT

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. The fourth step of the
proof of Stacks 02TT treats a bundle of rank one over an integral base by an induction on the
delta-dimension of that base, run over the *one* base at hand rather than over every base, and it
has to recognize the class of a prime cycle of the total space as a flat pullback after the total
space has been relabelled by an isomorphism. This file collects the three utilities that step
needs, each a small variation on something already available.

* Surjectivity of flat pullback along a globally trivial bundle is
  `Stacks.Chow.flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle`, whose hypothesis is
  surjectivity along the projection of affine space *over every base*. Its proof uses that
  hypothesis only over the target of the bundle, and the structure morphism of the source may be
  presented as any morphism equal to the composite; both generalizations are made here.
* Below the floor `k` there is nothing to prove: a base of delta-dimension `< k` has a total
  space with no point of relative dimension `k + r`, so the target Chow group vanishes. This is
  the step already carried out inside the devissage of Stacks 02TT, repeated here as a
  non-private declaration.
* Flat pullback along an isomorphism carries the prime cycle of `e x` to the prime cycle of `x`
  (Stacks 02RB in relative dimension zero), so membership of the class of a prime cycle in the
  range of a flat pullback transports along an isomorphism of the source over the base. This is
  the new content, and it is where Stacks 02RD enters: the two pullbacks differ by a pullback
  along the isomorphism.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle_of_base` — surjectivity
  of flat pullback along a globally trivial affine-space bundle, from surjectivity along the
  projection of affine space over the one base at hand.
* `Stacks.Chow.mem_range_flatPullbackChow_primeCycle_of_isIso_comp` — membership of the class of
  a prime cycle in the range of a flat pullback transports along an isomorphism over the base.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02RB](https://stacks.math.columbia.edu/tag/02RB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] flat_affineSpaceOver

/-! ### Transport of surjectivity along a single trivialization -/

/-- **Surjectivity of flat pullback along a globally trivial affine-space bundle, over one base.**
If flat pullback along the projection of affine `r`-space over `Y` is surjective in degree `k`,
then so is flat pullback in degree `k` along every morphism to `Y` that is such a projection up to
an isomorphism of its source.

This is `Stacks.Chow.flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle` with its
hypothesis weakened from every base to the base `Y` at hand — the proof only ever used it there —
and with the structure morphism of the source presented as an arbitrary `sX` equal to the
composite. Precomposing with an isomorphism does not change surjectivity, by
`Stacks.Chow.flatPullbackChow_surjective_of_isIso_comp`. -/
theorem flatPullbackChow_surjective_of_isTrivialAffineSpaceBundle_of_base (C : ChowSituation.{u})
    (r : ℕ) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (f : X ⟶ Y) [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f]
    (hbase : f ≫ sY = sX) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (h : IsTrivialAffineSpaceBundle f r)
    (hsurj : Function.Surjective (flatPullbackChowOfRelativeDimension C
      ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) sY (𝔸(ULift.{u} (Fin r); Y) ↘ Y) rfl r
      (relativeDimension_affineSpaceOver Y r) k)) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C sX sY f hbase r hf k) := by
  obtain ⟨e, he⟩ := h
  have _ : IsIso e.hom := inferInstance
  exact flatPullbackChow_surjective_of_isIso_comp C sX
    ((𝔸(ULift.{u} (Fin r); Y) ↘ Y) ≫ sY) sY e.hom (𝔸(ULift.{u} (Fin r); Y) ↘ Y) f he
    (by rw [← Category.assoc, he, hbase]) rfl hbase r (relativeDimension_affineSpaceOver Y r)
    hf k
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
    hsurj

/-! ### Nothing to prove below the floor -/

/-- **A prime cycle pulls back along an isomorphism to a prime cycle.** An isomorphism `e` is flat
and locally of finite type of relative dimension zero
(`Stacks.Chow.relativeDimension_of_isIso`), so Stacks 02RB applies to it in degree `j + 0`; the
flat pullback of the prime cycle of `e x` is then the prime cycle of `x`.

Coefficientwise, the flat-pullback multiplicity of `e` at a point `z` agrees with that of the
identity of the source, by `Stacks.Chow.flatPullbackWeight_eq_of_isIso` applied to the square
`e ≫ e⁻¹ = 𝟙 ≫ 𝟙`, hence is one at a point of relative dimension `j` and zero elsewhere
(`Stacks.Chow.flatPullbackWeight_id`). The cycle factor is the coefficient of the prime cycle of
`e x` at `e z`, which is one exactly when `z = x` because `e` is injective on points. -/
private theorem flatPullback_primeCycle_of_isIso (C : ChowSituation.{u}) {X A : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    (e : X ⟶ A) [IsIso e] (hebase : e ≫ sA = sX) (j : ℤ) (x : X) :
    flatPullback C sX sA e hebase 0 (relativeDimension_of_isIso e) j
        (cycleAssociatedToClosedSubscheme C sA (integralComponentAt (e.base x)).subschemeι j) =
      cycleAssociatedToClosedSubscheme C sX (integralComponentAt x).subschemeι
        (j + ((0 : ℕ) : ℤ)) := by
  have h0 : j + ((0 : ℕ) : ℤ) = j := by simp
  have hdim : ∀ z : X, relativeDimension C.dimensionFunction sX z =
      relativeDimension C.dimensionFunction sA (e.base z) := by
    intro z
    rw [← hebase]
    exact relativeDimension_comp_closedImmersion C.dimensionFunction e sA z
  have hweight : ∀ (i : ℤ) (z : X), flatPullbackWeight C sX e i z =
      flatPullbackWeight C sX (𝟙 X) i z := by
    intro i z
    have h := flatPullbackWeight_eq_of_isIso C sX sX (inv e) (𝟙 X) (Category.id_comp sX) e
      (𝟙 X) (by simp) i z
    simpa using h
  have hinj : Function.Injective e.base := e.isClosedEmbedding.injective
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
  rw [flatPullback_apply, hweight]
  by_cases hz : z = x
  · subst hz
    by_cases hk : relativeDimension C.dimensionFunction sX z = j + ((0 : ℕ) : ℤ)
    · rw [flatPullbackWeight_id C sX (j + ((0 : ℕ) : ℤ)) z hk,
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C sA (e.base z)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sA (e.base z)
            ((hdim z).symm.trans (hk.trans h0))),
        cycleAssociatedToClosedSubscheme_integralComponentAt_self C sX z
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C sX z hk), one_mul]
    · rw [flatPullbackWeight_eq_zero_of_relativeDimension_ne C sX (𝟙 X)
          (j + ((0 : ℕ) : ℤ)) z hk,
        cycleAssociatedToClosedSubscheme_apply_eq_zero_of_relativeDimension_ne C sX _
          (j + ((0 : ℕ) : ℤ)) hk, mul_zero]
  · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sA j (e.base x)
        (fun h ↦ hz (hinj h)),
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C sX (j + ((0 : ℕ) : ℤ)) x hz,
      zero_mul]

/-- Flat pullback on Chow groups depends on the morphism and on its relative dimension only
through their values: equal morphisms of equal relative dimension pull a class back to the same
thing, up to the resulting equality of degrees. -/
private theorem flatPullbackChow_heq_of_eq (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    {w w' : A ⟶ B} [LocallyOfFiniteType w] [AlgebraicGeometry.Flat w] [LocallyOfFiniteType w']
    [AlgebraicGeometry.Flat w'] (hww' : w = w') {m n : ℕ} (hmn : m = n) (hw : w ≫ sB = sA)
    (hw' : w' ≫ sB = sA) (hwm : AlgebraicGeometry.RelativeDimension w m)
    (hw'n : AlgebraicGeometry.RelativeDimension w' n) (k : ℤ) (a : chowGroup C sB k) :
    flatPullbackChowOfRelativeDimension C sA sB w hw m hwm k a ≍
      flatPullbackChowOfRelativeDimension C sA sB w' hw' n hw'n k a := by
  subst hww'
  subst hmn
  rfl

/-- The class of the prime cycle of a point is unchanged, up to transport, by writing its degree
differently. -/
private theorem chowGroup_mk_primeCycle_heq (C : ChowSituation.{u}) {X : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (x : X) {j j' : ℤ} (hj : j = j') :
    (QuotientAddGroup.mk' (rationalEquivalences C sX j)
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x).subschemeι j)) ≍
      (QuotientAddGroup.mk' (rationalEquivalences C sX j')
        (cycleAssociatedToClosedSubscheme C sX (integralComponentAt x).subschemeι j')) := by
  subst hj
  rfl

/-- **Membership of the class of a prime cycle in the range of a flat pullback transports along
an isomorphism over the base.** Let `p = e ≫ q` with `e : X ⟶ A` an isomorphism over the base and
`q : A ⟶ Y` flat of relative dimension `r`, and let `x` be a point of `X`. If the class in
`A_{k+r}(A)` of the prime cycle of `e x` is in the range of `q^* : A_k(Y) ⟶ A_{k+r}(A)`, then the
class in `A_{k+r}(X)` of the prime cycle of `x` is in the range of
`p^* : A_k(Y) ⟶ A_{k+r}(X)`.

The witness for the conclusion is the one for the hypothesis: pulling it back along `q` and then
along `e` is pulling it back along `p`, by Stacks 02RD on Chow groups
(`Stacks.Chow.flatPullbackChow_comp`, whose two sides sit in the degrees `(k + r) + 0` and
`k + (0 + r)`), and flat pullback along `e` carries the prime cycle of `e x` to the prime cycle
of `x`. -/
theorem mem_range_flatPullbackChow_primeCycle_of_isIso_comp (C : ChowSituation.{u})
    {X A Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sA : A ⟶ C.S)
    [LocallyOfFiniteType sA] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (e : X ⟶ A) [IsIso e]
    (q : A ⟶ Y) [LocallyOfFiniteType q] [AlgebraicGeometry.Flat q] (p : X ⟶ Y)
    [LocallyOfFiniteType p] [AlgebraicGeometry.Flat p] (hp : e ≫ q = p) (hebase : e ≫ sA = sX)
    (hqbase : q ≫ sY = sA) (hpbase : p ≫ sY = sX) (r : ℕ)
    (hq : AlgebraicGeometry.RelativeDimension q r)
    (hpr : AlgebraicGeometry.RelativeDimension p r) (k : ℤ) (x : X)
    (h : (QuotientAddGroup.mk' (rationalEquivalences C sA (k + (r : ℤ)))
            (cycleAssociatedToClosedSubscheme C sA
              (integralComponentAt (e.base x)).subschemeι (k + (r : ℤ)))) ∈
          (flatPullbackChowOfRelativeDimension C sA sY q hqbase r hq k).range) :
    (QuotientAddGroup.mk' (rationalEquivalences C sX (k + (r : ℤ)))
            (cycleAssociatedToClosedSubscheme C sX
              (integralComponentAt x).subschemeι (k + (r : ℤ)))) ∈
          (flatPullbackChowOfRelativeDimension C sX sY p hpbase r hpr k).range := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β, ?_⟩
  have h0 : k + (r : ℤ) + ((0 : ℕ) : ℤ) = k + (r : ℤ) := by push_cast; ring
  have hcompbase : (e ≫ q) ≫ sY = sX := by rw [Category.assoc, hqbase, hebase]
  -- Stacks 02RD: pulling back along `q` and then along `e` is pulling back along `e ≫ q`
  have hcomp :
      flatPullbackChow C sX sA e hebase 0 (relativeDimension_of_isIso e) (k + (r : ℤ))
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
          (flatPullbackChowOfRelativeDimension C sA sY q hqbase r hq k β) ≍
        flatPullbackChowOfRelativeDimension C sX sY (e ≫ q) hcompbase (0 + r)
          (AlgebraicGeometry.RelativeDimension.comp_of_flat e q
            (relativeDimension_of_isIso e) hq) k β :=
    flatPullbackChow_comp C sX sA sY e q hebase hqbase 0 r (relativeDimension_of_isIso e) hq k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) β
  -- the pullback along `e ≫ q` is the pullback along `p`, of relative dimension `r`
  have hcongr := flatPullbackChow_heq_of_eq C sX sY hp (Nat.zero_add r) hcompbase hpbase
    (AlgebraicGeometry.RelativeDimension.comp_of_flat e q (relativeDimension_of_isIso e) hq)
    hpr k β
  -- flat pullback along `e` carries the prime cycle of `e x` to the prime cycle of `x`
  have hprime :
      flatPullbackChow C sX sA e hebase 0 (relativeDimension_of_isIso e) (k + (r : ℤ))
          (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _)
          (QuotientAddGroup.mk' (rationalEquivalences C sA (k + (r : ℤ)))
            (cycleAssociatedToClosedSubscheme C sA
              (integralComponentAt (e.base x)).subschemeι (k + (r : ℤ)))) ≍
        (QuotientAddGroup.mk' (rationalEquivalences C sX (k + (r : ℤ)))
          (cycleAssociatedToClosedSubscheme C sX
            (integralComponentAt x).subschemeι (k + (r : ℤ)))) := by
    rw [flatPullbackChow_mk, flatPullback_primeCycle_of_isIso C sX sA e hebase (k + (r : ℤ)) x]
    exact chowGroup_mk_primeCycle_heq C sX x h0
  rw [hβ] at hcomp
  exact eq_of_heq ((hcomp.trans hcongr).symm.trans hprime)

end Stacks.Chow

end
