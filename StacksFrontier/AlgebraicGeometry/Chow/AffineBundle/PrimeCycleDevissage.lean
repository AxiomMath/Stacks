module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralImageAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.FlatPullbackFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# The devissage of Stacks 02TT needs only prime cycles over an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
quasi-compact morphism of schemes locally of finite type over `S`, flat of relative dimension `r`.
The first step of the proof of Stacks 02TT reduces surjectivity of `f^* : A_k(Y) ⟶ A_{k+r}(X)` to
the case of an **integral** base. What that reduction consumes over the integral closed subscheme
`Z_y = closure {y}` of the base is much less than surjectivity of flat pullback along the
restriction `f^{-1}(Z_y) ⟶ Z_y`: the only classes it ever has to lift are the classes of **prime
cycles with coefficient one**, one for each point of `X`. This is the sentence of the second
paragraph of Stacks 02TT that reduces the statement to `Y` integral and `α = [W]`.

## The argument

The proof is the one of `Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent`
with its single appeal to the hypothesis weakened. A class on `X` is the class of a cycle `α`,
and `α` is the locally finite sum of its prime components: the restriction of `α` to a single
point `x` of its support is the `x`-th component, and those components are read as cycles `d_x`
on the inverse images `f^{-1}(Z_{f x})` through
`Stacks.Chow.cyclePullbackAlongClosedImmersion`, whose pushforward restores a cycle vanishing
off the image.

The point is that the restriction of `α` to `{x}` is not an arbitrary cycle: it is the integer
`α_x` times the fundamental cycle of `Z_x = closure {x}`, because that fundamental cycle has
coefficient one at `x` and coefficient zero elsewhere
(`Stacks.Chow.cycleAssociatedToClosedSubscheme_integralComponentAt_self`,
`Stacks.Chow.cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne`). Pulling back along a
closed immersion is coefficientwise, hence commutes with multiplication by an integer, so `d_x`
is `α_x` times the pullback of that fundamental cycle. The range of flat pullback is an additive
subgroup, so it is enough that it contain the class of the pullback of the fundamental cycle
alone: the class of `d_x` then lies in it by `AddSubgroup.zsmul_mem`. From there the proof is
again `Stacks.Chow.exists_flatPullbackChow_eq_of_finsum_properPushforward`, which assembles the
lifts into a single class on `Y` pulling back to the class of `α`.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_forall_primeCycle` — the reduction, with a
  hypothesis only about the classes of prime cycles with coefficient one.

## Implementation notes

No `@[stacks 02TT]` attribute is placed here. This is one step of the proof of that tag, whose
statement is the surjectivity itself; the attribute sits on
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`.

Unlike in `Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent`, the cycles `d_x`
on the inverse images cannot be introduced by an `obtain` on their defining property alone: the
weakened hypothesis applies to them only once they are known to be integer multiples of pullbacks
of fundamental cycles, so that identification is carried along as a second component of the same
`obtain`.

The hypothesis fixes the structure morphism of `f^{-1}(Z)` to
`(Z.comap f).subschemeι ≫ f ≫ sY` and the commutation proof to
`Stacks.Chow.comapRestrict_comp_base`, which is what the proof itself uses; no quantification
over those choices is needed here, because the hypothesis is applied to one explicit cycle rather
than used as a surjectivity statement.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] locallyOfFiniteType_comapRestrict flat_comapRestrict

/-- The restriction of a `k`-cycle `a` to a single point `x` is the coefficient of `a` at `x`
times the fundamental cycle of the integral closed subscheme attached to `x`: both sides have
coefficient `a_x` at `x` and coefficient zero at every other point. -/
private theorem cycleRestrict_singleton_eq_zsmul (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) (a : CycleGroup C p k) (x : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = (k : EInt)) :
    cycleRestrict C p k a {x} =
      a.1 x • cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  by_cases hy : y = x
  · subst hy
    simp [cycleAssociatedToClosedSubscheme_integralComponentAt_self C p y hDim]
  · simp [hy, cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x hy]

/-- Pulling a cycle back along a closed immersion commutes with multiplication by an integer:
the pullback is coefficientwise. -/
private theorem cyclePullbackAlongClosedImmersion_zsmul (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsClosedImmersion i] (hi : i ≫ sX = sZ) (k : ℤ)
    (n : ℤ) (c : CycleGroup C sX k) :
    cyclePullbackAlongClosedImmersion C sZ sX i hi k (n • c) =
      n • cyclePullbackAlongClosedImmersion C sZ sX i hi k c :=
  Subtype.ext (Function.locallyFinsuppWithin.ext fun _ ↦ rfl)

/-- **The first step of the devissage of Stacks 02TT, from prime cycles only.** Let
`f : X ⟶ Y` be quasi-compact and flat of relative dimension `r` between schemes locally of finite
type over the base of chapter 42. For each point `x` of `X` write `Z = closure {f x}` for the
integral closed subscheme of `Y` attached to its image. If for every `x` the class on
`f^{-1}(Z)` of the prime cycle of `closure {x}` — pulled back along the closed immersion
`f^{-1}(Z) ⟶ X`, so with coefficient one — is in the range of flat pullback along the
restriction `f^{-1}(Z) ⟶ Z` of `f`, then flat pullback in degree `k` is surjective along `f`
itself.

This is the hypothesis of
`Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent` weakened from surjectivity
over each integral closed subscheme of the base to the single prime cycle the proof uses: that
cycle is the only thing the devissage has to lift, because the range of flat pullback is an
additive subgroup and the prime components of a cycle are integer multiples of prime cycles. -/
theorem flatPullbackChow_surjective_of_forall_primeCycle (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] [QuasiCompact f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hprime : ∀ x : X,
      (QuotientAddGroup.mk' (rationalEquivalences C
          (((integralComponentAt (f.base x)).comap f).subschemeι ≫ f ≫ sY) (k + (r : ℤ)))
        (cyclePullbackAlongClosedImmersion C
          (((integralComponentAt (f.base x)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
          ((integralComponentAt (f.base x)).comap f).subschemeι rfl (k + (r : ℤ))
          (cycleAssociatedToClosedSubscheme C (f ≫ sY)
            (integralComponentAt x).subschemeι (k + (r : ℤ))))) ∈
      (flatPullbackChowOfRelativeDimension C
          (((integralComponentAt (f.base x)).comap f).subschemeι ≫ f ≫ sY)
          ((integralComponentAt (f.base x)).subschemeι ≫ sY)
          (comapRestrict (integralComponentAt (f.base x)) f)
          (comapRestrict_comp_base C (f ≫ sY) sY f rfl (integralComponentAt (f.base x))) r
          (relativeDimension_comapRestrict (integralComponentAt (f.base x)) f hf) k).range) :
    Function.Surjective (flatPullbackChowOfRelativeDimension C (f ≫ sY) sY f rfl r hf k) := by
  intro α
  induction α using QuotientAddGroup.induction_on with
  | H a =>
  -- the closures of the points of the support of `a`, and of their images
  have hσ : LocallyFinite fun x : cycleSupportIndex a ↦ closure ({x.1} : Set X) := by
    simpa only [coe_support_integralComponentAt] using
      locallyFinite_support_integralComponentAt a
  have hWloc : LocallyFinite fun x : cycleSupportIndex a ↦
      ((integralComponentAt (f.base x.1)).support : Set Y) :=
    locallyFinite_integralComponentAt_base_of_quasiCompact f
      (fun x : cycleSupportIndex a ↦ x.1) hσ
  -- a point of the support lies in the inverse image of the closure of its image
  have hmem : ∀ x : cycleSupportIndex a,
      x.1 ∈ Set.range ((integralComponentAt (f.base x.1)).comap f).subschemeι.base := by
    intro x
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_comap]
    simpa only [Set.mem_preimage, coe_support_integralComponentAt] using
      subset_closure (Set.mem_singleton (f.base x.1))
  -- the prime components of `a`
  have hc0 : ∀ (x : cycleSupportIndex a) (y : X), y ≠ x.1 →
      (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}).1 y = 0 := fun x y hy ↦
    cycleRestrict_apply_of_notMem C (f ≫ sY) (k + (r : ℤ)) a (by simpa using hy)
  have hrestrict : ∀ y : X, a.1 y =
      ∑ᶠ x : cycleSupportIndex a, (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}).1 y := by
    intro y
    by_cases hy : a.1 y = 0
    · rw [hy, eq_comm]
      refine finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_
      by_cases hyx : y = x.1
      · exact absurd (hyx ▸ hy) x.2
      · exact hc0 x y hyx
    · rw [finsum_eq_single _ (⟨y, hy⟩ : cycleSupportIndex a) fun x hx ↦
        hc0 x y fun h ↦ hx (Subtype.ext h.symm)]
      exact (cycleRestrict_apply_of_mem C (f ≫ sY) (k + (r : ℤ)) a
        (Set.mem_singleton y)).symm
  -- each prime component is a pushforward from the inverse image of the closure of its image,
  -- and is an integer multiple of the pullback of a prime cycle
  obtain ⟨d, hpush, hdval⟩ : ∃ d : ∀ x : cycleSupportIndex a,
      CycleGroup C (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY)
        (k + (r : ℤ)),
      (∀ (x : cycleSupportIndex a) (y : X),
        (properPushforward C
          (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
          ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ)) (d x)).1 y =
        (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}).1 y) ∧
      ∀ x : cycleSupportIndex a, d x = a.1 x.1 • cyclePullbackAlongClosedImmersion C
        (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
        ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ))
        (cycleAssociatedToClosedSubscheme C (f ≫ sY)
          (integralComponentAt x.1).subschemeι (k + (r : ℤ))) := by
    refine ⟨fun x ↦ cyclePullbackAlongClosedImmersion C
      (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
      ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ))
      (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}), fun x y ↦ ?_, fun x ↦ ?_⟩
    · rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
      by_cases hy : y ∈ Set.range ((integralComponentAt (f.base x.1)).comap f).subschemeι.base
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy]
        exact (hc0 x y fun h ↦ hy (h ▸ hmem x)).symm
    · dsimp only
      rw [cycleRestrict_singleton_eq_zsmul C (f ≫ sY) (k + (r : ℤ)) a x.1
        (schemeDeltaDimension_cycleSupportIndex a x), cyclePullbackAlongClosedImmersion_zsmul]
  have hsum : ∀ y : X, a.1 y = ∑ᶠ x : cycleSupportIndex a, (properPushforward C
      (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
      ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ)) (d x)).1 y := by
    intro y
    rw [hrestrict y]
    exact finsum_congr fun x ↦ (hpush x y).symm
  -- lift each component to the closure of the image of its point
  have hex : ∀ x : cycleSupportIndex a,
      ∃ bx : CycleGroup C ((integralComponentAt (f.base x.1)).subschemeι ≫ sY) k,
        RationallyEquivalent C
          (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (k + (r : ℤ))
          (flatPullback C
            (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY)
            ((integralComponentAt (f.base x.1)).subschemeι ≫ sY)
            (comapRestrict (integralComponentAt (f.base x.1)) f)
            (comapRestrict_comp_base C (f ≫ sY) sY f rfl (integralComponentAt (f.base x.1))) r
            (relativeDimension_comapRestrict (integralComponentAt (f.base x.1)) f hf) k bx)
          (d x) := by
    intro x
    have hrange : (QuotientAddGroup.mk' (rationalEquivalences C
        (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (k + (r : ℤ)))
        (d x)) ∈ (flatPullbackChowOfRelativeDimension C
          (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY)
          ((integralComponentAt (f.base x.1)).subschemeι ≫ sY)
          (comapRestrict (integralComponentAt (f.base x.1)) f)
          (comapRestrict_comp_base C (f ≫ sY) sY f rfl (integralComponentAt (f.base x.1))) r
          (relativeDimension_comapRestrict (integralComponentAt (f.base x.1)) f hf) k).range := by
      rw [hdval x, map_zsmul]
      exact AddSubgroup.zsmul_mem _ (hprime x.1) _
    obtain ⟨βx, hβx⟩ := hrange
    obtain ⟨bx, rfl⟩ := QuotientAddGroup.mk'_surjective
      (rationalEquivalences C ((integralComponentAt (f.base x.1)).subschemeι ≫ sY) k) βx
    rw [flatPullbackChowOfRelativeDimension_mk] at hβx
    exact ⟨bx, QuotientAddGroup.eq_iff_sub_mem.1 hβx⟩
  choose b hb using hex
  exact exists_flatPullbackChow_eq_of_finsum_properPushforward C sY f r hf k
    (fun x : cycleSupportIndex a ↦ integralComponentAt (f.base x.1)) hWloc b d hb a hsum

end Stacks.Chow

end
