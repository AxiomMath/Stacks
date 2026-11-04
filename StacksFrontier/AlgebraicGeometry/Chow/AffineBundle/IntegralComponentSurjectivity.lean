module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.IntegralImageAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.FlatPullbackFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# The first step of the devissage of Stacks 02TT: reduction to an integral base

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y` be a
quasi-compact morphism of schemes locally of finite type over `S`, flat of relative dimension `r`.
The first step of the proof of Stacks 02TT reduces surjectivity of `f^* : A_k(Y) ⟶ A_{k+r}(X)` to
the case of an **integral** base: it is enough that flat pullback be surjective along the
restriction `f^{-1}(Z) ⟶ Z` of `f` over the integral closed subscheme `Z = closure {y}` attached
to each point `y` of `Y`.

## The argument

A class on `X` is the class of a cycle `α`, and a cycle is the locally finite sum of its prime
components: indexing the support of `α` by `Stacks.Chow.cycleSupportIndex`, the restriction of
`α` to the single point `x` is the `x`-th component, and the family of closures `closure {x}` is
locally finite by `Stacks.Chow.locallyFinite_support_integralComponentAt`. Put
`Z_x = closure(f(x)) = Stacks.Chow.integralComponentAt (f x)`, an integral closed subscheme of
`Y`; the family `(Z_x)` is locally finite because `f` is quasi-compact
(`Stacks.Chow.locallyFinite_integralComponentAt_base_of_quasiCompact`).

The `x`-th component of `α` is supported at the single point `x`, which lies in `f^{-1}(Z_x)`, so
it is the pushforward of a cycle `d_x` on `f^{-1}(Z_x)` — this is
`Stacks.Chow.cyclePullbackAlongClosedImmersion`, whose pushforward restores a cycle vanishing off
the image. By hypothesis there is a class on `Z_x` whose pullback along `f^{-1}(Z_x) ⟶ Z_x` is the
class of `d_x`; choosing cycles `b_x` representing those classes puts the situation in the shape
of `Stacks.Chow.exists_flatPullbackChow_eq_of_finsum_properPushforward`, which assembles the `b_x`
into a single class on `Y` pulling back to the class of `α`.

## Main results

* `Stacks.Chow.flatPullbackChow_surjective_of_forall_integralComponent` — the reduction.

## Implementation notes

No `@[stacks 02TT]` attribute is placed here. This is one step of the proof of that tag, whose
statement is the surjectivity itself; the attribute sits on
`Stacks.Chow.flatPullbackChow_surjective_of_isAffineSpaceBundle` in
`StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity`.

The cycles `d_x` on the inverse images are introduced through an `obtain` on their defining
property rather than named: the family they belong to has a long dependent type, and the only
thing used about them downstream is that their pushforwards are the components of `α`.

The hypothesis quantifies over the structure morphism of `f^{-1}(Z)` and over the proof that the
restriction of `f` commutes with it, rather than fixing them to the pair
`((Z.comap f).subschemeι ≫ f ≫ sY, Stacks.Chow.comapRestrict_comp_base)` the proof itself uses.
Both choices name the same morphism, but not by the same expression, and the Chow group of a
scheme is indexed by the expression; the consumer of this reduction is
`Stacks.Chow.flatPullbackChow_surjective_isIntegral_of_forall_schemeDeltaDimension_lt`, whose
conclusion is stated for the other one.

## References

* [Stacks Project, Tag 02TT](https://stacks.math.columbia.edu/tag/02TT)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] locallyOfFiniteType_comapRestrict flat_comapRestrict

/-- **The first step of the devissage of Stacks 02TT.** Let `f : X ⟶ Y` be quasi-compact and flat
of relative dimension `r` between schemes locally of finite type over the base of chapter 42. If
flat pullback in degree `k` is surjective along the restriction `f^{-1}(Z) ⟶ Z` of `f` over the
integral closed subscheme `Z = closure {y}` for every point `y` of `Y`, then it is surjective
along `f` itself.

A representing cycle is decomposed into its prime components, each is read as a cycle on the
inverse image of the closure of the image of its point, lifted to a class on that closure by the
hypothesis, and the lifts are reassembled by
`Stacks.Chow.exists_flatPullbackChow_eq_of_finsum_properPushforward`. -/
theorem flatPullbackChow_surjective_of_forall_integralComponent (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [AlgebraicGeometry.Flat f] [QuasiCompact f] (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (hint : ∀ (y : Y) (sW : ((integralComponentAt y).comap f).subscheme ⟶ C.S)
      [LocallyOfFiniteType sW]
      (hgb : comapRestrict (integralComponentAt y) f ≫
        ((integralComponentAt y).subschemeι ≫ sY) = sW)
      (hg : AlgebraicGeometry.RelativeDimension (comapRestrict (integralComponentAt y) f) r),
      Function.Surjective (flatPullbackChowOfRelativeDimension C sW
        ((integralComponentAt y).subschemeι ≫ sY) (comapRestrict (integralComponentAt y) f)
        hgb r hg k)) :
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
  -- each prime component is a pushforward from the inverse image of the closure of its image
  obtain ⟨d, hpush⟩ : ∃ d : ∀ x : cycleSupportIndex a,
      CycleGroup C (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY)
        (k + (r : ℤ)),
      ∀ (x : cycleSupportIndex a) (y : X),
        (properPushforward C
          (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
          ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ)) (d x)).1 y =
        (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}).1 y := by
    refine ⟨fun x ↦ cyclePullbackAlongClosedImmersion C
      (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY) (f ≫ sY)
      ((integralComponentAt (f.base x.1)).comap f).subschemeι rfl (k + (r : ℤ))
      (cycleRestrict C (f ≫ sY) (k + (r : ℤ)) a {x.1}), fun x y ↦ ?_⟩
    rw [properPushforward_cyclePullbackAlongClosedImmersion_apply]
    by_cases hy : y ∈ Set.range ((integralComponentAt (f.base x.1)).comap f).subschemeι.base
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      exact (hc0 x y fun h ↦ hy (h ▸ hmem x)).symm
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
    obtain ⟨βx, hβx⟩ := hint (f.base x.1)
      (((integralComponentAt (f.base x.1)).comap f).subschemeι ≫ f ≫ sY)
      (comapRestrict_comp_base C (f ≫ sY) sY f rfl (integralComponentAt (f.base x.1)))
      (relativeDimension_comapRestrict (integralComponentAt (f.base x.1)) f hf)
      (QuotientAddGroup.mk' _ (d x))
    obtain ⟨bx, rfl⟩ := QuotientAddGroup.mk'_surjective
      (rationalEquivalences C ((integralComponentAt (f.base x.1)).subschemeι ≫ sY) k) βx
    rw [flatPullbackChowOfRelativeDimension_mk] at hβx
    exact ⟨bx, QuotientAddGroup.eq_iff_sub_mem.1 hβx⟩
  choose b hb using hex
  exact exists_flatPullbackChow_eq_of_finsum_properPushforward C sY f r hf k
    (fun x : cycleSupportIndex a ↦ integralComponentAt (f.base x.1)) hWloc b d hb a hsum

end Stacks.Chow

end
