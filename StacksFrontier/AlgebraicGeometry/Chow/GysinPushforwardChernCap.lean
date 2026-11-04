module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme

/-!
# Pushing the Gysin class forward is capping with the first Chern class

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module and let `s ∈ Γ(X, L)` be a global section with zero
scheme `i : D = Z(s) ⟶ X`. Stacks 02T9 is the identity

  `i_* i^* α = c₁(L) ∩ α`  in  `A_k(X)`,  for `α ∈ Z_{k+1}(X)`,

where `i^*` is the Gysin homomorphism of Stacks 02T8 and `c₁(L) ∩ −` is the cap product of
Stacks 02SO. In particular, when `D` is an effective Cartier divisor, intersection with `D` is
capping with `c₁(𝒪_X(D))`.

The proof is the source's. Both sides are extensions of a rule on the integral components of `X`,
so the identity is compared component by component. For an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1`:

* if `W ⊆ D`, the Gysin rule is the pushforward into `D` of a cycle representing
  `c₁(L|_W) ∩ [W]`, and pushing on into `X` gives the pushforward of that same cycle along
  `W ⟶ X` — which is exactly what the cap product rule pushes forward, up to the choice of a
  representative, hence up to rational equivalence on `W`;
* if `W ⊄ D`, the Gysin rule is the fundamental cycle of the scheme-theoretic intersection
  `W ∩ D`, which is the same closed subscheme of `X` whether it is formed inside `D` or inside
  `W` (`Stacks.ChernCap42.exists_iso_comap_sup` twice, reconciled by `sup_comm`); and the cycle
  the cap product rule chose on `W` differs from it by a principal divisor, because `D ∩ W` is
  the zero scheme of the restriction `s|_W`, which is nonzero precisely because `W ⊄ D`.

Both comparisons are rational equivalences **on `W`**, and a cycle is only a *locally* finite sum
of its components, so they are assembled by Stacks 02RZ in the form
`Stacks.Chow.rationallyEquivalent_finsum_of_closedSupports`, over the canonical presentation
`Stacks.Chow.cycle_eq_finsum_primeCycles` of `α` by the integral closed subschemes attached to the
points of its support.

## Main results

* `Stacks.Chow.exists_properPushforward_gysinComponentCycle_eq` — the component comparison: on a
  single integral closed subscheme the pushed Gysin component cycle is the pushforward of a cycle
  rationally equivalent to the cap product component cycle.
* `Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible` — **Stacks 02T9.**
* `Stacks.Chow.effectiveCartierIntersection_divisorSheaf_eq_firstChernClassCapOfInvertible` —
  the "in particular" clause of Stacks 02T9: intersection with an effective Cartier divisor `D`
  is capping with `c₁(𝒪_X(D))`. It is deduced from
  `Stacks.Chow.effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible`, the
  same statement for an arbitrary pair `(L, s)` whose zero scheme is an effective Cartier
  divisor.

## Implementation notes

### Nothing is assumed

Unlike `StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward` and
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ProperPushforward`, no component rule and no
integral-component compatibility is carried here. Both operations are taken at the component rule
`Stacks.Chow.firstChernComponentClass` of `L` itself, and the component comparison is *proved*:
the two rules are built from the same chosen meromorphic section of `L|_W`, and
`Stacks.Chow.firstChernComponentClass_eq_mk` says the class-valued rule is the class of the
cycle-valued one by definition. That is why Stacks 02T9 is reachable where Stacks 02TI, 02TM and
02TO are not — those compare the rule of `L` on `X` with the rule of a *different* module on a
*different* scheme, which needs the key formula of Stacks 0AYC.

The vanishing of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is not carried
either: every morphism pushed along below is a closed immersion, for which Stacks 02S2 is proved
outright as
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`.

### The grading of the source

The source writes `α` as a `(k+1)`-cycle and the conclusion in `CH_k(X)`, which is what is used
here. The displayed proof of the source writes `dim_δ(W_j) = k` for the components of `α`; that is
a slip, since `α` is a `(k+1)`-cycle. The statement is the one above.

### The two "in particular" forms

`Stacks.Chow.effectiveCartierIntersection` indexes intersection with an effective Cartier divisor
by a pair `(L, s)` whose zero scheme is that divisor, so the "in particular" clause is immediate
from the main theorem in that indexing. The form indexed by the divisor `D` itself, with
`L = 𝒪_X(D)` and `s = 1_D`, follows because `Z(1_D) = D`
(`Stacks.Divisors.zeroScheme_canonicalSection`, Stacks 01X0) and because the effective Cartier
hypothesis is carried but unused by the construction.

## References

* [Stacks Project, Tag 02T9](https://stacks.math.columbia.edu/tag/02T9)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02SQ](https://stacks.math.columbia.edu/tag/02SQ)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 01X0](https://stacks.math.columbia.edu/tag/01X0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Three small transport lemmas -/

/-- Proper pushforward commutes with integer multiples of a cycle. -/
private theorem properPushforward_zsmul (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ) (n : ℤ) (c : CycleGroup C sX k) :
    properPushforward C sX sY f hf k (n • c) = n • properPushforward C sX sY f hf k c :=
  map_zsmul (properPushforwardHom C sX sY f hf k) n c

/-- The coefficient of an integer multiple of a cycle. -/
private theorem zsmul_cycle_apply (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) (n : ℤ) (c : CycleGroup C p k) (x : X) :
    (n • c).1 x = n * c.1 x := by simp

/-- A locally finite sum over a type whose terms vanish off a subtype is the sum over that
subtype. -/
private theorem finsum_subtype_eq_finsum_of_eq_zero {A : Type*} (q : A → Prop) (g : A → ℤ)
    (hg : ∀ a, ¬ q a → g a = 0) : ∑ᶠ a : {a // q a}, g a.1 = ∑ᶠ a : A, g a := by
  classical
  rw [finsum_subtype_eq_finsum_cond]
  refine finsum_congr fun a ↦ ?_
  by_cases h : q a
  · have _ : Unique (q a) := ⟨⟨h⟩, fun _ ↦ rfl⟩
    rw [finsum_unique]
  · have _ : IsEmpty (q a) := ⟨h⟩
    rw [finsum_of_isEmpty, hg a h]

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-! ### The restriction of the section to an integral component -/

/-- **The restriction of `s` to an integral closed subscheme not contained in the zero scheme is
nonzero.** By Stacks 02OR (2) a vanishing restriction would factor the immersion of `W` through
the zero scheme `D = Z(s)`, putting the support of `W` inside the support of `D`; as `W` is
reduced it is the vanishing ideal of its support, so that would force `D ≤ W`, which is exactly
the containment `W ⊆ D` excluded. -/
theorem pullbackGlobalSections_subschemeι_ne_zero (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme) (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    (ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L)) s ≠ 0 := by
  have _ : IsIntegral W.subscheme := hW
  intro h0
  obtain ⟨g, hg⟩ := (Stacks.Divisors.pullbackSection_eq_zero_iff_factorsThrough_zeroScheme
    X L s W.subschemeι).mp h0
  refine h ?_
  have hsub : (W.support : Set X) ⊆ ((Stacks.Divisors.zeroScheme X L s).support : Set X) := by
    rw [← W.range_subschemeι, ← (Stacks.Divisors.zeroScheme X L s).range_subschemeι]
    rintro x ⟨w, rfl⟩
    exact ⟨g.base w, congrArg (fun q : W.subscheme ⟶ X ↦ q.base w) hg⟩
  have hle : Stacks.Divisors.zeroScheme X L s ≤
      Scheme.IdealSheafData.vanishingIdeal W.support :=
    Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp (SetLike.coe_subset_coe.mp hsub)
  rwa [← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme W W.support rfl] at hle

/-! ### The component comparison -/

/-- Pushing the cycle of the intersection `B ∩ A`, formed inside `A`, forward along `A ⟶ X`
gives the cycle of the closed subscheme `A ⊔ B` of `X`. -/
private theorem properPushforward_cycleAssociatedToClosedSubscheme_comap (A B : X.IdealSheafData) :
    properPushforward C (A.subschemeι ≫ p) p A.subschemeι rfl k
        (cycleAssociatedToClosedSubscheme C (A.subschemeι ≫ p)
          (B.comap A.subschemeι).subschemeι k) =
      cycleAssociatedToClosedSubscheme C p (A ⊔ B).subschemeι k := by
  obtain ⟨e, he⟩ := Stacks.ChernCap42.exists_iso_comap_sup A B A.subschemeι (Iso.refl _) (by simp)
  rw [properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
    (A.subschemeι ≫ p) p A.subschemeι rfl (B.comap A.subschemeι).subschemeι k,
    cycleAssociatedToClosedSubscheme_eq_of_iso C p _ (A ⊔ B).subschemeι e he k]

/-- **Stacks 02T9 on a single integral component.** For an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` there is a `k`-cycle `c` on `W` such that

* pushing the Gysin component cycle of `W` from the zero scheme `D = Z(s)` on to `X` is the
  pushforward of `c` along `W ⟶ X`, and
* `c` is rationally equivalent on `W` to the cycle the first Chern class component rule of `L`
  attaches to `W`.

In the contained case `W ⊆ D` the cycle `c` is the chosen representative of `c₁(L|_W) ∩ [W]`, and
the second item is the identity `Quotient.out ∘ mk = id` up to rational equivalence. In the
uncontained case it is the fundamental cycle of the scheme-theoretic intersection `D ∩ W`, formed
inside `W`; the first item then says that forming it inside `D` instead gives the same closed
subscheme of `X`, and the second is Stacks 02SK on `W` — the component rule chose the divisor
cycle of some nonzero meromorphic section of `L|_W`, and the ratio of that section with the
restriction `s|_W` is the rational function witnessing the equivalence. -/
theorem exists_properPushforward_gysinComponentCycle_eq (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    ∃ c : CycleGroup C (W.subschemeι ≫ p) k,
      properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (gysinComponentCycle C p k L s (firstChernComponentClass C p k L) W hW hDim) =
        properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k c ∧
      RationallyEquivalent C (W.subschemeι ≫ p) k c
        (firstChernComponentCycleRule C p k L W hW hDim) := by
  by_cases h : Stacks.Divisors.zeroScheme X L s ≤ W
  · refine ⟨Quotient.out (firstChernComponentClass C p k L W hW hDim), ?_,
      QuotientAddGroup.eq_iff_sub_mem.mp
        ((Quotient.out_eq _).trans (firstChernComponentClass_eq_mk C p k L W hW hDim))⟩
    rw [gysinComponentCycle_of_le C p k L s (firstChernComponentClass C p k L) W hW hDim h,
      properPushforward_properPushforward C (W.subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Scheme.IdealSheafData.inclusion h) (Stacks.Divisors.zeroScheme X L s).subschemeι
        (by simp) rfl k]
    exact properPushforward_hom_congr C (W.subschemeι ≫ p) p
      (Scheme.IdealSheafData.inclusion_subschemeι h) _ rfl k _
  · have _ : IsIntegral W.subscheme := hW
    have _ : IsLocallyNoetherian W.subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
    refine ⟨cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ p)
      ((Stacks.Divisors.zeroScheme X L s).comap W.subschemeι).subschemeι k, ?_, ?_⟩
    · rw [gysinComponentCycle_of_not_le C p k L s (firstChernComponentClass C p k L) W hW hDim h,
        properPushforward_cycleAssociatedToClosedSubscheme_comap C p k _ W,
        properPushforward_cycleAssociatedToClosedSubscheme_comap C p k W _, sup_comm]
    · obtain ⟨f, hf, heq⟩ := Stacks.ChernCap42.exists_firstChernComponentCycleRule_coe_eq C p k L
        W hDim ((ConcreteCategory.hom (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L)) s)
        (pullbackGlobalSections_subschemeι_ne_zero L s W hW h)
      rw [Stacks.Divisors.zeroScheme_pullback W.subschemeι L s] at heq
      have hba : IsRationallyEquivalentToZero C (W.subschemeι ≫ p) k
          (firstChernComponentCycleRule C p k L W hW hDim -
            cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ p)
              ((Stacks.Divisors.zeroScheme X L s).comap W.subschemeι).subschemeι k) := by
        refine isRationallyEquivalentToZero_of_eq_principalCycle C (W.subschemeι ≫ p) hDim hf _ ?_
        change (firstChernComponentCycleRule C p k L W hW hDim : AlgebraicCycle W.subscheme ℤ) -
          (cycleAssociatedToClosedSubscheme C (W.subschemeι ≫ p)
            ((Stacks.Divisors.zeroScheme X L s).comap W.subschemeι).subschemeι k :
              AlgebraicCycle W.subscheme ℤ) = _
        rw [heq]
        abel
      have hneg := (rationalEquivalences C (W.subschemeι ≫ p) k).neg_mem hba
      rwa [neg_sub] at hneg

/-! ### Stacks 02T9 -/

/-- **Stacks 02T9.** Pushing the Gysin class of the zero scheme `i : D = Z(s) ⟶ X` forward to `X`
is capping with the first Chern class of `L`: `i_* i^* α = c₁(L) ∩ α` in `A_k(X)` for every
`α ∈ Z_{k+1}(X)`.

The vanishing of Stacks 02S2 that `Stacks.Chow.properChowPushforward` requires is supplied, not
assumed, the zero scheme being a closed subscheme of `X`. -/
@[stacks 02T9]
theorem properChowPushforward_gysinHomomorphismOfInvertible (α : CycleGroup C p (k + 1)) :
    properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        (properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
          (Stacks.Divisors.zeroScheme X L s).subschemeι C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p rfl k)
        (gysinHomomorphismOfInvertible C p k L s α) =
      firstChernClassCapOfInvertible C p k L α := by
  classical
  -- the canonical presentation of `α` by the integral components through the points of its support
  have hW : ∀ i : cycleSupportIndex α, IsIntegral (integralComponentAt i.1).subscheme :=
    fun i ↦ isIntegral_integralComponentAt i.1
  have hDimW : ∀ i : cycleSupportIndex α,
      schemeDeltaDimension C ((integralComponentAt i.1).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) :=
    fun i ↦ schemeDeltaDimension_cycleSupportIndex α i
  have hLocal : LocallyFinite fun i : cycleSupportIndex α ↦
      (((integralComponentAt i.1).support : Set X)) :=
    locallyFinite_support_integralComponentAt α
  -- the component comparison, chosen once for each component
  choose c hc₁ hc₂ using fun i : cycleSupportIndex α ↦
    exists_properPushforward_gysinComponentCycle_eq C p k L s (integralComponentAt i.1) (hW i)
      (hDimW i)
  -- the point-indexed Gysin component cycle is the component cycle of the component
  have hAt : ∀ i : cycleSupportIndex α,
      gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) i.1 =
        gysinComponentCycle C p k L s (firstChernComponentClass C p k L)
          (integralComponentAt i.1) (hW i) (hDimW i) := by
    intro i
    rw [← gysinComponentCycleAt_genericPointOf C p k L s (firstChernComponentClass C p k L)
      (integralComponentAt i.1) (hW i) (hDimW i), genericPointOf_integralComponentAt]
  -- the pushed Gysin cycle, as a locally finite sum over the components of `α`
  have hLHS : ∀ y : X,
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup α)).1 y =
      ∑ᶠ z : X, α.1 z *
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) z)).1 y := by
    intro y
    have hcpt : IsCompact ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' {y}) :=
      (Stacks.Divisors.zeroScheme X L s).subschemeι.isProperMap.isCompact_preimage
        isCompact_singleton
    rw [properPushforward_apply_eq_map,
      show ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup α).1 =
        (gysinRule C p k L s (firstChernComponentClass C p k L)).toComponentRule.extendCycle
          (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous α.1 from rfl,
      ComponentRule.map_extendCycle_apply _ _ _ _ _ hcpt]
    exact finsum_congr fun _ ↦ rfl
  have key : RationallyEquivalent C p k
      (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
        ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup α))
      ((firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup α) := by
    refine rationallyEquivalent_finsum_of_closedSupports C p k
      (fun i : cycleSupportIndex α ↦ integralComponentAt i.1) hLocal
      (fun i ↦ α.1 i.1 • c i)
      (fun i ↦ α.1 i.1 • firstChernComponentCycleRule C p k L (integralComponentAt i.1) (hW i)
        (hDimW i)) (fun i ↦ ?_) (fun x ↦ ?_) (fun x ↦ ?_)
    · have hsmul := (rationalEquivalences C ((integralComponentAt i.1).subschemeι ≫ p) k).zsmul_mem
        (hc₂ i) (α.1 i.1)
      rw [smul_sub] at hsmul
      exact hsmul
    · -- the left hand side, reindexed over the components of `α`
      rw [hLHS x,
        ← finsum_subtype_eq_finsum_of_eq_zero (fun z : X ↦ α.1 z ≠ 0)
          (fun z ↦ α.1 z *
            (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
              (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
              (gysinComponentCycleAt C p k L s (firstChernComponentClass C p k L) z)).1 x)
          fun z hz ↦ by rw [not_not.mp hz, zero_mul]]
      refine finsum_congr fun i ↦ ?_
      rw [hAt i, hc₁ i, properPushforward_zsmul, zsmul_cycle_apply]
    · -- the right hand side, on the same presentation
      rw [(firstChernCapRule C p k
        (firstChernComponentCycleRule C p k L)).extendCycleGroup_apply_of_presentation
          (fun i : cycleSupportIndex α ↦ integralComponentAt i.1) hW hDimW hLocal
          (fun i ↦ α.1 i.1) α (cycle_eq_finsum_primeCycles α) x]
      refine finsum_congr fun i ↦ ?_
      rw [properPushforward_zsmul, zsmul_cycle_apply]
      rfl
  change properChowPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _
      (QuotientAddGroup.mk' (rationalEquivalences C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)
        ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup α)) =
    QuotientAddGroup.mk' (rationalEquivalences C p k)
      ((firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup α)
  rw [properChowPushforward_mk]
  exact QuotientAddGroup.eq_iff_sub_mem.mpr key

/-- **Stacks 02T9, the "in particular" clause.** When the zero scheme `D = Z(s)` is an effective
Cartier divisor, intersection with `D` is capping with the first Chern class of `L`:
`D · α = c₁(L) ∩ α` in `A_k(X)`.

Intersection with an effective Cartier zero scheme is by definition the Gysin map followed by
proper pushforward into `X` (`Stacks.Chow.effectiveCartierIntersectionOfInvertible_apply`), so
this is `Stacks.Chow.properChowPushforward_gysinHomomorphismOfInvertible` read through that
definition. The module `L` is canonically `𝒪_X(D)`, by
`AlgebraicGeometry.invertibleSheafIsoZeroScheme`.

No attribute is placed here: the clause of the source is about an effective Cartier divisor `D`
and the module `𝒪_X(D)`, and that form is
`Stacks.Chow.effectiveCartierIntersection_divisorSheaf_eq_firstChernClassCapOfInvertible` below.
This is the generalization it is deduced from, where `L` is only canonically isomorphic to
`𝒪_X(D)`. -/
theorem effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme X L s))
    (α : CycleGroup C p (k + 1)) :
    effectiveCartierIntersectionOfInvertible C p k L s hD α =
      firstChernClassCapOfInvertible C p k L α :=
  (effectiveCartierIntersectionOfInvertible_apply C p k L s hD α).trans
    (properChowPushforward_gysinHomomorphismOfInvertible C p k L s α)

/-- The zero scheme of the canonical section of `𝒪_X(D)` is an effective Cartier divisor when
`D` is: it *is* `D`, by Stacks 01X0. -/
theorem isEffectiveCartierDivisor_zeroScheme_divisorSheaf {X : Scheme.{u}}
    (D : X.IdealSheafData) [hD : Stacks.Divisors.IsEffectiveCartierDivisor D] :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)) := by
  rw [show Stacks.Divisors.zeroScheme X (Stacks.Divisors.divisorSheaf D)
      (Stacks.Divisors.divisorSheafGlobalSection D) = D from
    Stacks.Divisors.zeroScheme_canonicalSection D]
  exact hD

/-- **Stacks 02T9, the "in particular" clause for a given effective Cartier divisor.** For an
effective Cartier divisor `D` on `X`, intersection with `D` — taken through the canonical section
`1_D` of `𝒪_X(D)`, whose zero scheme is `D` — is capping with `c₁(𝒪_X(D))`.

The effective Cartier hypothesis of `Stacks.Chow.effectiveCartierIntersection` is carried but
unused by that construction, so transporting it along `Z(1_D) = D` (Stacks 01X0) costs nothing. -/
@[stacks 02T9 "in particular"]
theorem effectiveCartierIntersection_divisorSheaf_eq_firstChernClassCapOfInvertible
    (D : X.IdealSheafData) [hD : Stacks.Divisors.IsEffectiveCartierDivisor D]
    (α : CycleGroup C p (k + 1)) :
    effectiveCartierIntersectionOfInvertible C p k (Stacks.Divisors.divisorSheaf D)
        (Stacks.Divisors.divisorSheafGlobalSection D)
        (isEffectiveCartierDivisor_zeroScheme_divisorSheaf D) α =
      firstChernClassCapOfInvertible C p k (Stacks.Divisors.divisorSheaf D) α :=
  effectiveCartierIntersectionOfInvertible_eq_firstChernClassCapOfInvertible C p k
    (Stacks.Divisors.divisorSheaf D) (Stacks.Divisors.divisorSheafGlobalSection D) _ α

end Stacks.Chow

end
