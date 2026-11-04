module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ClassRule
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# Gysin pullback and the first Chern class of an invertible module

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℒ` be an invertible `𝒪_X`-module with a global section
`s ∈ Γ(X, ℒ)` and zero scheme `i : D = Z(s) ⟶ X`, and let `𝒩` be a second invertible
`𝒪_X`-module. Stacks 0B72 is the compatibility

  `i^*(c₁(𝒩) ∩ α) = c₁(i^*𝒩) ∩ i^*α`  in  `A_k(D)`,  for `α ∈ A_{k+2}(X)`,

and the source proves it "with exactly the same proof as in Lemma 42.30.2", from Stacks 02SU,
02TJ and 02TM: present `α` over the integral closed subschemes it is supported on, reduce to the
fundamental cycle of a single one of them, and on that one invoke Stacks 02TM.

`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap` proves the identity with **four** component
rules of Stacks 02SO as free parameters, so none of its statements is about the modules `ℒ` and
`𝒩` at all, and it carries the integral-component case as a hypothesis **at the level of
cycles**. This file removes both defects. All four operations are taken at the component rules of
`ℒ` and of `𝒩`, so that every statement below is a function of `ℒ`, `s` and `𝒩`; and the
integral-component input is carried at the level of **classes**, which is what Stacks 02TM
asserts, the passage from there to every class being proved rather than assumed.

## Main definitions

* `Stacks.Chow.GysinChernCapRationallyEquivalentOnComponents` — **Stacks 02TM** for `ℒ`, `s` and
  `𝒩` on the integral closed subschemes of `X` of delta-dimension `k + 2`: on each such `W` the
  two component cycles agree in the Chow group of `D ∩ W`, in the form of a rational equivalence
  carried by `D ∩ W`.

## Main results

* `Stacks.Chow.GysinChernCap.extendCycleGroup_eq_finsum_cycle`,
  `Stacks.Chow.GysinChernCap.extendCycleGroup_comp_eq_finsum` — a rule, and a composite of two
  rules, on integral components, read on the canonical presentation of a cycle by the integral
  closed subschemes attached to the points of its support.
* `Stacks.Chow.GysinChernCap.isRationallyEquivalentToZero_sub_of_finsum` — a difference of two
  locally finite sums carried by a locally finite family of closed subschemes is rationally
  equivalent to zero as soon as the summands differ by pushforwards of rational equivalences.
* `Stacks.Chow.isRationallyEquivalentToZero_gysinChernCap_sub` — the passage from the integral
  components to every cycle.

## Implementation notes

### Degrees

The source writes the input degree as `k` and the output degree as `k - 2`. Here the output
degree is `k` and the input degree is `k + 1 + 1`, so that the two successive degree-lowering
operations compose without casts; this is the convention of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`.

### Why Stacks 02TM is carried at the level of classes

`Stacks.Chow.GysinCommutesWithChernCapOnComponents` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap` asks for the two component *cycles* on each
integral component to be equal. At the component rules of two invertible modules that is in
general **false**, for the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible`: each rule chooses a nonzero
meromorphic section on each component independently, and the key formula of Stacks 0AYC exhibits
the difference of the resulting cycles as a sum of principal divisors, not as zero. Instantiating
the cycle-level statement at the rules of `ℒ` and `𝒩` would therefore carry a false hypothesis.
So the input here is the class-level statement — a rational equivalence on `D ∩ W` — and the
extension to every cycle is the content of this file.

That extension is not formal. A cycle is only a *locally* finite sum of the fundamental cycles of
the integral closed subschemes attached to the points of its support
(`Stacks.Chow.cycle_eq_finsum_primeCycles`), so both composites are double locally finite sums
over that family; each of the four rules keeps the family as a carrier, on `X` or on `D`
according to where it lands; the carriers downstairs are the intersections `D ∩ W`, which form a
locally finite family on `D` because they are the preimages under `i` of a locally finite family
on `X`; and a locally finite sum of pushforwards along closed immersions of cycles rationally
equivalent to zero is rationally equivalent to zero, which is
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion`.

### Why the hypothesis is Stacks 02TM and not Stacks 0B72 restated

On an integral closed subscheme `W ⊆ X` of delta-dimension `n = k + 2` not contained in `D` the
cap product rule of `𝒩` is the divisor `div_{𝒩|_W}(t)` of the meromorphic section it chooses on
`W`, and the Gysin rule of `(ℒ, s)` sends `[W]` to `[D ∩ W]`. So on `W` the identity reads
`i^* div_{𝒩|_W}(t) = c₁(𝒩|_{D ∩ W}) ∩ [D ∩ W]_{n-1}`, which is **verbatim the statement of
Stacks 02TM** — Lemma 42.30.1, whose proof is a direct application of the key formula of Stacks
0AYC and does not use Stacks 0B72. That is the shape in which the source consumes it, and it is
the same arrangement as `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm`, which carries
Stacks 02TH on the integral components in order to prove Stacks 02TJ on every class.

### The invertibility of `𝒩|_D`

Stacks 0B8L — that the pullback of an invertible module along a morphism of schemes is
invertible — is in this repository as
`Stacks.Chow.isInvertible_presheaf_modulePullback`. It is taken here as an instance argument
rather than resolved inside each statement, so that the restriction `𝒩|_D` and its component
rule may be named in the hypotheses as well as in the conclusion.

## References

* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

namespace GysinChernCap

/-! ### Carriers for a rule on integral components -/

section Carrier

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (g : Y ⟶ X) {m : ℤ}

/-- The preimages of a locally finite family of sets under a continuous map again form a locally
finite family: a neighbourhood of `f y` meeting only finitely many members pulls back to a
neighbourhood of `y` meeting only finitely many preimages. -/
theorem locallyFinite_preimage {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    {J : Type*} {E : J → Set Z} (hE : LocallyFinite E) {f : W → Z} (hf : Continuous f) :
    LocallyFinite fun j ↦ f ⁻¹' E j := by
  intro w
  obtain ⟨t, ht, hfin⟩ := hE (f w)
  refine ⟨f ⁻¹' t, hf.continuousAt.preimage_mem_nhds ht, hfin.subset ?_⟩
  rintro j ⟨z, hz, hzt⟩
  exact ⟨f z, hz, hzt⟩

/-- **A rule on integral components keeps a carrier.** A cycle supported on a closed set `A` of
`X` is sent to a cycle supported over `A`: only the points of the support of the input
contribute, and the cycle the rule attaches to such a point lies over its closure. -/
theorem support_extendCycleGroup_subset (R : IntegralComponentRule C p q g m) {A : Set X}
    (hA : IsClosed A) (β : CycleGroup C p (m + 1)) (hβ : Function.support β.1 ⊆ A) :
    Function.support (R.extendCycleGroup β).1 ⊆ g.base ⁻¹' A := by
  intro y hy
  have hy' : R.toComponentRule.extend g.continuous β.1 y ≠ 0 := hy
  by_cases hall : ∀ x : X, β.1 x * R.toComponentRule.cycle x y = 0
  · exact absurd (finsum_eq_zero_of_forall_eq_zero hall) hy'
  · obtain ⟨x, hx⟩ := not_forall.1 hall
    have hxA : x ∈ A := hβ (left_ne_zero_of_mul hx)
    have hclos : g.base y ∈ closure ({x} : Set X) :=
      R.toComponentRule.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hx)
    exact hA.closure_subset (closure_mono (Set.singleton_subset_iff.2 hxA) hclos)

/-- An integer multiple of the cycle a rule attaches to an integral closed subscheme is supported
over that subscheme. -/
theorem support_zsmul_cycle_subset (R : IntegralComponentRule C p q g m)
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((m + 1 : ℤ) : EInt)) (n : ℤ) :
    Function.support (n • R.cycle W hW hDim).1 ⊆ g.base ⁻¹' (W.support : Set X) := by
  refine Set.Subset.trans ?_ (R.support_subset W hW hDim)
  intro y hy
  have hy' : (n • R.cycle W hW hDim).1 y ≠ 0 := hy
  show (R.cycle W hW hDim).1 y ≠ 0
  intro h
  exact hy' (by simp [h])

/-- **The component formula on the canonical presentation.** The extension of a rule on integral
components is, coefficientwise, the locally finite sum over the points of the support of the
cycle of the multiples of the cycles the rule attaches to the corresponding components. -/
theorem extendCycleGroup_eq_finsum_cycle (R : IntegralComponentRule C p q g m)
    (β : CycleGroup C p (m + 1)) (y : Y) :
    (R.extendCycleGroup β).1 y = ∑ᶠ i : cycleSupportIndex β,
      (β.1 i.1 • R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex β i)).1 y := by
  have hpres : ∀ x : X, β.1 x = ∑ᶠ i : cycleSupportIndex β,
      (β.1 i.1 • cycleAssociatedToClosedSubscheme C p
        (integralComponentAt i.1).subschemeι (m + 1)).1 x := by
    intro x
    rw [cycle_eq_finsum_primeCycles β x]
    exact finsum_congr fun i ↦ by simp
  rw [R.extendCycleGroup_finsum
    (fun i : cycleSupportIndex β ↦ β.1 i.1 • cycleAssociatedToClosedSubscheme C p
      (integralComponentAt i.1).subschemeι (m + 1))
    (fun i : cycleSupportIndex β ↦ ((integralComponentAt i.1).support : Set X))
    (locallyFinite_support_integralComponentAt β)
    (support_zsmul_primeCycle_subset C p β) β hpres y]
  refine finsum_congr fun i ↦ ?_
  have hstep : R.extendCycleGroup (β.1 i.1 • cycleAssociatedToClosedSubscheme C p
      (integralComponentAt i.1).subschemeι (m + 1)) =
      β.1 i.1 • R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex β i) := by
    rw [map_zsmul, R.extendCycleGroup_cycleAssociatedToClosedSubscheme]
  rw [hstep]

end Carrier

/-! ### The composite of two rules on the canonical presentation -/

section Two

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (q : Y ⟶ C.S) [LocallyOfFiniteType q] (r : Z ⟶ C.S) [LocallyOfFiniteType r]
  (g : Y ⟶ X) (h : Z ⟶ Y) {m : ℤ}

/-- **The composite of two coefficientwise extensions on the canonical presentation.** The
composite of the extensions of two rules on integral components is, coefficientwise, the locally
finite sum over the points of the support of the cycle of the values of the outer rule on the
multiples of the cycles the inner rule attaches to the components.

The carriers downstairs are the preimages under `g` of the carriers upstairs, and those again
form a locally finite family. -/
theorem extendCycleGroup_comp_eq_finsum (Rin : IntegralComponentRule C p q g (m + 1))
    (Rout : IntegralComponentRule C q r h m) (β : CycleGroup C p (m + 1 + 1)) (z : Z) :
    (Rout.extendCycleGroup (Rin.extendCycleGroup β)).1 z =
      ∑ᶠ i : cycleSupportIndex β,
        (Rout.extendCycleGroup (β.1 i.1 • Rin.cycle (integralComponentAt i.1)
          (isIntegral_integralComponentAt i.1)
          (schemeDeltaDimension_cycleSupportIndex β i))).1 z :=
  Rout.extendCycleGroup_finsum _
    (fun i : cycleSupportIndex β ↦ g.base ⁻¹' ((integralComponentAt i.1).support : Set X))
    (locallyFinite_preimage (locallyFinite_support_integralComponentAt β) g.continuous)
    (fun _i ↦ support_zsmul_cycle_subset C p q g Rin _ _ _ _)
    (Rin.extendCycleGroup β)
    (extendCycleGroup_eq_finsum_cycle C p q g Rin β) z

end Two

/-! ### Assembling a rational equivalence from a locally finite family -/

section Assembly

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (k : ℤ)

/-- **A difference of two locally finite sums with a common carrier family.** If two `k`-cycles
are coefficientwise the locally finite sums of two families `u` and `v` carried by a locally
finite family of closed subschemes `W`, and if `u j - v j` is the pushforward from `W j` of a
cycle rationally equivalent to zero, then the difference of the two cycles is rationally
equivalent to zero.

At a point only finitely many members of each family contribute, because each is supported on its
carrier, so the two sums may be subtracted termwise; the conclusion is then
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion`. -/
theorem isRationallyEquivalentToZero_sub_of_finsum {J : Type u} (W : J → Y.IdealSheafData)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set Y)) (A B : CycleGroup C q k)
    (u v : J → CycleGroup C q k)
    (hu : ∀ j, Function.support (u j).1 ⊆ ((W j).support : Set Y))
    (hv : ∀ j, Function.support (v j).1 ⊆ ((W j).support : Set Y))
    (hA : ∀ y : Y, A.1 y = ∑ᶠ j : J, (u j).1 y)
    (hB : ∀ y : Y, B.1 y = ∑ᶠ j : J, (v j).1 y)
    (a : ∀ j, CycleGroup C ((W j).subschemeι ≫ q) k)
    (ha : ∀ j, IsRationallyEquivalentToZero C ((W j).subschemeι ≫ q) k (a j))
    (hpush : ∀ j, properPushforward C ((W j).subschemeι ≫ q) q (W j).subschemeι rfl k (a j) =
      u j - v j) :
    IsRationallyEquivalentToZero C q k (A - B) := by
  have hfinite : LocallyFinite fun j : J ↦ Set.range ((W j).subschemeι) := by
    refine hLocal.subset fun j ↦ ?_
    rw [(W j).range_subschemeι]
  refine rationallyEquivalentToZero_finsum_of_isClosedImmersion C q k
    (fun j ↦ (W j).subschemeι) hfinite a ha _ fun y ↦ ?_
  have hfin : ∀ w : J → CycleGroup C q k,
      (∀ j, Function.support (w j).1 ⊆ ((W j).support : Set Y)) →
      Function.HasFiniteSupport fun j : J ↦ (w j).1 y := fun w hw ↦
    (hLocal.point_finite y).subset fun j hj ↦ hw j (by exact hj)
  have hpt : (A - B).1 y = A.1 y - B.1 y := by simp
  rw [hpt, hA y, hB y, ← finsum_sub_distrib (hfin u hu) (hfin v hv)]
  exact finsum_congr fun j ↦ by rw [hpush j]; simp

end Assembly

end GysinChernCap

/-! ### Stacks 02TM as a hypothesis -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  [AlgebraicGeometry.SheafOfModules.IsInvertible
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N)]

/-- **Stacks 02TM for `ℒ`, `s` and `𝒩` on the integral components of `X`.** On every integral
closed subscheme `W ⊆ X` of delta-dimension `k + 2`, the Gysin cycle of the cap product component
cycle of `𝒩` on `W` and the cap product cycle of `𝒩|_D` on the Gysin component cycle of `W`
agree in the Chow group of the intersection `D ∩ W`: their difference is the pushforward from
`D ∩ W` of a cycle rationally equivalent to zero.

For `W ⊄ D` this reads `i^* div_{𝒩|_W}(t) = c₁(𝒩|_{D ∩ W}) ∩ [D ∩ W]_{n-1}` with `n = k + 2`,
which is the statement of Stacks 02TM; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapInvertible`. It is an equality of *classes*,
as the tag asserts, witnessed by a rational equivalence carried by `D ∩ W` — the carrier is what
makes the locally infinite sum over the components of a general cycle assemble. -/
def GysinChernCapRationallyEquivalentOnComponents : Prop :=
  ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
    ∃ a : CycleGroup C
      ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      IsRationallyEquivalentToZero C
        ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k a ∧
      (gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
          (firstChernComponentCycle C p (k + 1)
            (firstChernComponentCycleRule C p (k + 1) N) W hW hDim) -
        (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
          (firstChernComponentCycleRule C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
            ((Scheme.Modules.pullback
              (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N))).extendCycleGroup
          (gysinComponentCycle C p (k + 1) L s
            (firstChernComponentClass C p (k + 1) L) W hW hDim) =
        properPushforward C
          ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι rfl k a

/-! ### From the integral components to every cycle -/

/-- **The passage from the integral components to every cycle.** Granted Stacks 02TM on the
integral components, the difference of the two composites of Stacks 0B72 is rationally equivalent
to zero on every `(k+2)`-cycle.

Both composites are read on the canonical presentation of the cycle by the integral closed
subschemes attached to the points of its support, which is
`Stacks.Chow.GysinChernCap.extendCycleGroup_comp_eq_finsum`; the carriers on `D` are the
intersections `D ∩ W`, a locally finite family because they are the preimages under `i` of a
locally finite family on `X`; and the assembly is
`Stacks.Chow.GysinChernCap.isRationallyEquivalentToZero_sub_of_finsum`. -/
theorem isRationallyEquivalentToZero_gysinChernCap_sub
    (hcomp : GysinChernCapRationallyEquivalentOnComponents C p k L s N)
    (β : CycleGroup C p (k + 1 + 1)) :
    IsRationallyEquivalentToZero C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      ((gysinRule C p k L s (firstChernComponentClass C p k L)).extendCycleGroup
          ((firstChernCapRule C p (k + 1)
            (firstChernComponentCycleRule C p (k + 1) N)).extendCycleGroup β) -
        (firstChernCapRule C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
          (firstChernComponentCycleRule C
            ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
            ((Scheme.Modules.pullback
              (Stacks.Divisors.zeroScheme X L s).subschemeι).obj N))).extendCycleGroup
          ((gysinRule C p (k + 1) L s
            (firstChernComponentClass C p (k + 1) L)).extendCycleGroup β)) := by
  classical
  set D := Stacks.Divisors.zeroScheme X L s with hD
  set RG := gysinRule C p k L s (firstChernComponentClass C p k L) with hRG
  set RGup := gysinRule C p (k + 1) L s (firstChernComponentClass C p (k + 1) L) with hRGup
  set RCapX := firstChernCapRule C p (k + 1) (firstChernComponentCycleRule C p (k + 1) N)
    with hRCapX
  set RCapD := firstChernCapRule C (D.subschemeι ≫ p) k
    (firstChernComponentCycleRule C (D.subschemeι ≫ p) k
      ((Scheme.Modules.pullback D.subschemeι).obj N)) with hRCapD
  choose a ha hapush using fun i : cycleSupportIndex β ↦
    hcomp (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
      (schemeDeltaDimension_cycleSupportIndex β i)
  -- the carriers on `D` are the intersections `D ∩ W`, and they are a locally finite family
  have hcar : ∀ i : cycleSupportIndex β,
      (((integralComponentAt i.1).comap D.subschemeι).support : Set D.subscheme) =
        D.subschemeι.base ⁻¹' ((integralComponentAt i.1).support : Set X) := by
    intro i
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hLocal : LocallyFinite fun i : cycleSupportIndex β ↦
      (((integralComponentAt i.1).comap D.subschemeι).support : Set D.subscheme) := by
    simp only [hcar]
    exact GysinChernCap.locallyFinite_preimage
      (locallyFinite_support_integralComponentAt β) D.subschemeι.continuous
  refine GysinChernCap.isRationallyEquivalentToZero_sub_of_finsum C (D.subschemeι ≫ p) k
    (fun i : cycleSupportIndex β ↦ (integralComponentAt i.1).comap D.subschemeι) hLocal _ _
    (fun i ↦ RG.extendCycleGroup (β.1 i.1 • RCapX.cycle (integralComponentAt i.1)
      (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i)))
    (fun i ↦ RCapD.extendCycleGroup (β.1 i.1 • RGup.cycle (integralComponentAt i.1)
      (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i)))
    (fun i ↦ ?_) (fun i ↦ ?_)
    (GysinChernCap.extendCycleGroup_comp_eq_finsum C p p (D.subschemeι ≫ p) (𝟙 X)
      D.subschemeι RCapX RG β)
    (GysinChernCap.extendCycleGroup_comp_eq_finsum C p (D.subschemeι ≫ p) (D.subschemeι ≫ p)
      D.subschemeι (𝟙 D.subscheme) RGup RCapD β)
    (fun i ↦ β.1 i.1 • a i)
    (fun i ↦ (rationalEquivalences C
      (((integralComponentAt i.1).comap D.subschemeι).subschemeι ≫ D.subschemeι ≫ p) k).zsmul_mem
      (ha i) _) fun i ↦ ?_
  · -- the left summand is carried by `D ∩ W`
    rw [hcar i]
    exact GysinChernCap.support_extendCycleGroup_subset C p (D.subschemeι ≫ p) D.subschemeι RG
      (integralComponentAt i.1).support.isClosed' _
      (GysinChernCap.support_zsmul_cycle_subset C p p (𝟙 X) RCapX _ _ _ _)
  · -- the right summand is carried by `D ∩ W`
    rw [hcar i]
    exact GysinChernCap.support_extendCycleGroup_subset C (D.subschemeι ≫ p)
      (D.subschemeι ≫ p) (𝟙 D.subscheme) RCapD
      ((integralComponentAt i.1).support.isClosed'.preimage D.subschemeι.continuous) _
      (GysinChernCap.support_zsmul_cycle_subset C p (D.subschemeι ≫ p) D.subschemeι RGup
        _ _ _ _)
  · -- the pushforward of the rational equivalence is the difference, by Stacks 02TM on `W`
    rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply, map_zsmul,
      map_zsmul, ← smul_sub]
    exact congrArg (fun z : CycleGroup C (D.subschemeι ≫ p) k ↦ β.1 i.1 • z) (hapush i).symm

end Stacks.Chow

end
