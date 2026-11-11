module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativity
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapRationalEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction

/-!
# Commutativity of the first Chern class cap products of two invertible modules

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `ℒ` and `𝒩` be invertible `𝒪_X`-modules. Stacks 02TJ is
the commutativity

  `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α`  in  `A_k(X)`,  for `α ∈ A_{k+2}(X)`,

and the source proves it by presenting `α` as a locally finite sum `∑_j m_j [Z_j]` over integral
closed subschemes of delta-dimension `k + 2`, pushing both iterated cap products through
`⨿_j Z_j ⟶ X` by two applications of Stacks 02SU, and invoking the integral case, which is
Stacks 02TH.

This file proves Stacks 02TJ with **two inputs**: Stacks 02TI, in the single reduced form
`Stacks.Chow.FirstChernCapKillsPrincipalDivisor` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapRationalEquivalenceReduction`, and Stacks 02TH
itself,
as the hypothesis `Stacks.Chow.FirstChernCapCommutesOnIntegralComponents`. The two operations
being composed exist on Chow groups only granted the first, and the identity comes from the
second.

## Main definitions

* `Stacks.Chow.FirstChernCapCommutesOnIntegralComponents` — **Stacks 02TH** for the restrictions
  of `ℒ` and `𝒩` to the integral closed subschemes of `X` of delta-dimension `k + 2`: an equality
  of *classes* in `A_k(W)`, which is what the tag asserts.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_sub_of_finsum` — a difference of two locally finite
  sums carried by a locally finite family of closed subschemes is rationally equivalent to zero as
  soon as the summands differ by pushforwards of rational equivalences.
* `Stacks.Chow.isRationallyEquivalentToZero_sub_extendCycleGroup_of_components` — the passage from
  the integral components to every cycle, for two iterated extensions of rules on integral
  components.
* `Stacks.Chow.exists_isRationallyEquivalentToZero_comm_component` — the component step: granted
  Stacks 02TH on `W`, the difference of the two iterated cap product cycles attached to `W` is the
  pushforward from `W` of a cycle rationally equivalent to zero.
* `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm` — Stacks 02TJ out of its two inputs.
  Both inputs are theorems of this repository, and Stacks 02TJ itself is
  `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm_unconditional` of
  `StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.FirstChernCommOfInvertible`.

## Implementation notes

### Why Stacks 02TH is carried at the level of classes

`Stacks.Chow.FirstChernCapCommutesOnComponents` of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativity` asks for the two iterated cap product
*cycles* on each integral component to be equal. That is strictly stronger than Stacks 02TH, whose
conclusion is an equality of classes, and for the component rules of two invertible modules it is
in general false: each rule chooses a meromorphic section on each component independently, so the
two cycles agree only up to rational equivalence. The hypothesis here is therefore the class-level
statement, and the extension to all cycles is proved rather than assumed.

That extension is the content of this file. The difference of the two iterated cap product cycles
of a `(k+2)`-cycle is a locally finite sum, over the points carrying a nonzero coefficient, of the
differences attached to the integral components; and a locally finite sum of pushforwards of
cycles rationally equivalent to zero along closed immersions is rationally equivalent to zero,
which is `Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion`. The carriers that
make the family locally finite are the components themselves
(`Stacks.Chow.locallyFinite_support_integralComponentAt`), and the presentation of the cycle over
them is `Stacks.Chow.cycle_eq_finsum_primeCycles`. This replaces the disjoint-union reduction of
the source, which would need infinite coproducts of schemes.

### The restriction to a component, and the transported rule

Pushing a cap product through the closed immersion `i_W : W ⟶ X` uses Stacks 02SU at the level of
cycles, which needs the rules upstairs and downstairs to be compatible coefficientwise. The rule
of `ℒ|_W` is not compatible with the rule of `ℒ`, but `Stacks.Chow.pullbackComponentRule` is, and
agrees with the rule of `ℒ|_W` in the Chow group of every component; the two may therefore be
exchanged inside a class, by `Stacks.Chow.firstChernClassCap_congr`. This is the same device as in
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapRationalEquivalenceReduction`.

### The two inputs are independent

Deriving Stacks 02TI from Stacks 02TH is the source's argument — take the second module to be
`𝒪_X` with its meromorphic section a rational function `f`, and use the second half of Stacks
02SP — but it needs Stacks 02TH for an *arbitrary* nonzero meromorphic section of `𝒪_X`, whereas
the component rule of `𝒪_X` carries only the section it chooses, and comparing the two divisor
cycles is itself an appeal to Stacks 02TI. So the vanishing is carried separately, in the one
reduced form it has here.

## References

* [Stacks Project, Tag 02TJ](https://stacks.math.columbia.edu/tag/02TJ)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Carriers and presentations -/

section Carrier

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {m : ℤ}

/-- The coefficientwise extension of a rule on integral components keeps a carrier: a cycle
supported on a closed subscheme `W` is sent to a cycle supported on `W`. Only the points of the
support of the input contribute, and the cycle the rule attaches to such a point is supported on
its closure, which lies in `W`. -/
theorem support_extendCycleGroup_subset_of_support_subset
    (R : IntegralComponentRule C p p (𝟙 X) m) (W : X.IdealSheafData) (D : CycleGroup C p (m + 1))
    (hD : Function.support D.1 ⊆ (W.support : Set X)) :
    Function.support (R.extendCycleGroup D).1 ⊆ (W.support : Set X) := by
  intro y hy
  have hy' : R.toComponentRule.extend (𝟙 X : X ⟶ X).continuous D.1 y ≠ 0 := hy
  by_cases hall : ∀ x : X, D.1 x * R.toComponentRule.cycle x y = 0
  · exact absurd (finsum_eq_zero_of_forall_eq_zero hall) hy'
  · obtain ⟨x, hx⟩ := not_forall.1 hall
    have hxW : x ∈ (W.support : Set X) := hD (left_ne_zero_of_mul hx)
    have hclos : y ∈ closure ({x} : Set X) :=
      R.toComponentRule.mem_closure_of_apply_ne_zero x y (right_ne_zero_of_mul hx)
    exact W.support.isClosed'.closure_subset
      (closure_mono (Set.singleton_subset_iff.2 hxW) hclos)

/-- The extension of a rule on integral components over an integer multiple of the fundamental
cycle of an integral closed subscheme is that multiple of the cycle the rule attaches to it. -/
theorem extendCycleGroup_zsmul_cycleAssociatedToClosedSubscheme
    (R : IntegralComponentRule C p p (𝟙 X) m) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((m + 1 : ℤ) : EInt)) (n : ℤ) :
    R.extendCycleGroup (n • cycleAssociatedToClosedSubscheme C p W.subschemeι (m + 1)) =
      n • R.cycle W hW hDim := by
  rw [map_zsmul, R.extendCycleGroup_cycleAssociatedToClosedSubscheme W hW hDim]

/-- The canonical presentation of a cycle, with the coefficients absorbed into the summands: a
`m`-cycle is the locally finite sum of the integer multiples of the fundamental cycles of the
integral closed subschemes attached to the points of its support. -/
theorem cycle_eq_finsum_zsmul_primeCycles (β : CycleGroup C p m) (y : X) :
    β.1 y = ∑ᶠ i : cycleSupportIndex β,
      (β.1 i.1 • cycleAssociatedToClosedSubscheme C p
        (integralComponentAt i.1).subschemeι m).1 y := by
  rw [cycle_eq_finsum_primeCycles β y]
  exact finsum_congr fun i ↦ by simp

/-- **The component formula on the canonical presentation.** The extension of a rule on integral
components is, coefficientwise, the locally finite sum over the points of the support of the cycle
of the multiples of the cycles the rule attaches to the corresponding components. -/
theorem extendCycleGroup_finsum_primeCycles (R : IntegralComponentRule C p p (𝟙 X) m)
    (β : CycleGroup C p (m + 1)) (y : X) :
    (R.extendCycleGroup β).1 y = ∑ᶠ i : cycleSupportIndex β,
      (β.1 i.1 • R.cycle (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
        (schemeDeltaDimension_cycleSupportIndex β i)).1 y := by
  rw [R.extendCycleGroup_finsum
    (fun i : cycleSupportIndex β ↦ β.1 i.1 • cycleAssociatedToClosedSubscheme C p
      (integralComponentAt i.1).subschemeι (m + 1))
    (fun i : cycleSupportIndex β ↦ ((integralComponentAt i.1).support : Set X))
    (locallyFinite_support_integralComponentAt β) (support_zsmul_primeCycle_subset C p β) β
    (cycle_eq_finsum_zsmul_primeCycles C p β) y]
  exact finsum_congr fun i ↦ by
    rw [extendCycleGroup_zsmul_cycleAssociatedToClosedSubscheme C p R
      (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
      (schemeDeltaDimension_cycleSupportIndex β i) (β.1 i.1)]

/-- Each summand of the component formula is supported on the integral closed subscheme it is
attached to. -/
theorem support_zsmul_cycle_primeCycle_subset (R : IntegralComponentRule C p p (𝟙 X) m)
    (β : CycleGroup C p (m + 1)) (i : cycleSupportIndex β) :
    Function.support (β.1 i.1 • R.cycle (integralComponentAt i.1)
        (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i)).1 ⊆
      ((integralComponentAt i.1).support : Set X) := by
  rw [← extendCycleGroup_zsmul_cycleAssociatedToClosedSubscheme C p R
    (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
    (schemeDeltaDimension_cycleSupportIndex β i) (β.1 i.1)]
  exact support_extendCycleGroup_subset_of_support_subset C p R (integralComponentAt i.1) _
    (support_zsmul_primeCycle_subset C p β i)

end Carrier

/-! ### Assembling a rational equivalence from a locally finite family -/

section Assembly

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- **A difference of two locally finite sums with a common carrier family.** If two `k`-cycles
are coefficientwise the locally finite sums of two families `u` and `v` carried by a locally
finite family of closed subschemes `W`, and if `u j - v j` is the pushforward from `W j` of a
cycle rationally equivalent to zero, then the difference of the two cycles is rationally
equivalent to zero.

At a point only finitely many members of each family contribute, because each is supported on its
carrier, so the two sums may be subtracted termwise; the conclusion is then
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion`. -/
theorem isRationallyEquivalentToZero_sub_of_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (A B : CycleGroup C p k)
    (u v : J → CycleGroup C p k)
    (hu : ∀ j, Function.support (u j).1 ⊆ ((W j).support : Set X))
    (hv : ∀ j, Function.support (v j).1 ⊆ ((W j).support : Set X))
    (hA : ∀ y : X, A.1 y = ∑ᶠ j : J, (u j).1 y)
    (hB : ∀ y : X, B.1 y = ∑ᶠ j : J, (v j).1 y)
    (a : ∀ j, CycleGroup C ((W j).subschemeι ≫ p) k)
    (ha : ∀ j, IsRationallyEquivalentToZero C ((W j).subschemeι ≫ p) k (a j))
    (hpush : ∀ j, properPushforward C ((W j).subschemeι ≫ p) p (W j).subschemeι rfl k (a j) =
      u j - v j) :
    IsRationallyEquivalentToZero C p k (A - B) := by
  have hfinite : LocallyFinite fun j : J ↦ Set.range ((W j).subschemeι) := by
    refine hLocal.subset fun j ↦ ?_
    rw [(W j).range_subschemeι]
  refine rationallyEquivalentToZero_finsum_of_isClosedImmersion C p k
    (fun j ↦ (W j).subschemeι) hfinite a ha _ fun y ↦ ?_
  have hfu : Function.HasFiniteSupport fun j : J ↦ (u j).1 y :=
    (hLocal.point_finite y).subset fun j hj ↦ hu j (by exact hj)
  have hfv : Function.HasFiniteSupport fun j : J ↦ (v j).1 y :=
    (hLocal.point_finite y).subset fun j hj ↦ hv j (by exact hj)
  have hpt : (A - B).1 y = A.1 y - B.1 y := by simp
  rw [hpt, hA y, hB y, ← finsum_sub_distrib hfu hfv]
  exact finsum_congr fun j ↦ by rw [hpush j]; simp

end Assembly

/-! ### From the integral components to every cycle -/

section Extension

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (RL RN : IntegralComponentRule C p p (𝟙 X) k)
  (RL' RN' : IntegralComponentRule C p p (𝟙 X) (k + 1))

/-- The iterated extension of two rules on integral components, read on the canonical
presentation of a cycle: it is the locally finite sum, over the points of the support, of the
values on the multiples of the cycles the inner rule attaches to the components. -/
theorem extendCycleGroup_extendCycleGroup_finsum_primeCycles (β : CycleGroup C p (k + 1 + 1))
    (y : X) :
    (RL.extendCycleGroup (RN'.extendCycleGroup β)).1 y = ∑ᶠ i : cycleSupportIndex β,
      (RL.extendCycleGroup (β.1 i.1 • RN'.cycle (integralComponentAt i.1)
        (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i))).1 y :=
  RL.extendCycleGroup_finsum _
    (fun i : cycleSupportIndex β ↦ ((integralComponentAt i.1).support : Set X))
    (locallyFinite_support_integralComponentAt β) (support_zsmul_cycle_primeCycle_subset C p RN' β)
    (RN'.extendCycleGroup β) (extendCycleGroup_finsum_primeCycles C p RN' β) y

/-- **The passage from the integral components to every cycle.** If for every integral closed
subscheme `W ⊆ X` of delta-dimension `k + 2` the difference of the two iterated extensions
attached to `W` is the pushforward from `W` of a cycle rationally equivalent to zero, then the
difference of the two iterated extensions is rationally equivalent to zero on every `(k+2)`-cycle.

The cycle is presented over the integral components it is supported on, those form a locally
finite family and each extension keeps them as carriers, so the difference is a locally finite sum
of pushforwards of rational equivalences; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible`. -/
theorem isRationallyEquivalentToZero_sub_extendCycleGroup_of_components
    (hstep : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
      ∃ a : CycleGroup C (W.subschemeι ≫ p) k,
        IsRationallyEquivalentToZero C (W.subschemeι ≫ p) k a ∧
        RL.extendCycleGroup (RN'.cycle W hW hDim) - RN.extendCycleGroup (RL'.cycle W hW hDim) =
          properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k a)
    (β : CycleGroup C p (k + 1 + 1)) :
    IsRationallyEquivalentToZero C p k
      (RL.extendCycleGroup (RN'.extendCycleGroup β) -
        RN.extendCycleGroup (RL'.extendCycleGroup β)) := by
  classical
  choose b hb hbpush using fun i : cycleSupportIndex β ↦
    hstep (integralComponentAt i.1) (isIntegral_integralComponentAt i.1)
      (schemeDeltaDimension_cycleSupportIndex β i)
  refine isRationallyEquivalentToZero_sub_of_finsum C p k
    (fun i : cycleSupportIndex β ↦ integralComponentAt i.1)
    (locallyFinite_support_integralComponentAt β) _ _
    (fun i ↦ RL.extendCycleGroup (β.1 i.1 • RN'.cycle (integralComponentAt i.1)
      (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i)))
    (fun i ↦ RN.extendCycleGroup (β.1 i.1 • RL'.cycle (integralComponentAt i.1)
      (isIntegral_integralComponentAt i.1) (schemeDeltaDimension_cycleSupportIndex β i)))
    (fun i ↦ support_extendCycleGroup_subset_of_support_subset C p RL _ _
      (support_zsmul_cycle_primeCycle_subset C p RN' β i))
    (fun i ↦ support_extendCycleGroup_subset_of_support_subset C p RN _ _
      (support_zsmul_cycle_primeCycle_subset C p RL' β i))
    (extendCycleGroup_extendCycleGroup_finsum_primeCycles C p k RL RN' β)
    (extendCycleGroup_extendCycleGroup_finsum_primeCycles C p k RN RL' β)
    (fun i ↦ β.1 i.1 • b i)
    (fun i ↦ (rationalEquivalences C ((integralComponentAt i.1).subschemeι ≫ p) k).zsmul_mem
      (hb i) _) fun i ↦ ?_
  rw [← properPushforwardHom_apply, map_zsmul, properPushforwardHom_apply, map_zsmul, map_zsmul,
    ← smul_sub, hbpush i]

end Extension

/-! ### Stacks 02TH as a hypothesis -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **Stacks 02TH, for the restrictions of `ℒ` and `𝒩` to the integral components of `X`.** On
every integral closed subscheme `W ⊆ X` of delta-dimension `k + 2`, the class of
`c₁(ℒ|_W) ∩ div_{𝒩|_W}(t)` in `A_k(W)` equals the class of `c₁(𝒩|_W) ∩ div_{ℒ|_W}(s)`, where `s`
and `t` are the meromorphic sections the component rules of `ℒ` and `𝒩` choose on `W`.

This is an equality of *classes*, as the tag asserts. -/
def FirstChernCapCommutesOnIntegralComponents : Prop :=
  ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)),
    haveI := isInvertible_presheaf_modulePullback L W.subschemeι
    haveI := isInvertible_presheaf_modulePullback N W.subschemeι
    firstChernClassCapOfInvertible C (W.subschemeι ≫ p) k
        ((Scheme.Modules.pullback W.subschemeι).obj L)
        (firstChernComponentCycleRule C p (k + 1) N W hW hDim) =
      firstChernClassCapOfInvertible C (W.subschemeι ≫ p) k
        ((Scheme.Modules.pullback W.subschemeι).obj N)
        (firstChernComponentCycleRule C p (k + 1) L W hW hDim)

/-! ### The component step -/

/-- Capping with the transported rule of `ℒ` or with the rule of `ℒ|_W` gives the same class on a
cycle on `W`. -/
private theorem firstChernClassCap_pullbackComponentRule_eq
    {W : X.IdealSheafData} (c : CycleGroup C (W.subschemeι ≫ p) (k + 1)) :
    firstChernClassCap C (W.subschemeι ≫ p) k
        (pullbackComponentRule C (W.subschemeι ≫ p) p W.subschemeι rfl k
          (firstChernComponentCycleRule C p k L)) c =
      haveI := isInvertible_presheaf_modulePullback L W.subschemeι
      firstChernClassCap C (W.subschemeι ≫ p) k
        (firstChernComponentCycleRule C (W.subschemeι ≫ p) k
          ((Scheme.Modules.pullback W.subschemeι).obj L)) c :=
  (firstChernClassCap_congr C (W.subschemeι ≫ p) k _ _
    (fun V hV hDimV ↦ rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule
      C (W.subschemeι ≫ p) p W.subschemeι rfl k L V hV hDimV) _).symm

/-- Stacks 02SU for the transported rule of `ℒ`: pushing the extension along `i_W` is the
extension of the pushforward. -/
private theorem properPushforward_extendCycleGroup_pullbackComponentRule
    {W : X.IdealSheafData} (c : CycleGroup C (W.subschemeι ≫ p) (k + 1)) :
    properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k
        ((firstChernCapRule C (W.subschemeι ≫ p) k
          (pullbackComponentRule C (W.subschemeι ≫ p) p W.subschemeι rfl k
            (firstChernComponentCycleRule C p k L))).extendCycleGroup c) =
      (firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup
        (properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl (k + 1) c) :=
  properPushforward_firstChernCapRule_extendCycleGroup C (W.subschemeι ≫ p) p W.subschemeι rfl k _
    (firstChernComponentCycleRule C p k L)
    (firstChernCapCompatibleWithPushforward_pullbackComponentRule C (W.subschemeι ≫ p) p
      W.subschemeι rfl k (firstChernComponentCycleRule C p k L)) c

/-- **The component step of Stacks 02TJ.** Granted Stacks 02TH on `W`, the difference of the two
iterated cap product cycles attached to an integral closed subscheme `W ⊆ X` of delta-dimension
`k + 2` is the pushforward along `i_W` of a `k`-cycle on `W` that is rationally equivalent to
zero.

Both cap products are pushed from `W` to `X` by Stacks 02SU through the transported rules, after
which the difference upstairs is rationally equivalent to zero by Stacks 02TH; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible`. -/
theorem exists_isRationallyEquivalentToZero_comm_component
    (h : FirstChernCapCommutesOnIntegralComponents C p k L N) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt)) :
    ∃ a : CycleGroup C (W.subschemeι ≫ p) k,
      IsRationallyEquivalentToZero C (W.subschemeι ≫ p) k a ∧
      (firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup
          (firstChernComponentCycle C p (k + 1) (firstChernComponentCycleRule C p (k + 1) N)
            W hW hDim) -
        (firstChernCapRule C p k (firstChernComponentCycleRule C p k N)).extendCycleGroup
          (firstChernComponentCycle C p (k + 1) (firstChernComponentCycleRule C p (k + 1) L)
            W hW hDim) =
        properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k a := by
  refine ⟨(firstChernCapRule C (W.subschemeι ≫ p) k
      (pullbackComponentRule C (W.subschemeι ≫ p) p W.subschemeι rfl k
        (firstChernComponentCycleRule C p k L))).extendCycleGroup
      (firstChernComponentCycleRule C p (k + 1) N W hW hDim) -
    (firstChernCapRule C (W.subschemeι ≫ p) k
      (pullbackComponentRule C (W.subschemeι ≫ p) p W.subschemeι rfl k
        (firstChernComponentCycleRule C p k N))).extendCycleGroup
      (firstChernComponentCycleRule C p (k + 1) L W hW hDim), ?_, ?_⟩
  · -- the difference upstairs is rationally equivalent to zero, by Stacks 02TH
    exact QuotientAddGroup.eq_iff_sub_mem.1
      ((firstChernClassCap_pullbackComponentRule_eq C p k L _).trans
        ((h W hW hDim).trans (firstChernClassCap_pullbackComponentRule_eq C p k N _).symm))
  · -- Stacks 02SU in each degree, through the transported rules
    rw [properPushforward_sub, properPushforward_extendCycleGroup_pullbackComponentRule C p k L,
      properPushforward_extendCycleGroup_pullbackComponentRule C p k N]
    rfl

/-! ### Stacks 02TJ -/

/-- **Stacks 02TJ, from its two inputs.** For two invertible modules `ℒ` and `𝒩` on a scheme `X`
locally of finite type over the base, intersecting successively with the two first Chern classes
is independent of the order: `c₁(ℒ) ∩ c₁(𝒩) ∩ α = c₁(𝒩) ∩ c₁(ℒ) ∩ α` in `A_k(X)` for
`α ∈ A_{k+1+1}(X)`.

The four descended operations are those of `Stacks.Chow.firstChernClassCapOnChowOfInvertible`, so
Stacks 02TI enters only through its reduced input `hkills`, and Stacks 02TH only through the
class-level hypothesis `hcomm`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernCapCommutativityInvertible`. Both inputs are theorems
here (`Stacks.Chow.firstChernCapKillsPrincipalDivisor` and
`Stacks.Chow.GenuineChern.firstChernCapCommutesOnIntegralComponents`), and the statement with them
supplied is `Stacks.Chow.firstChernClassCapOnChowOfInvertible_comm_unconditional`. -/
theorem firstChernClassCapOnChowOfInvertible_comm
    (hkills : ∀ j : ℤ, FirstChernCapKillsPrincipalDivisor C j)
    (hcomm : FirstChernCapCommutesOnIntegralComponents C p k L N)
    (α : chowGroup C p (k + 1 + 1)) :
    firstChernClassCapOnChowOfInvertible C k (hkills k) p L
        (firstChernClassCapOnChowOfInvertible C (k + 1) (hkills (k + 1)) p N α) =
      firstChernClassCapOnChowOfInvertible C k (hkills k) p N
        (firstChernClassCapOnChowOfInvertible C (k + 1) (hkills (k + 1)) p L α) := by
  induction α using QuotientAddGroup.induction_on with
  | H β =>
    have hzero := isRationallyEquivalentToZero_sub_extendCycleGroup_of_components C p k
      (firstChernCapRule C p k (firstChernComponentCycleRule C p k L))
      (firstChernCapRule C p k (firstChernComponentCycleRule C p k N))
      (firstChernCapRule C p (k + 1) (firstChernComponentCycleRule C p (k + 1) L))
      (firstChernCapRule C p (k + 1) (firstChernComponentCycleRule C p (k + 1) N))
      (fun W hW hDim ↦ exists_isRationallyEquivalentToZero_comm_component C p k L N hcomm
        W hW hDim) β
    have hmk : (QuotientAddGroup.mk' (rationalEquivalences C p k))
        ((firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup
            ((firstChernCapRule C p (k + 1)
              (firstChernComponentCycleRule C p (k + 1) N)).extendCycleGroup β) -
          (firstChernCapRule C p k (firstChernComponentCycleRule C p k N)).extendCycleGroup
            ((firstChernCapRule C p (k + 1)
              (firstChernComponentCycleRule C p (k + 1) L)).extendCycleGroup β)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 hzero
    rw [map_sub, sub_eq_zero] at hmk
    exact hmk

end Stacks.Chow

end
