module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapClosedImmersionInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity.ComponentRuleFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent

/-!
# Intersecting with a first Chern class kills a rational equivalence as soon as it kills one
principal divisor

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project. Stacks 02TI asserts that
for `X` locally of finite type over `S` and `ℒ` an invertible `𝒪_X`-module the cap product
`α ↦ c₁(ℒ) ∩ α` of Stacks 02SO kills every `(k+1)`-cycle rationally equivalent to zero, so that it
descends to `c₁(ℒ) ∩ - : A_{k+1}(X) ⟶ A_k(X)`.

The proof of the source has two halves. The first is a reduction: a cycle rationally equivalent to
zero is a locally finite sum `α = ∑_j (i_j)_* div_{W_j}(f_j)` of pushforwards of principal
divisors along the inclusions of integral closed subschemes `W_j ⊆ X` of delta-dimension `k + 2`,
the cap product commutes with proper pushforward (Stacks 02SU), and the summands are therefore
killed one at a time. The second is the integral case: `c₁(ℒ|_W) ∩ div_W(f) = 0` for an integral
`W` of delta-dimension `k + 2`, which the source obtains from the commutativity of Stacks 02TH.

This file proves the **reduction, with no hypothesis**, in the form of an equivalence: the cap
products of all invertible modules on all schemes locally of finite type over `S` factor through
rational equivalence in degree `k` exactly when they kill the principal divisor of a single
nonzero rational function on an integral scheme of delta-dimension `k + 2`.

## Main definitions

* `Stacks.Chow.FirstChernCapFactorsEverywhere` — the conclusion of Stacks 02TI, asserted for
  every scheme locally of finite type over the base and every invertible module on it at once.
* `Stacks.Chow.FirstChernCapKillsPrincipalDivisor` — the integral case the source reduces to.

## Main results

* `Stacks.Chow.firstChernClassCapOfInvertible_eq_zero_of_killsPrincipalDivisor` — the reduction
  itself: granted the integral case, the cap product of an invertible module kills every cycle
  rationally equivalent to zero.
* `Stacks.Chow.firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor` — the two assertions are
  equivalent, so the reduction loses nothing.
* `Stacks.Chow.firstChernClassCapOnChowOfInvertible` — the descended operation
  `A_{k+1}(X) ⟶ A_k(X)`, as a function of the integral case alone.

## Implementation notes

### Why the reduction is stated as an equivalence

The integral case is the statement of Stacks 02TI for the scheme `W` and the cycle `div_W(f)`:
`div_W(f)` is rationally equivalent to zero on `W` by Stacks 02RW. So quantifying the conclusion
over all schemes over the base makes the reduction an equivalence rather than an implication, and
no hypothesis is carried by anything below. What is still missing is Stacks 02TH, and through it
the key formula of Stacks 0AYC and the tame symbol reciprocity of Stacks 0EAX.

### The two inputs of the reduction

Pushing the cap product through the inclusion `i_j : W_j ⟶ X` uses Stacks 02SU at the level of
*cycles*, `Stacks.Chow.properPushforward_firstChernCapRule_extendCycleGroup`, which needs the
component rules upstairs and downstairs to be compatible coefficientwise. The rules of `ℒ|_{W_j}`
and of `ℒ` are not: each chooses a meromorphic section on each integral component independently.
The transported rule `Stacks.Chow.pullbackComponentRule` is compatible by construction, and
agrees with the rule of `ℒ|_{W_j}` in the Chow group of every component, which is enough because
the conclusion is a statement about rational equivalence. Summing over the locally finite family
is `Stacks.Chow.IntegralComponentRule.extendCycleGroup_finsum` on one side and
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion` on the other.

## References

* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) (k : ℤ)

/-! ### The two assertions -/

/-- **The conclusion of Stacks 02TI, for every scheme over the base at once.** Intersecting with
the first Chern class of an invertible module kills every `(k+1)`-cycle rationally equivalent to
zero, whatever the scheme locally of finite type over the base and whatever the module. -/
def FirstChernCapFactorsEverywhere : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L],
    FirstChernClassCapFactorsThroughRationalEquivalence C p k
      (firstChernComponentCycleRule C p k L)

/-- **The integral case of Stacks 02TI.** On an integral scheme `Z` of delta-dimension `k + 2`
locally of finite type over the base, intersecting the principal divisor of a nonzero rational
function with the first Chern class of an invertible module gives zero in `A_k(Z)`.

The cycle is taken in the flexible form "a `(k+1)`-cycle whose underlying cycle is `div(f)`", as
`Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle` is, so that the statement applies
with no transport of gradings. -/
def FirstChernCapKillsPrincipalDivisor : Prop :=
  ∀ (Z : Scheme.{u}) (q : Z ⟶ C.S) [LocallyOfFiniteType q] [IsIntegral Z]
    [IsLocallyNoetherian Z]
    (_hq : schemeDeltaDimension C q = ((k + 1 + 1 : ℤ) : EInt)) (M : Z.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M]
    (f : Z.functionField) (_hf : f ≠ 0) (β : CycleGroup C q (k + 1))
    (_hβ : (β : AlgebraicCycle Z ℤ) = principalCycle Z f),
    firstChernClassCapOfInvertible C q k M β = 0

/-! ### One integral closed subscheme -/

/-- **The reduction on a single integral closed subscheme.** Granted the integral case, the cycle
representing `c₁(ℒ) ∩ (i_W)_* div_W(f)` is the pushforward along `i_W` of a `k`-cycle on `W` that
is rationally equivalent to zero.

The `k`-cycle produced is the one representing `c₁(ℒ|_W) ∩ div_W(f)`, computed through the
transported component rule rather than through the rule of `ℒ|_W`, since only the transported rule
is compatible with pushforward coefficientwise. -/
theorem exists_isRationallyEquivalentToZero_component
    (h : FirstChernCapKillsPrincipalDivisor C k) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 + 1 : ℤ) : EInt))
    (g : (rationalFunctions W.subscheme)ˣ) (D : CycleGroup C p (k + 1))
    (hD : (D : AlgebraicCycle X ℤ) = principalDivisorPushforward C p W hW g) :
    ∃ a : CycleGroup C (W.subschemeι ≫ p) k,
      IsRationallyEquivalentToZero C (W.subschemeι ≫ p) k a ∧
      (firstChernCapRule C p k (firstChernComponentCycleRule C p k L)).extendCycleGroup D =
        properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl k a := by
  have := hW
  have : IsLocallyNoetherian W.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.subschemeι ≫ p)
  have := isInvertible_presheaf_modulePullback L W.subschemeι
  set f : W.subscheme.functionField :=
    (rationalFunctionsEquivFunctionField W.subscheme).1 (g : rationalFunctions W.subscheme)
    with hfdef
  have hf : f ≠ 0 := by
    intro h0
    exact g.ne_zero ((rationalFunctionsEquivFunctionField W.subscheme).1.injective
      (h0.trans (map_zero _).symm))
  set β : CycleGroup C (W.subschemeι ≫ p) (k + 1) :=
    ⟨principalCycle W.subscheme f, by
      simpa only [add_sub_cancel_right] using
        principalCycle_mem_cyclesOfDimension C (W.subschemeι ≫ p) hDim f⟩ with hβdef
  have hDβ : D = properPushforward C (W.subschemeι ≫ p) p W.subschemeι rfl (k + 1) β := by
    refine Subtype.ext (hD.trans ?_)
    rfl
  set chernUp : FirstChernComponentCycleRule C (W.subschemeι ≫ p) k :=
    pullbackComponentRule C (W.subschemeι ≫ p) p W.subschemeι rfl k
      (firstChernComponentCycleRule C p k L) with hchernUp
  refine ⟨(firstChernCapRule C (W.subschemeι ≫ p) k chernUp).extendCycleGroup β, ?_, ?_⟩
  · have hcongr := firstChernClassCap_congr C (W.subschemeι ≫ p) k
      (firstChernComponentCycleRule C (W.subschemeι ≫ p) k
        ((Scheme.Modules.pullback W.subschemeι).obj L))
      chernUp
      (fun V hV hDimV =>
        rationallyEquivalent_firstChernComponentCycleRule_pullbackComponentRule C
          (W.subschemeι ≫ p) p W.subschemeι rfl k L V hV hDimV) β
    have hzero : firstChernClassCap C (W.subschemeι ≫ p) k chernUp β = 0 :=
      hcongr.symm.trans (h W.subscheme (W.subschemeι ≫ p) hDim
        ((Scheme.Modules.pullback W.subschemeι).obj L) f hf β rfl)
    exact (QuotientAddGroup.eq_zero_iff _).1 hzero
  · rw [hDβ, properPushforward_firstChernCapRule_extendCycleGroup C (W.subschemeι ≫ p) p
      W.subschemeι rfl k chernUp (firstChernComponentCycleRule C p k L)
      (firstChernCapCompatibleWithPushforward_pullbackComponentRule C (W.subschemeι ≫ p) p
        W.subschemeι rfl k (firstChernComponentCycleRule C p k L)) β]

/-! ### The reduction -/

/-- **The reduction step of Stacks 02TI.** Granted the integral case, intersecting with the first
Chern class of an invertible module kills every `(k+1)`-cycle rationally equivalent to zero.

Stacks 02RW presents such a cycle as a locally finite sum `α = ∑_j (i_j)_* div_{W_j}(f_j)` over
integral closed subschemes `W_j ⊆ X` of delta-dimension `k + 2`. The cycle representing
`c₁(ℒ) ∩ α` is then the corresponding locally finite sum of the cycles representing
`c₁(ℒ) ∩ (i_j)_* div_{W_j}(f_j)`, each of which is the pushforward of a cycle rationally
equivalent to zero on `W_j`; a locally finite sum of such pushforwards is rationally equivalent to
zero. -/
theorem firstChernClassCapOfInvertible_eq_zero_of_killsPrincipalDivisor
    (h : FirstChernCapKillsPrincipalDivisor C k) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (α : CycleGroup C p (k + 1)) (hα : IsRationallyEquivalentToZero C p (k + 1) α) :
    firstChernClassCapOfInvertible C p k L α = 0 := by
  classical
  obtain ⟨J, W, hW, hDim, hLocal, g, hcoeff⟩ := hα
  set R := firstChernCapRule C p k (firstChernComponentCycleRule C p k L) with hR
  -- the summands of `α`, as `(k+1)`-cycles on `X`
  set D : J → CycleGroup C p (k + 1) := fun j =>
    ⟨principalDivisorPushforward C p (W j) (hW j) (g j),
      principalDivisorPushforward_mem_cyclesOfDimension C p (k + 1) (W j) (hW j) (hDim j) (g j)⟩
    with hDdef
  have hDcoe : ∀ j, (D j : AlgebraicCycle X ℤ) =
      principalDivisorPushforward C p (W j) (hW j) (g j) := fun _ => rfl
  -- the `k`-cycles upstairs that the reduction on one component produces
  have hstep := fun j => exists_isRationallyEquivalentToZero_component C k h p L
    (W j) (hW j) (hDim j) (g j) (D j) (hDcoe j)
  choose a ha hpush using hstep
  -- the family of closed immersions is locally finite
  have hfinite : LocallyFinite fun j => Set.range ((W j).subschemeι).base := by
    refine hLocal.subset fun j => ?_
    rw [(W j).range_subschemeι]
  -- the representative of `c₁(ℒ) ∩ α` is the locally finite sum of the pushforwards
  have hsum : ∀ x : X, (R.extendCycleGroup α).1 x = ∑ᶠ j : J,
      (properPushforward C ((W j).subschemeι ≫ p) p (W j).subschemeι rfl k (a j)).1 x := by
    intro x
    rw [R.extendCycleGroup_finsum D (fun j => ((W j).support : Set X)) hLocal
      (fun j => support_principalDivisorPushforward_subset C p (W j) (hW j) (g j)) α
      (fun y => (hcoeff y).trans rfl) x]
    exact finsum_congr fun j => congrArg (fun c : CycleGroup C p k => c.1 x) (hpush j)
  have hmem : IsRationallyEquivalentToZero C p k (R.extendCycleGroup α) :=
    rationallyEquivalentToZero_finsum_of_isClosedImmersion C p k (fun j => (W j).subschemeι)
      hfinite a ha (R.extendCycleGroup α) hsum
  exact (QuotientAddGroup.eq_zero_iff _).2 hmem

/-- **Stacks 02TI, reduced to its integral case.** The cap product with the first Chern class of
an invertible module factors through rational equivalence, for every scheme locally of finite type
over the base and every invertible module on it, **exactly when** it kills the principal divisor of
a nonzero rational function on an integral scheme of delta-dimension `k + 2`.

The reverse implication is the reduction step of the source's proof of Stacks 02TI; the forward
implication holds because `div_Z(f)` is rationally equivalent to zero on `Z` itself, which is
Stacks 02RW. So the delivered content of this tag is the reduction, and what remains of the tag is
its integral case — the source's appeal to Stacks 02TH. -/
@[stacks 02TI "the vanishing reduced to one principal divisor on an integral scheme"]
theorem firstChernCapFactorsEverywhere_iff_killsPrincipalDivisor :
    FirstChernCapFactorsEverywhere C k ↔ FirstChernCapKillsPrincipalDivisor C k := by
  refine ⟨fun hall Z q _ _ _ hq M _ f hf β hβ => ?_, fun h X p _ L _ α hα => ?_⟩
  · exact hall Z q M β (isRationallyEquivalentToZero_of_eq_principalCycle C q hq hf β hβ)
  · exact firstChernClassCapOfInvertible_eq_zero_of_killsPrincipalDivisor C k h p L α hα

/-! ### The descended operation -/

/-- **Stacks 02TI, the operation on Chow groups, as a function of the integral case.**
Intersection with the first Chern class of an invertible module, descended to
`c₁(ℒ) ∩ - : A_{k+1}(X) ⟶ A_k(X)`.

This is `Stacks.Chow.firstChernClassCapOnChow` with the vanishing supplied by
`Stacks.Chow.firstChernClassCapOfInvertible_eq_zero_of_killsPrincipalDivisor`, so that the
integral case is the only input. -/
def firstChernClassCapOnChowOfInvertible (h : FirstChernCapKillsPrincipalDivisor C k)
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    chowGroup C p (k + 1) →+ chowGroup C p k :=
  firstChernClassCapOnChow C p k (firstChernComponentCycleRule C p k L)
    fun α hα => firstChernClassCapOfInvertible_eq_zero_of_killsPrincipalDivisor C k h p L α hα

/-- The descended operation agrees with the cap product on cycle representatives. -/
@[simp]
theorem firstChernClassCapOnChowOfInvertible_mk (h : FirstChernCapKillsPrincipalDivisor C k)
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOnChowOfInvertible C k h p L
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      firstChernClassCapOfInvertible C p k L α :=
  rfl

end Stacks.Chow

end
