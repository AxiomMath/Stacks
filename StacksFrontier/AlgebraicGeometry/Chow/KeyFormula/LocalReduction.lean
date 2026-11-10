module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula

/-!
# Localizing the key formula, and what its data does not determine

Stacks 0AYC, the key formula, is recorded as the predicate
`Stacks.Chow.KeyFormulaData.KeyFormula` on the cycle-level data
`Stacks.Chow.KeyFormulaData`. This file establishes two things about that predicate.

## The localization

Both sides of the key formula are supported at the codimension-one points of the members
`Z_i` of the family — the left hand side because the restricted divisors are required to be
supported in codimension one, the right hand side because an order of vanishing is zero away
from codimension one. Consequently the key formula is equivalent to a family of identities, one
at each codimension-one point of each `Z_i`, and each of those involves only the finitely many
members of the family through that point.

These are exactly the points `x` of `X` at which `𝒪_{X, x}` is two-dimensional, and the identity
at such a point is obtained in the source from the tame symbol reciprocity law of Stacks 0EAX on
that local ring. So `Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one` is
the step of the source's proof that passes from the equality of cycles to the equality of
coefficients. It is only that step: the identity of coefficients is the right hand side of the
equivalence, and the key formula itself is not proved here.

Stacks 0EAX is itself available, as
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`. What separates it from the identity
of coefficients is the dictionary between the scheme and the two-dimensional local ring
`A = 𝒪_{X, x}`: the members of the family through `x` as the height-one primes of `A`, the local
rings `B_i = 𝒪_{X, ξ_i}` as the localizations `A_{𝔮_i}` compatibly with their tame symbols, and
the order of vanishing on `Z_i` at `x` as `Ring.ord` on `A/𝔮_i`. All three are available: the
first as `Stacks.Chow.heightOnePrimeEquivCoheightOneGenerization`, the second as
`Stacks.Chow.isLocalization_stalk_heightOnePrime` together with
`Stacks.Chow.map_tameSymbol_ringEquiv`, and the third as
`Stacks.Chow.ord_quot_eq_ord_intermediatePointStalk`. This file does not assemble them into the
identity of coefficients.

## What the data does not determine

The second half of this file records an obstruction to stating Stacks 0AYC this way at all.

In `Stacks.Chow.KeyFormulaData` the field `tameSymbol` is unconstrained: nothing relates it to
`orderL`, `orderN`, `restrictedDivisorL` and `restrictedDivisorN`. The left hand side of the key
formula does not mention it (`Stacks.Chow.KeyFormulaData.leftCoeff_withTameSymbol`), so the key
formula asserts that a cycle not depending on the tame symbols equals one that does. Taking the
family of tame symbols to be arbitrary therefore forces every principal divisor to vanish:
`Stacks.Chow.principalDivisorPushforward_eq_zero_of_forall_keyFormula` derives from
"`KeyFormula` holds for every term of `KeyFormulaData`" that the principal divisor of *every*
nonzero rational function on *every* integral closed subscheme attached to a codimension-one
point pushes forward to the zero cycle — that is, that rational equivalence (Stacks 02RW) is
trivial.

So `Stacks.Chow.KeyFormulaData.KeyFormula` is a predicate that fails for some of its data, not a
theorem awaiting a proof, and no declaration can produce it from a term of `KeyFormulaData`
alone. To carry Stacks 0AYC the structure must gain the fields tying `tameSymbol` to the orders
and the restricted divisors. `Stacks.Chow.KeyFormulaLocalData` adds the fields that tie
`tameSymbol` and the two orders of vanishing to a family of pairs of rational functions, using
Stacks 0EAH in the form `Stacks.Chow.tameSymbolOfKrullDimOne`; the restricted divisors stay free,
and `Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula`
shows that the collapse survives that constraint.

## Main definitions

* `Stacks.Chow.KeyFormulaData.IsFamilyCodimOnePoint` — the points of `X` at which the key
  formula has content: the codimension-one points of the members of the family.
* `Stacks.Chow.KeyFormulaData.withTameSymbol` — the same data with another family of tame
  symbols.
* `Stacks.Chow.KeyFormulaData.singleComponent` — one prime divisor, vanishing orders and
  vanishing restricted divisors, one prescribed tame symbol.

## Main results

* `Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one` — the key formula is
  equivalent to the family of its local identities at the codimension-one points of the `Z_i`.
  This is the localization step of the source's proof, not the key formula.
* `Stacks.Chow.principalDivisorPushforward_eq_zero_of_forall_keyFormula` — the key formula, read
  as a statement about arbitrary `KeyFormulaData`, collapses rational equivalence.

## References

* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The pushforward of the zero cycle along a closed immersion is zero. -/
theorem closedSubschemeCyclePushforward_zero_apply (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) (W : X.IdealSheafData) (y : X) :
    closedSubschemeCyclePushforward C p W 0 y = 0 := by
  by_cases hy : y ∈ Set.range ⇑W.subschemeι
  · obtain ⟨z, rfl⟩ := hy
    simp
  · exact closedSubschemeCyclePushforward_apply_of_notMem_range C p W 0 hy

namespace KeyFormulaData

variable {X : Scheme.{u}} (D : KeyFormulaData X) (C : ChowSituation.{u}) (p : X ⟶ C.S)

/-! ### The points at which the key formula has content -/

/-- A point of `X` is a codimension-one point of the family if it is the image of a
codimension-one point of some member `Z_i`.

These are the points at which both sides of the key formula can be nonzero. On an integral `X`
of delta-dimension `n` they are the points of delta-dimension `n - 2`, at which the local ring
of `X` is two-dimensional. -/
def IsFamilyCodimOnePoint (x : X) : Prop :=
  ∃ (i : D.Index) (z : (D.component i).subscheme),
    Order.coheight z = 1 ∧ (D.component i).subschemeι.base z = x

/-- The right hand side of the key formula, as the locally finite sum it is defined to be. -/
theorem tameSymbolCoeff_eq_finsum [LocallyOfFiniteType p] (x : X) :
    D.tameSymbolCoeff C p x =
      ∑ᶠ i : D.Index, principalDivisorPushforward C p (D.component i)
        (D.isIntegral_component i) (D.tameSymbol i) x :=
  rfl

/-- A point carrying a term of a locally finite family of cycles pushed forward from the members
of the family lies on one of those members. -/
private theorem exists_preimage_of_pushforward_ne_zero {i : D.Index}
    {c : AlgebraicCycle (D.component i).subscheme ℤ} {x : X}
    (hc : closedSubschemeCyclePushforward C p (D.component i) c x ≠ 0) :
    ∃ z : (D.component i).subscheme, (D.component i).subschemeι.base z = x := by
  by_contra h
  push Not at h
  refine hc (closedSubschemeCyclePushforward_apply_of_notMem_range C p _ _ fun hmem ↦ ?_)
  obtain ⟨z, hz⟩ := hmem
  exact h z hz

/-- The left hand side of the key formula vanishes away from the codimension-one points of the
members of the family: a nonzero coefficient comes from a nonzero restricted divisor, and those
are supported in codimension one. -/
theorem isFamilyCodimOnePoint_of_leftCoeff_ne_zero {x : X} (hx : D.leftCoeff C p x ≠ 0) :
    D.IsFamilyCodimOnePoint x := by
  obtain ⟨i, hi⟩ : ∃ i : D.Index,
      closedSubschemeCyclePushforward C p (D.component i) (D.componentDifference i) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨z, rfl⟩ := D.exists_preimage_of_pushforward_ne_zero C p hi
  rw [closedSubschemeCyclePushforward_apply, D.componentDifference_apply] at hi
  refine ⟨i, z, ?_, rfl⟩
  by_cases hN : D.restrictedDivisorN i z = 0
  · by_cases hL : D.restrictedDivisorL i z = 0
    · exact absurd (by rw [hN, hL]; ring) hi
    · exact D.coheight_of_restrictedDivisorL i z hL
  · exact D.coheight_of_restrictedDivisorN i z hN

/-- The right hand side of the key formula vanishes away from the codimension-one points of the
members of the family: an order of vanishing is zero outside codimension one. -/
theorem isFamilyCodimOnePoint_of_tameSymbolCoeff_ne_zero [LocallyOfFiniteType p] {x : X}
    (hx : D.tameSymbolCoeff C p x ≠ 0) : D.IsFamilyCodimOnePoint x := by
  rw [D.tameSymbolCoeff_eq_finsum C p] at hx
  obtain ⟨i, hi⟩ : ∃ i : D.Index, principalDivisorPushforward C p (D.component i)
      (D.isIntegral_component i) (D.tameSymbol i) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  rw [principalDivisorPushforward_eq] at hi
  obtain ⟨z, rfl⟩ := D.exists_preimage_of_pushforward_ne_zero C p hi
  rw [closedSubschemeCyclePushforward_apply] at hi
  refine ⟨i, z, ?_, rfl⟩
  have _ := D.isIntegral_component i
  have _ : IsLocallyNoetherian (D.component i).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((D.component i).subschemeι ≫ p)
  by_contra hz
  rw [principalCycle_apply] at hi
  exact hi (Scheme.ord_eq_zero_of_coheight_neq_one hz _)

/-- **The key formula is local at the codimension-one points of the family.** It holds if and
only if its two coefficients agree at the image of every codimension-one point of every member
`Z_i`.

This is the step of the source's proof that says "since we are proving the equality of cycles we
may argue one coefficient at a time", and it is only that step. At such a point `x` the local
ring `𝒪_{X, x}` has dimension two, only the finitely many members of the family through `x`
contribute to either side, and the source derives the resulting identity of coefficients from the
Key Lemma Stacks 0EAX on `𝒪_{X, x}`. That derivation is not carried out here: the identity of
coefficients stands on the right hand side of the equivalence, so this declaration proves the
equivalence and not the key formula.

Stacks 0EAX itself is proved, as
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`. The step from it to the identity of
coefficients goes through the dictionary between `X` and `A = 𝒪_{X, x}` described in the module
documentation. -/
@[stacks 0AYC "the localization step of the source's proof: the equality of the two cycles is \
equivalent to the equality of their coefficients at the codimension-two points of the family"]
theorem keyFormula_iff_forall_component_coheight_one [LocallyOfFiniteType p] :
    D.KeyFormula C p ↔ ∀ (i : D.Index) (z : (D.component i).subscheme), Order.coheight z = 1 →
      D.leftCoeff C p ((D.component i).subschemeι.base z) =
        D.tameSymbolCoeff C p ((D.component i).subschemeι.base z) := by
  rw [D.keyFormula_iff_forall C p]
  refine ⟨fun h i z _ ↦ h _, fun h x ↦ ?_⟩
  by_cases hl : D.leftCoeff C p x = 0
  · by_cases hr : D.tameSymbolCoeff C p x = 0
    · rw [hl, hr]
    · obtain ⟨i, z, hz, rfl⟩ := D.isFamilyCodimOnePoint_of_tameSymbolCoeff_ne_zero C p hr
      exact h i z hz
  · obtain ⟨i, z, hz, rfl⟩ := D.isFamilyCodimOnePoint_of_leftCoeff_ne_zero C p hl
    exact h i z hz

/-! ### The tame symbols are not determined by the rest of the data -/

/-- The same key-formula data with another family of tame symbols. -/
def withTameSymbol (u : (i : D.Index) → (rationalFunctions (D.component i).subscheme)ˣ) :
    KeyFormulaData X :=
  { D with tameSymbol := u }

/-- The left hand side of the key formula does not mention the tame symbols. -/
@[simp]
theorem leftCoeff_withTameSymbol
    (u : (i : D.Index) → (rationalFunctions (D.component i).subscheme)ˣ) (x : X) :
    (D.withTameSymbol u).leftCoeff C p x = D.leftCoeff C p x :=
  rfl

/-- The key-formula data of a single prime divisor with vanishing orders of vanishing and
vanishing restricted divisors, carrying one prescribed tame symbol. Every field of
`Stacks.Chow.KeyFormulaData` is satisfied, and the left hand side of the key formula is
identically zero. -/
def singleComponent {x : X} (hx : Order.coheight x = 1)
    (g : (rationalFunctions (integralComponentAt x).subscheme)ˣ) : KeyFormulaData X where
  Index := PUnit.{u + 1}
  componentPoint _ := x
  coheight_componentPoint _ := hx
  componentPoint_injective a b _ := Subsingleton.elim a b
  locallyFinite_component := locallyFinite_of_finite _
  orderL _ := 0
  orderN _ := 0
  restrictedDivisorL _ := 0
  restrictedDivisorN _ := 0
  coheight_of_restrictedDivisorL _ _ h := absurd rfl h
  coheight_of_restrictedDivisorN _ _ h := absurd rfl h
  tameSymbol _ := g

/-- The left hand side of the key formula for `singleComponent hx g` is zero at every point. -/
@[simp]
theorem leftCoeff_singleComponent {x : X} (hx : Order.coheight x = 1)
    (g : (rationalFunctions (integralComponentAt x).subscheme)ˣ) (y : X) :
    (singleComponent hx g).leftCoeff C p y = 0 := by
  have hdiff : ∀ i, (singleComponent hx g).componentDifference i = 0 := fun _ ↦ sub_self _
  change (∑ᶠ i, closedSubschemeCyclePushforward C p
    ((singleComponent hx g).component i) ((singleComponent hx g).componentDifference i) y) = 0
  simp only [hdiff, closedSubschemeCyclePushforward_zero_apply, finsum_zero]

/-- The tame-symbol side of the key formula for `singleComponent hx g` is the pushforward of the
principal divisor of `g` on the integral component at `x`. -/
@[simp]
theorem tameSymbolCoeff_singleComponent [LocallyOfFiniteType p] {x : X}
    (hx : Order.coheight x = 1)
    (g : (rationalFunctions (integralComponentAt x).subscheme)ˣ) (y : X) :
    (singleComponent hx g).tameSymbolCoeff C p y =
      principalDivisorPushforward C p (integralComponentAt x)
        (isIntegral_integralComponentAt x) g y := by
  rw [(singleComponent hx g).tameSymbolCoeff_eq_finsum C p]
  exact @finsum_unique _ _ _ (inferInstanceAs (Unique PUnit.{u + 1})) _

end KeyFormulaData

/-- **The key formula, read as a statement about arbitrary `Stacks.Chow.KeyFormulaData`,
collapses rational equivalence.** If `Stacks.Chow.KeyFormulaData.KeyFormula` held for every term
of `Stacks.Chow.KeyFormulaData`, then the principal divisor of every nonzero rational function on
every integral closed subscheme attached to a codimension-one point would push forward to the
zero cycle — so every cycle of Stacks 02RW's defining family would vanish and rational
equivalence would be the trivial relation.

The mechanism is that the field `tameSymbol` of `Stacks.Chow.KeyFormulaData` is unconstrained by
the other fields while the left hand side of the key formula does not mention it
(`Stacks.Chow.KeyFormulaData.leftCoeff_withTameSymbol`). Taking the orders of vanishing and the
restricted divisors to be zero makes the left hand side vanish, and the key formula then asserts
that the prescribed tame symbol has trivial principal divisor.

So `Stacks.Chow.KeyFormulaData.KeyFormula` is not a theorem about `Stacks.Chow.KeyFormulaData`:
it fails for some of its data, and no declaration can produce it from a term of that structure
alone. Stacks 0AYC can only be carried by a structure whose tame symbols are tied to its orders
and restricted divisors. Tying the tame symbols alone does not suffice, by
`Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula`. -/
theorem principalDivisorPushforward_eq_zero_of_forall_keyFormula (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (h : ∀ D : KeyFormulaData X, D.KeyFormula C p) {x : X} (hx : Order.coheight x = 1)
    (g : (rationalFunctions (integralComponentAt x).subscheme)ˣ) :
    principalDivisorPushforward C p (integralComponentAt x) (isIntegral_integralComponentAt x) g
      = 0 := by
  have hk := (KeyFormulaData.keyFormula_iff_forall _ C p).1
    (h (KeyFormulaData.singleComponent hx g))
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  have hy := hk y
  rw [KeyFormulaData.leftCoeff_singleComponent, KeyFormulaData.tameSymbolCoeff_singleComponent]
    at hy
  exact hy.symm

end Stacks.Chow

end
