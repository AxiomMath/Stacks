module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward

/-!
# The key formula

Let `X` be an integral scheme locally of finite type over the base of chapter 42, of
delta-dimension `n`, and let `L` and `N` be invertible sheaves on `X` equipped with nonzero
meromorphic sections `s` and `t`. Choose a locally finite family `{Z_i}` of irreducible closed
subsets of codimension one, large enough that `s` generates `L` and `t` generates `N` at the
generic point of every codimension-one subset not in the family. Write `ξ_i` for the generic
point of `Z_i` and `B_i = 𝒪_{X, ξ_i}`, pick generators `s_i` of `L_{ξ_i}` and `t_i` of
`N_{ξ_i}`, and write `s = f_i s_i` and `t = g_i t_i`. Then

* `div_L(s) = ∑ ord_{B_i}(f_i) [Z_i]` and `div_N(t) = ∑ ord_{B_i}(g_i) [Z_i]`;
* `c_1(N) ∩ div_L(s) = ∑ ord_{B_i}(f_i) (Z_i → X)_* div_{N|Z_i}(t_i|Z_i)`, and symmetrically
  `c_1(L) ∩ div_N(t) = ∑ ord_{B_i}(g_i) (Z_i → X)_* div_{L|Z_i}(s_i|Z_i)`.

The *key formula*, Stacks 0AYC, is the assertion that the difference of these two cycles is a
locally finite sum of principal divisors on the `Z_i`, namely

`∑ (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))
  = ∑ (Z_i → X)_* div_{Z_i}(∂_{B_i}(f_i, g_i))`,

with `∂_{B_i}` the tame symbol of the one-dimensional Noetherian local domain `B_i`. It is the
single input from which chapter 42 derives that intersecting with the first Chern class of an
invertible sheaf factors through rational equivalence (Stacks 02TI), that these operations
commute (Stacks 02TH), and that the Gysin homomorphism of an effective Cartier divisor factors
through rational equivalence (Stacks 02TM, 02TO).

## Shape of the statement

Of the sheaf-theoretic quantities the formula mentions, the order of vanishing
`ord_{Z_i, L}(s)` of a meromorphic section along a prime divisor and the divisor cycle it
assembles into are available (Stacks 02SF is `Stacks.Divisors.orderOfVanishingMeromorphic` and
Stacks 02SJ(1) is `Stacks.Chow.divisorOfMeromorphicSection`), and so is the tame symbol
`∂_{B_i}` (Stacks 0EAH is `Stacks.Chow.tameSymbolOfKrullDimOne`, and the Key Lemma Stacks 0EAX
that the source *derives* from it in Section 0EAU is
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`). What is missing is the restriction
`div_{M|Z_i}(v_i|Z_i)` of such a divisor to a prime divisor. Accordingly the key formula
is recorded here as a statement about the *cycle-level* data it involves, bundled as
`Stacks.Chow.KeyFormulaData`: the family `{Z_i}`, the two integers `ord_{B_i}(f_i)` and
`ord_{B_i}(g_i)`, the two restricted divisors as cycles on `Z_i`, and the tame symbols as
rational functions on `Z_i`. Whoever lands the restriction of a divisor to a prime divisor
instantiates the structure and recovers the statement of the source verbatim; the orders of
vanishing and the tame symbols are already tied to a family of local ratios by
`Stacks.Chow.KeyFormulaLocalData`. The one condition the restricted divisors are
required to satisfy — that they are supported in codimension one on `Z_i` — is what makes both
sides of the formula cycles of delta-dimension `n - 2`.

`Stacks.Chow.KeyFormulaData.KeyFormula` is therefore a predicate on that data rather than a
theorem: with the tame symbols unconstrained it fails for some of its data, as
`Stacks.Chow.principalDivisorPushforward_eq_zero_of_forall_keyFormula` shows, and constraining
them does not repair that, as
`Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula`
shows. **The key formula itself is not proved in this repository.** What is proved about it is,
first, its reduction to the local identity at each codimension-two point
(`Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one`, which is the step of
the source's proof passing from cycles to coefficients, and nothing more) and, second, the
consequence for which chapter 42 uses it:
`Stacks.Chow.isRationallyEquivalentToZero_of_keyFormula` says that a cycle presented by the left
hand side is rationally equivalent to zero, which is exactly how Stacks 02TH, 02TI, 02TM and
02TO consume the formula.

The structure is stated for an arbitrary scheme `X`: its data make sense without any hypothesis,
and the integrality and finite-type hypotheses of the source are carried by the statements
about it rather than by the data.

## Main definitions

* `Stacks.Chow.KeyFormulaData` — the data of "the situation above" Stacks 0AYC, at the level of
  cycles.
* `Stacks.Chow.KeyFormulaData.leftCycle` — the left hand side of the key formula.
* `Stacks.Chow.KeyFormulaData.tameSymbolCycle` — the right hand side of the key formula.
* `Stacks.Chow.KeyFormulaData.KeyFormula` — the key formula itself (Stacks 0AYC).

## Main results

* `Stacks.Chow.KeyFormulaData.leftCycle_apply`,
  `Stacks.Chow.KeyFormulaData.tameSymbolCycle_apply` — the coefficients of the two sides.
* `Stacks.Chow.KeyFormulaData.keyFormula_iff_forall` — the key formula read coefficientwise.
* `Stacks.Chow.KeyFormulaData.schemeDeltaDimension_component` — each `Z_i` has
  delta-dimension `n - 1`.
* `Stacks.Chow.KeyFormulaData.leftCycle_mem_cyclesOfDimension` — the left hand side is a cycle of
  delta-dimension `n - 2`.
* `Stacks.Chow.isRationallyEquivalentToZero_of_keyFormula`,
  `Stacks.Chow.isRationallyEquivalentToZero_leftCycle` — the key formula makes the left hand side
  rationally equivalent to zero.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The data entering the key formula of Stacks 0AYC, at the level of cycles.

A term of this type records a locally finite family `{Z_i}` of prime divisors of `X`, indexed by
their generic points `ξ_i`, together with, for each `i`:

* the integers `ord_{B_i}(f_i)` and `ord_{B_i}(g_i)` — the orders of vanishing along `Z_i` of the
  two meromorphic sections, `B_i = 𝒪_{X, ξ_i}` (fields `orderL` and `orderN`);
* the restricted divisors `div_{L|Z_i}(s_i|Z_i)` and `div_{N|Z_i}(t_i|Z_i)`, as cycles on the
  integral closed subscheme `Z_i` supported in codimension one (fields `restrictedDivisorL` and
  `restrictedDivisorN`);
* the tame symbol `∂_{B_i}(f_i, g_i) ∈ κ(ξ_i)^* = R(Z_i)^*` (field `tameSymbol`).

The invertible sheaves, their meromorphic sections and the chosen generators do not appear: the
formula only uses them through these quantities. `Stacks.Chow.KeyFormulaLocalData` constrains
`orderL`, `orderN` and `tameSymbol` to be the ones a family of pairs of rational functions
determines, by Stacks 02SF and by Stacks 0EAH in the form
`Stacks.Chow.tameSymbolOfKrullDimOne`; the restricted divisors cannot be constrained this way,
because the restriction of a divisor to a prime divisor is not available here. -/
structure KeyFormulaData (X : Scheme.{u}) : Type (u + 1) where
  /-- The index set of the family `{Z_i}`. -/
  Index : Type u
  /-- The generic point `ξ_i` of `Z_i`. -/
  componentPoint : Index → X
  /-- Each `Z_i` has codimension one in `X`. -/
  coheight_componentPoint : ∀ i, Order.coheight (componentPoint i) = 1
  /-- Distinct indices give distinct prime divisors. -/
  componentPoint_injective : Function.Injective componentPoint
  /-- The family `{Z_i}` is locally finite. -/
  locallyFinite_component : LocallyFinite fun i ↦ closure {componentPoint i}
  /-- The order of vanishing `ord_{B_i}(f_i)` of the section of `L` along `Z_i`. -/
  orderL : Index → ℤ
  /-- The order of vanishing `ord_{B_i}(g_i)` of the section of `N` along `Z_i`. -/
  orderN : Index → ℤ
  /-- The restricted divisor `div_{L|Z_i}(s_i|Z_i)`, a cycle on `Z_i`. -/
  restrictedDivisorL : (i : Index) →
    AlgebraicCycle (integralComponentAt (componentPoint i)).subscheme ℤ
  /-- The restricted divisor `div_{N|Z_i}(t_i|Z_i)`, a cycle on `Z_i`. -/
  restrictedDivisorN : (i : Index) →
    AlgebraicCycle (integralComponentAt (componentPoint i)).subscheme ℤ
  /-- A divisor on `Z_i` is supported in codimension one. -/
  coheight_of_restrictedDivisorL : ∀ (i : Index)
    (z : (integralComponentAt (componentPoint i)).subscheme),
    restrictedDivisorL i z ≠ 0 → Order.coheight z = 1
  /-- A divisor on `Z_i` is supported in codimension one. -/
  coheight_of_restrictedDivisorN : ∀ (i : Index)
    (z : (integralComponentAt (componentPoint i)).subscheme),
    restrictedDivisorN i z ≠ 0 → Order.coheight z = 1
  /-- The tame symbol `∂_{B_i}(f_i, g_i)`, a nonzero rational function on `Z_i`. -/
  tameSymbol : (i : Index) →
    (rationalFunctions (integralComponentAt (componentPoint i)).subscheme)ˣ

namespace KeyFormulaData

variable {X : Scheme.{u}} (D : KeyFormulaData X)

/-- The prime divisor `Z_i`, as a closed subscheme of `X`: the reduced induced structure on the
closure of `ξ_i`. -/
abbrev component (i : D.Index) : X.IdealSheafData :=
  integralComponentAt (D.componentPoint i)

/-- The prime divisor `Z_i` is integral. -/
theorem isIntegral_component (i : D.Index) : IsIntegral (D.component i).subscheme :=
  isIntegral_integralComponentAt _

/-- The support of `Z_i` is the closure of `ξ_i`. -/
theorem coe_support_component (i : D.Index) :
    ((D.component i).support : Set X) = closure {D.componentPoint i} :=
  coe_support_integralComponentAt _

/-- The family of supports of the `Z_i` is locally finite. -/
theorem locallyFinite_support_component :
    LocallyFinite fun i ↦ ((D.component i).support : Set X) := by
  simpa only [D.coe_support_component] using D.locallyFinite_component

/-- A family of cycles on `X`, each supported on its own `Z_i`, has a locally finite sum. -/
private theorem locallyFiniteSupport_finsum_component (c : D.Index → AlgebraicCycle X ℤ)
    (hsub : ∀ i, Function.support (c i) ⊆ (D.component i).support) :
    LocallyFiniteSupport fun x ↦ ∑ᶠ i, c i x :=
  locallyFiniteSupport_finsum _ D.locallyFinite_support_component (fun i ↦ c i)
    (fun i ↦ (c i).locallyFiniteSupport) hsub

/-- The cycle `ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i)` on the
prime divisor `Z_i`: the `i`-th summand of the left hand side of the key formula, before
pushing forward to `X`. -/
def componentDifference (i : D.Index) : AlgebraicCycle (D.component i).subscheme ℤ :=
  D.orderL i • D.restrictedDivisorN i - D.orderN i • D.restrictedDivisorL i

/-- The coefficient of `D.componentDifference i` at `z` is
`ord_{B_i}(f_i) · div_{N|Z_i}(t_i|Z_i)(z) - ord_{B_i}(g_i) · div_{L|Z_i}(s_i|Z_i)(z)`. -/
@[simp]
theorem componentDifference_apply (i : D.Index) (z : (D.component i).subscheme) :
    D.componentDifference i z =
      D.orderL i * D.restrictedDivisorN i z - D.orderN i * D.restrictedDivisorL i z := by
  show D.orderL i • D.restrictedDivisorN i z - D.orderN i • D.restrictedDivisorL i z = _
  simp

variable (C : ChowSituation.{u}) (p : X ⟶ C.S)

/-- The coefficient at `x` of the left hand side of the key formula: the locally finite sum over
`i` of the pushforwards to `X` of
`ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i)`. -/
def leftCoeff (x : X) : ℤ :=
  ∑ᶠ i : D.Index,
    closedSubschemeCyclePushforward C p (D.component i) (D.componentDifference i) x

/-- The left hand side of the key formula has locally finite support: the family `{Z_i}` is
locally finite and each summand is supported on its own `Z_i`. -/
theorem locallyFiniteSupport_leftCoeff : LocallyFiniteSupport (D.leftCoeff C p) :=
  D.locallyFiniteSupport_finsum_component
    (fun i ↦ closedSubschemeCyclePushforward C p (D.component i) (D.componentDifference i))
    fun i ↦ support_closedSubschemeCyclePushforward_subset C p (D.component i)
      (D.componentDifference i)

/-- The left hand side of the key formula, as a cycle on `X`. -/
def leftCycle : AlgebraicCycle X ℤ where
  toFun := D.leftCoeff C p
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' x _ := D.locallyFiniteSupport_leftCoeff C p x

/-- The coefficient of `D.leftCycle C p` at `x` is `D.leftCoeff C p x`. -/
@[simp]
theorem leftCycle_apply (x : X) : D.leftCycle C p x = D.leftCoeff C p x := rfl

variable [LocallyOfFiniteType p]

/-- The coefficient at `x` of the right hand side of the key formula: the locally finite sum
over `i` of the pushforwards to `X` of the principal divisors
`div_{Z_i}(∂_{B_i}(f_i, g_i))`. -/
def tameSymbolCoeff (x : X) : ℤ :=
  principalDivisorFamilyCoefficient C p D.component D.isIntegral_component D.tameSymbol x

/-- The right hand side of the key formula has locally finite support. -/
theorem locallyFiniteSupport_tameSymbolCoeff : LocallyFiniteSupport (D.tameSymbolCoeff C p) :=
  D.locallyFiniteSupport_finsum_component
    (fun i ↦ principalDivisorPushforward C p (D.component i) (D.isIntegral_component i)
      (D.tameSymbol i))
    fun i ↦ support_principalDivisorPushforward_subset C p (D.component i)
      (D.isIntegral_component i) (D.tameSymbol i)

/-- The right hand side of the key formula, as a cycle on `X`. -/
def tameSymbolCycle : AlgebraicCycle X ℤ where
  toFun := D.tameSymbolCoeff C p
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' x _ := D.locallyFiniteSupport_tameSymbolCoeff C p x

/-- The coefficient of `D.tameSymbolCycle C p` at `x` is `D.tameSymbolCoeff C p x`. -/
@[simp]
theorem tameSymbolCycle_apply (x : X) : D.tameSymbolCycle C p x = D.tameSymbolCoeff C p x := rfl

/-- **Stacks 0AYC, the key formula.** The cycle

`∑ (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))`

is equal to the cycle `∑ (Z_i → X)_* div_{Z_i}(∂_{B_i}(f_i, g_i))`.

This is a predicate on the data, not a theorem about it, and it is not proved here. Its Stacks
proof reduces, after changing the chosen generators `s_i` and `t_i` by units (Divisors 02SH and
the bilinearity of the tame symbol), to the Key Lemma Stacks 0EAX on a two-dimensional
Noetherian local domain, which is available as
`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`; the passage from the equality of
cycles to the equality of coefficients at a codimension-two point is
`Stacks.Chow.KeyFormulaData.keyFormula_iff_forall_component_coheight_one`. What is not available
is the dictionary identifying the data of the family through a codimension-two point `x` with
the height-one primes of `𝒪_{X, x}` and their tame symbols. Statements that depend on the
formula take it as a hypothesis, as
`Stacks.Chow.isRationallyEquivalentToZero_of_keyFormula` does. -/
def KeyFormula : Prop :=
  D.leftCycle C p = D.tameSymbolCycle C p

/-- The key formula read one coefficient at a time. -/
theorem keyFormula_iff_forall :
    D.KeyFormula C p ↔ ∀ x : X, D.leftCoeff C p x = D.tameSymbolCoeff C p x :=
  ⟨fun h x ↦ by rw [← D.leftCycle_apply C p x, h, D.tameSymbolCycle_apply],
    fun h ↦ Function.locallyFinsuppWithin.ext h⟩

/-- On an integral scheme of delta-dimension `n` each prime divisor `Z_i` of the family has
delta-dimension `n - 1`.

The dimension function `d` on `X` whose underlying function is
`Stacks.Chow.relativeDimension` is taken as a hypothesis, as everywhere else in this
development: producing it is Stacks 02JW, which this repository does not have. -/
theorem schemeDeltaDimension_component [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) (i : D.Index) :
    schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((n - 1 : ℤ) : EInt) :=
  schemeDeltaDimension_integralComponentAt_of_coheight_one C p hn hd
    (D.coheight_componentPoint i)

/-- The left hand side of the key formula is a cycle of delta-dimension `n - 2` on an integral
scheme of delta-dimension `n`: a nonzero coefficient occurs at the image of a point of
codimension one of some `Z_i`, and `Z_i` has delta-dimension `n - 1`.

This is what makes the key formula a statement in `CH_{n-2}(X)`, and it is what lets a consumer
build the element of `Stacks.Chow.CycleGroup C p (n - 2)` that
`Stacks.Chow.isRationallyEquivalentToZero_leftCycle` asks for. -/
theorem leftCycle_mem_cyclesOfDimension [IsIntegral X] {n : ℤ}
    (hn : schemeDeltaDimension C p = (n : EInt)) {d : DimensionFunction X}
    (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y) :
    D.leftCycle C p ∈ cyclesOfDimension C p (n - 2) := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i : D.Index,
      closedSubschemeCyclePushforward C p (D.component i) (D.componentDifference i) x ≠ 0 := by
    by_contra! h
    exact hx (finsum_eq_zero_of_forall_eq_zero h)
  obtain ⟨z, rfl⟩ : ∃ z : (D.component i).subscheme, (D.component i).subschemeι.base z = x := by
    by_contra! h
    exact hi (closedSubschemeCyclePushforward_apply_of_notMem_range C p _ _
      fun ⟨z, hz⟩ ↦ h z hz)
  rw [closedSubschemeCyclePushforward_apply, D.componentDifference_apply] at hi
  have hcoh : Order.coheight z = 1 := by
    by_cases hN : D.restrictedDivisorN i z = 0
    · by_cases hL : D.restrictedDivisorL i z = 0
      · simp [hN, hL] at hi
      · exact D.coheight_of_restrictedDivisorL i z hL
    · exact D.coheight_of_restrictedDivisorN i z hN
  have _ := D.isIntegral_component i
  have hd' : ∀ y : (D.component i).subscheme,
      (d.compClosedEmbedding (D.component i).subschemeι.isClosedEmbedding) y =
        relativeDimension C.dimensionFunction ((D.component i).subschemeι ≫ p) y := fun y ↦ by
    rw [DimensionFunction.compClosedEmbedding_apply, hd,
      relativeDimension_comp_closedImmersion]
  have key := deltaDimension_closure_singleton_of_coheight_one C
    ((D.component i).subschemeι ≫ p) (D.schemeDeltaDimension_component C p hn hd i) hd' hcoh
  rw [deltaDimension_closure_singleton] at key
  rw [← relativeDimension_comp_closedImmersion C.dimensionFunction (D.component i).subschemeι p z,
    key]
  ring

end KeyFormulaData

/-- **Stacks 0AYC, as chapter 42 uses it.** Granting the key formula, a cycle whose
coefficients are given by the left hand side is rationally equivalent to zero: the right hand
side exhibits it as a locally finite sum of principal divisors on the prime divisors `Z_i`,
which is Stacks 02RW's definition of rational equivalence to zero.

This is the step by which the key formula enters Stacks 02TH (commutativity of intersection with
two invertible sheaves), 02TI (intersection with an invertible sheaf factors through rational
equivalence), 02TM and 02TO (the Gysin homomorphism factors through rational equivalence). -/
theorem isRationallyEquivalentToZero_of_keyFormula (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (D : KeyFormulaData X) (hKey : D.KeyFormula C p)
    (k : ℤ) (hdim : ∀ i : D.Index,
      schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C p k) (hα : ∀ x : X, α.1 x = D.leftCoeff C p x) :
    IsRationallyEquivalentToZero C p k α := by
  refine ⟨D.Index, D.component, D.isIntegral_component, hdim,
    D.locallyFinite_support_component, D.tameSymbol, fun x ↦ ?_⟩
  rw [hα x]
  exact (D.keyFormula_iff_forall C p).1 hKey x

/-- **Stacks 0AYC in the grading the source states it in.** On an integral scheme of
delta-dimension `n`, granting the key formula, the `(n - 2)`-cycle presented by its left hand
side is rationally equivalent to zero.

The cycle `α` exists by `Stacks.Chow.KeyFormulaData.leftCycle_mem_cyclesOfDimension`. The
dimension function `d` is the hypothesis standing in for Stacks 02JW, as everywhere else in this
development. -/
theorem isRationallyEquivalentToZero_leftCycle (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral X] (D : KeyFormulaData X)
    (hKey : D.KeyFormula C p) {n : ℤ} (hn : schemeDeltaDimension C p = (n : EInt))
    {d : DimensionFunction X} (hd : ∀ y, d y = relativeDimension C.dimensionFunction p y)
    (α : CycleGroup C p (n - 2)) (hα : ∀ x : X, α.1 x = D.leftCoeff C p x) :
    IsRationallyEquivalentToZero C p (n - 2) α :=
  isRationallyEquivalentToZero_of_keyFormula C p D hKey (n - 2)
    (fun i ↦ by
      rw [show (n - 2 + 1 : ℤ) = n - 1 by ring]
      exact D.schemeDeltaDimension_component C p hn hd i) α hα

end Stacks.Chow

end
