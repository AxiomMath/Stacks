module

public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.LocalReduction
public import StacksFrontier.AlgebraicGeometry.Chow.TameSymbol

/-!
# Tying the tame symbols of the key formula to the rest of its data

`Stacks.Chow.KeyFormulaData` records the data of Stacks 0AYB at the level of cycles, and its
field `tameSymbol` is free: nothing relates it to `orderL`, `orderN`, `restrictedDivisorL` and
`restrictedDivisorN`. That is why `Stacks.Chow.KeyFormulaData.KeyFormula` fails for some of its
data, as `Stacks.Chow.principalDivisorPushforward_eq_zero_of_forall_keyFormula` shows.

This file removes that freedom. In the situation of Stacks 0AYB the tame symbol attached to the
member `Z_i` is `∂_{B_i}(f_i, g_i)`, where `B_i = 𝒪_{X, ξ_i}` and `f_i`, `g_i` are the rational
functions with `s = f_i s_i` and `t = g_i t_i`, and the two integers are the orders of vanishing
of the same two rational functions:

`ord_{Z_i, L}(s) = ord_{B_i}(f_i)` and `ord_{Z_i, N}(t) = ord_{B_i}(g_i)`.

All three quantities are therefore determined by the pair `(f_i, g_i)`, and
`Stacks.Chow.KeyFormulaLocalData` is `Stacks.Chow.KeyFormulaData` together with that pair and the
three equations. The tame symbol used is the canonical one: the local ring at a codimension-one
point of a locally Noetherian scheme is a one-dimensional Noetherian local ring, so Stacks 0EAH
applies to it as `Stacks.Chow.tameSymbolAtCoheightOne`, and `Stacks.Chow.tameSymbolAt` reads the
result as a rational function on `Z_i`. No field of `Stacks.Chow.KeyFormulaLocalData` is a
Prop-valued
stand-in for a result: the three new conditions are equations between quantities the repository
already constructs.

## What this is still not enough for

Constraining the tame symbols does not make the key formula provable, and the obstruction has
moved rather than disappeared. `Stacks.Chow.KeyFormulaLocalData.singleComponentLocal` is a
constrained datum with one member, vanishing restricted divisors and the canonical tame symbol
of a prescribed pair `(f, g)`; its left hand side is identically zero, so
`Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula`
derives from "the key formula holds for every term of `KeyFormulaLocalData`" that the principal
divisor of `∂_ξ(f, g)` pushes forward to the zero cycle for every codimension-one point `ξ` and
every pair of nonzero rational functions.

That is not expected to hold, and the reason is precise: the source's proof evaluates the
coefficient at a codimension-two point `x` as a sum over *all* height-one primes of
`𝒪_{X, x}` — the sum that vanishes by the Key Lemma Stacks 0EAX
(`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`) — and it is entitled to do so
because the family `{Z_i}` of Stacks 0AYB is chosen to contain every prime divisor along which
`s` or `t` fails to generate, so that the omitted primes contribute nothing. That choice is a
condition on the invertible modules `L`, `N` and the sections `s`, `t`, and a term of
`Stacks.Chow.KeyFormulaData` carries none of them. So the condition cannot be stated at the
level of cycles at all, and neither can the restricted divisors be tied to the data: that needs
`div_{N|Z_i}(t_i|Z_i)`, the divisor of the restriction of a meromorphic section to a prime
divisor. Stacks 0AYC can only be carried by a structure holding the sheaf-level situation of
Stacks 0AYB. That structure is `Stacks.Chow.KeyFormulaSituation`, which carries the two
invertible modules, their meromorphic sections, the family and the chosen generators, and whose
field `isCoordinateAt_one_of_notMem` is the condition on the family; the divisor of the
restriction of a meromorphic section to a prime divisor is `Stacks.Chow.restrictedDivisor`.

## Main definitions

* `Stacks.Chow.canonicalTameSymbolAt` — the tame symbol of Stacks 0EAH at a codimension-one
  point, read as a map `R(X)^* × R(X)^* → R(Z_ξ)^*`.
* `Stacks.Chow.KeyFormulaLocalData` — key-formula data whose orders of vanishing and tame
  symbols are the ones determined by a family of pairs of rational functions.
* `Stacks.Chow.KeyFormulaLocalData.singleComponentLocal` — one prime divisor, vanishing
  restricted divisors, a prescribed pair of rational functions.

## Main results

* `Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula` —
  the key formula read as a statement about arbitrary constrained data still collapses, so
  tying the tame symbols is not by itself enough to carry Stacks 0AYC.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
* [Stacks Project, Tag 0EAX](https://stacks.math.columbia.edu/tag/0EAX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The canonical tame symbol at a codimension-one point -/

/-- **The tame symbol `∂_{𝒪_{X, ξ}}(f, g)` of two nonzero rational functions, as a nonzero
rational function on `Z_ξ`.** This is `Stacks.Chow.tameSymbolAt` applied to
`Stacks.Chow.tameSymbolAtCoheightOne`, the symbol Stacks 0EAH attaches to the one-dimensional
Noetherian local ring `𝒪_{X, ξ}`, and it is exactly the shape the field
`Stacks.Chow.KeyFormulaData.tameSymbol` takes. -/
def canonicalTameSymbolAt {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {ξ : X}
    (hξ : Order.coheight ξ = 1) (f g : (rationalFunctions X)ˣ) :
    (rationalFunctions (integralComponentAt ξ).subscheme)ˣ :=
  tameSymbolAt ξ (tameSymbolAtCoheightOne hξ) f g

/-- The order of vanishing at `ξ` of a nonzero rational function on an integral scheme, read
through the identification of `Stacks.Chow.rationalFunctions` with the function field. -/
def ordAtOfRationalFunction (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
    (f : (rationalFunctions X)ˣ) (ξ : X) : ℤ :=
  X.ord ((rationalFunctionsEquivFunctionField X).1 (f : rationalFunctions X)) ξ

/-! ### Key-formula data with constrained tame symbols -/

/-- **Key-formula data whose orders of vanishing and tame symbols are determined by the local
ratios.** In the situation of Stacks 0AYB the member `Z_i` of the family carries the two
rational functions `f_i` and `g_i` defined by `s = f_i s_i` and `t = g_i t_i`, and all three of
the quantities `ord_{Z_i, L}(s)`, `ord_{Z_i, N}(t)` and `∂_{B_i}(f_i, g_i)` are computed from
them: the first two as orders of vanishing at `ξ_i`, the third as the tame symbol of
Stacks 0EAH on `B_i = 𝒪_{X, ξ_i}`.

This structure is `Stacks.Chow.KeyFormulaData` together with that pair of rational functions for
each `i` and the three resulting equations. Every new field is either data of the source or an
equation between quantities this repository constructs; none stands in for a missing result.

The restricted divisors remain free, because `div_{N|Z_i}(t_i|Z_i)` is not available at the
level of cycles, and so does the condition of Stacks 0AYB that `s` and `t` generate along every
prime divisor outside the family, because that condition mentions the invertible modules and
their sections. Both are needed for the key formula; see
`Stacks.Chow.principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula`. -/
structure KeyFormulaLocalData (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] extends
    KeyFormulaData X where
  /-- The rational function `f_i` of the equation `s = f_i s_i`. -/
  ratioL : Index → (rationalFunctions X)ˣ
  /-- The rational function `g_i` of the equation `t = g_i t_i`. -/
  ratioN : Index → (rationalFunctions X)ˣ
  /-- `ord_{Z_i, L}(s) = ord_{B_i}(f_i)`. -/
  orderL_eq : ∀ i, orderL i = ordAtOfRationalFunction X (ratioL i) (componentPoint i)
  /-- `ord_{Z_i, N}(t) = ord_{B_i}(g_i)`. -/
  orderN_eq : ∀ i, orderN i = ordAtOfRationalFunction X (ratioN i) (componentPoint i)
  /-- The tame symbol is `∂_{B_i}(f_i, g_i)`. -/
  tameSymbol_eq : ∀ i,
    tameSymbol i = canonicalTameSymbolAt (coheight_componentPoint i) (ratioL i) (ratioN i)

namespace KeyFormulaLocalData

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **One prime divisor with a prescribed pair of rational functions.** The orders of vanishing
are the ones the pair determines, the restricted divisors vanish and the tame symbol is the
canonical one, so every field of `Stacks.Chow.KeyFormulaLocalData` holds by definition. The left
hand side of the key formula is identically zero. -/
def singleComponentLocal {x : X} (hx : Order.coheight x = 1)
    (f g : (rationalFunctions X)ˣ) : KeyFormulaLocalData X where
  Index := PUnit.{u + 1}
  componentPoint _ := x
  coheight_componentPoint _ := hx
  componentPoint_injective a b _ := Subsingleton.elim a b
  locallyFinite_component := locallyFinite_of_finite _
  orderL _ := ordAtOfRationalFunction X f x
  orderN _ := ordAtOfRationalFunction X g x
  restrictedDivisorL _ := 0
  restrictedDivisorN _ := 0
  coheight_of_restrictedDivisorL _ _ h := absurd rfl h
  coheight_of_restrictedDivisorN _ _ h := absurd rfl h
  tameSymbol _ := canonicalTameSymbolAt hx f g
  ratioL _ := f
  ratioN _ := g
  orderL_eq _ := rfl
  orderN_eq _ := rfl
  tameSymbol_eq _ := rfl

variable (C : ChowSituation.{u}) (p : X ⟶ C.S)

/-- The left hand side of the key formula for `singleComponentLocal hx f g` is zero at every
point. -/
@[simp]
theorem leftCoeff_singleComponentLocal {x : X} (hx : Order.coheight x = 1)
    (f g : (rationalFunctions X)ˣ) (y : X) :
    (singleComponentLocal hx f g).leftCoeff C p y = 0 := by
  have hdiff : ∀ i, (singleComponentLocal hx f g).componentDifference i = 0 := fun _ ↦ by
    show _ • (0 : AlgebraicCycle _ ℤ) - _ • (0 : AlgebraicCycle _ ℤ) = 0
    simp
  show (∑ᶠ i, closedSubschemeCyclePushforward C p
    ((singleComponentLocal hx f g).component i)
      ((singleComponentLocal hx f g).componentDifference i) y) = 0
  simp only [hdiff, closedSubschemeCyclePushforward_zero_apply, finsum_zero]

/-- The tame-symbol side of the key formula for `singleComponentLocal hx f g` is the pushforward
of the principal divisor of `canonicalTameSymbolAt hx f g` on the integral component at `x`. -/
@[simp]
theorem tameSymbolCoeff_singleComponentLocal [LocallyOfFiniteType p] {x : X}
    (hx : Order.coheight x = 1) (f g : (rationalFunctions X)ˣ) (y : X) :
    (singleComponentLocal hx f g).tameSymbolCoeff C p y =
      principalDivisorPushforward C p (integralComponentAt x)
        (isIntegral_integralComponentAt x) (canonicalTameSymbolAt hx f g) y := by
  rw [(singleComponentLocal hx f g).tameSymbolCoeff_eq_finsum C p]
  exact @finsum_unique _ _ _ (inferInstanceAs (Unique PUnit.{u + 1})) _

end KeyFormulaLocalData

/-- **Tying the tame symbols to the local ratios is not by itself enough to carry
Stacks 0AYC.** If `Stacks.Chow.KeyFormulaData.KeyFormula` held for every term of
`Stacks.Chow.KeyFormulaLocalData` — that is, for every family whose orders of vanishing and tame
symbols are the ones its local ratios determine — then for every codimension-one point `ξ` of
`X` and every pair `f`, `g` of nonzero rational functions the principal divisor of the tame
symbol `∂_{𝒪_{X, ξ}}(f, g)` would push forward to the zero cycle.

The mechanism is that two further constraints of Stacks 0AYB are still missing. The restricted
divisors are free, so taking them zero makes the left hand side vanish; and the family is not
required to contain every prime divisor along which `s` or `t` fails to generate, so a family
with a single member is admissible. The source's proof needs both: it computes the coefficient
at a codimension-two point `x` as the sum over *all* height-one primes of `𝒪_{X, x}`, which is
zero by the Key Lemma Stacks 0EAX
(`Stacks.Chow.finsum_fracTameSymbolOrderAt_canonical_eq_zero`), after reducing to the case where
the chosen generators are restrictions of trivializations, which is what makes the restricted
divisors vanish.

Neither constraint can be imposed on a term of `Stacks.Chow.KeyFormulaData`: both mention the
invertible modules `L` and `N` and their meromorphic sections, and the data of that structure
mention neither. So Stacks 0AYC needs a structure holding the sheaf-level situation of
Stacks 0AYB. -/
theorem principalDivisorPushforward_canonicalTameSymbol_eq_zero_of_forall_keyFormula
    (C : ChowSituation.{u}) {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (h : ∀ D : KeyFormulaLocalData X, D.KeyFormula C p) {x : X} (hx : Order.coheight x = 1)
    (f g : (rationalFunctions X)ˣ) :
    principalDivisorPushforward C p (integralComponentAt x) (isIntegral_integralComponentAt x)
      (canonicalTameSymbolAt hx f g) = 0 := by
  have hk := (KeyFormulaData.keyFormula_iff_forall _ C p).1
    (h (KeyFormulaLocalData.singleComponentLocal hx f g))
  refine Function.locallyFinsuppWithin.ext fun y ↦ ?_
  have hy := hk y
  rw [KeyFormulaLocalData.leftCoeff_singleComponentLocal,
    KeyFormulaLocalData.tameSymbolCoeff_singleComponentLocal] at hy
  exact hy.symm

end Stacks.Chow

end
