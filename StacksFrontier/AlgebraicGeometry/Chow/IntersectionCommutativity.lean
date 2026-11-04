module

public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent
public import StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.TrivialChernClass

/-!
# Commutativity of first Chern class intersections, and the integral case of Stacks 02TI

Let `X` be an integral scheme locally of finite type over the base scheme `S` of chapter 42 of
the Stacks Project, of delta-dimension `n = k + 2`, and let `L` and `N` be invertible modules on
`X` with nonzero meromorphic sections `s` and `t`. Stacks 02TH asserts

  `c₁(N) ∩ div_L(s) = c₁(L) ∩ div_N(t)`  in  `A_{n-2}(X)`,

and its proof is one step: the two sides are represented, on the locally finite family `{Z_i}` of
prime divisors of the key formula, by the two halves of the left hand side of Stacks 0AYC, whose
difference the key formula exhibits as a locally finite sum of principal divisors. That step is
`Stacks.Chow.mk_eq_mk_of_keyFormula`, and this file assembles it with the component formula
`Stacks.Chow.firstChernClassCap_finsum` for the cap product.

Specialising `N` to the structure sheaf `𝒪_X` with the meromorphic section given by a rational
function `f ∈ R(X)^*` gives the integral case of Stacks 02TI: then the chosen generators of
`𝒪_X` at the generic points `ξ_i` are units, so the restricted divisors
`div_{𝒪_{Z_i}}(t_i|_{Z_i})` all vanish while the orders `ord_{B_i}(f)` do not, and
`div_𝒪(f) = div_X(f)`. So `c₁(L) ∩ div_X(f) = c₁(𝒪_X) ∩ div_L(s)`, and the right hand side is zero
by the second half of Stacks 02SP. This is
`Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula`; it is the case to which the proof of
Stacks 02TI reduces the general statement, and the reduction itself is the one step still
missing (see the implementation notes).

## Main results

* `Stacks.Chow.firstChernClassCap_comm_of_keyFormula` — the commutativity of **Stacks 02TH**,
  granting the key formula. Stacks 02TH itself, with that hypothesis and the divisor cycles
  discharged, is `Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm` in
  `StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge`.
* `Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula` — **the integral case of Stacks 02TI**:
  intersecting the principal divisor of a rational function on an integral scheme with a first
  Chern class gives zero.

## Implementation notes

### The parameters threaded, and why

Three inputs of the source are absent from this repository and are carried as explicit
parameters, in the way established by
`StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass` and
`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence`:

* the component rules `chernL` and `chernN` of the cap product, standing in for Stacks 02SO —
  whose component input is the divisor cycle of Stacks 02SJ, resting on the absent Stacks 02SF
  and 0BE6;
* the key formula `Stacks.Chow.KeyFormulaData.KeyFormula` of Stacks 0AYC, which is a statement
  rather than a theorem here, since its proof bottoms out in Stacks 0EAX;
* the cycles `divL` and `divN` together with their presentations `∑_i ord_{B_i}(f_i) [Z_i]` and
  `∑_i ord_{B_i}(g_i) [Z_i]`, standing in for `div_L(s)` and `div_N(t)` of Stacks 02SJ; and the
  hypotheses `hchernL`, `hchernN` identifying the component rules on the `Z_i` with the restricted
  divisors of the key formula data.

Each of these is a quantity the source constructs and names; substituting the constructions, once
they land, recovers the statement of Stacks 02TH verbatim, so the statements below are
generalizations of it rather than weakenings. The hypotheses are also indispensable: for an
arbitrary pair of component rules the two sides of Stacks 02TH have no reason to agree, since
the cap product is built from the rule and nothing else.

The dimension function of Stacks 02JW is *not* a parameter: it is supplied by
`Stacks.Chow.deltaDimensionFunction`.

### The grading

The source states Stacks 02TH for `dim_δ(X) = n` with the conclusion in `A_{n-2}(X)`. Here the
hypothesis reads `dim_δ(X) = k + 2` and the conclusion lands in `A_k(X)`, which is the same
statement with `k = n - 2` and avoids transporting the cap product along `(n - 2) + 1 = n - 1`.

### The form of the `@[stacks 02TI]` attribute, and where `@[stacks 02TH]` sits

No declaration in this file carries Stacks 02TH. Every parameter listed above is discharged in
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge`: the key formula of Stacks
0AYC holds for the situation of Stacks 0AYB attached to the two sections, the canonical
component rules of Stacks 02SO may be used in place of the prescribed ones because the cap
product sees a rule only through the classes of its values, and the two divisor cycles are the
divisors of the sections themselves. So the attribute sits on
`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm` there, which assumes nothing
beyond the hypotheses of the source, and
`Stacks.Chow.firstChernClassCap_comm_of_keyFormula` below is the one step of its proof.

`Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula` carries Stacks 02TI restricted to the
integral case `α = div_X(f)`, which is the case the source's proof reduces the general statement
to. The reduction itself, by proper pushforward along `⨿ W_j ⟶ X`, needs Stacks 02SU and through
it Stacks 0GU8 and 02S2, so the general vanishing remains a hypothesis in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent`, where the
descended operation carries the tag.

## References

* [Stacks Project, Tag 02TH](https://stacks.math.columbia.edu/tag/02TH)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] {k : ℤ} (hn : schemeDeltaDimension C p = ((k + 2 : ℤ) : EInt))
  (D : KeyFormulaData X)

include hn

/-- On an integral scheme of delta-dimension `k + 2` each prime divisor `Z_i` of the family of
the key formula has delta-dimension `k + 1`, so it is one of the integral components over which
the cap product of Stacks 02SO is computed.

This is `Stacks.Chow.KeyFormulaData.schemeDeltaDimension_component` with the dimension function
of Stacks 02JW supplied by `Stacks.Chow.deltaDimensionFunction`. -/
theorem KeyFormulaData.schemeDeltaDimension_component_add_one (i : D.Index) :
    schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) := by
  have h := D.schemeDeltaDimension_component C p hn (deltaDimensionFunction_apply C p) i
  rwa [show (k + 2 - 1 : ℤ) = k + 1 from by ring] at h

/-- **The commutativity of Stacks 02TH, granting the key formula.** On an integral scheme of
delta-dimension `k + 2`, intersecting the divisor cycle of a nonzero meromorphic section of one
invertible module with the first Chern class of the other gives the same class in `A_k(X)`, in
either order.

Granting the key formula of Stacks 0AYC for the data `D`, this is immediate: the two sides are
represented by the two halves of its left hand side, so their difference is a locally finite sum
of principal divisors on the prime divisors `Z_i`. The component rules of the two invertible
modules, the key formula itself and the two divisor cycles with their presentations by the family
`{Z_i}` are explicit parameters; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity`.

The `@[stacks 02TH]` attribute sits on
`Stacks.Chow.firstChernClassCapOfInvertible_divisorCycle_comm`, where every one of those
parameters is discharged; this is the step its proof is made of. -/
@[stacks 02TH "granting the key formula 0AYC and the divisor cycles of 02SJ"]
theorem firstChernClassCap_comm_of_keyFormula (hKey : D.KeyFormula C p)
    (chernL chernN : FirstChernComponentCycleRule C p k)
    (hchernL : ∀ (i : D.Index) (hW : IsIntegral (D.component i).subscheme)
      (hDim : schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      (chernL (D.component i) hW hDim).1 = D.restrictedDivisorL i)
    (hchernN : ∀ (i : D.Index) (hW : IsIntegral (D.component i).subscheme)
      (hDim : schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      (chernN (D.component i) hW hDim).1 = D.restrictedDivisorN i)
    (divL divN : CycleGroup C p (k + 1))
    (hdivL : ∀ x : X, divL.1 x = ∑ᶠ i, D.orderL i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x)
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, D.orderN i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x) :
    firstChernClassCap C p k chernN divL = firstChernClassCap C p k chernL divN := by
  have hdim := D.schemeDeltaDimension_component_add_one C p hn
  obtain ⟨βN, hβN, hβNcoeff⟩ := firstChernClassCap_finsum C p k chernN D.component
    D.isIntegral_component hdim D.locallyFinite_support_component D.orderL divL hdivL
  obtain ⟨βL, hβL, hβLcoeff⟩ := firstChernClassCap_finsum C p k chernL D.component
    D.isIntegral_component hdim D.locallyFinite_support_component D.orderN divN hdivN
  have hc : ∀ (chern : FirstChernComponentCycleRule C p k) (i : D.Index) R,
      (chern (D.component i) (D.isIntegral_component i) (hdim i)).1 = R →
      (firstChernComponentCycle C p k chern (D.component i) (D.isIntegral_component i)
          (hdim i)).1 = closedSubschemeCyclePushforward C p (D.component i) R :=
    fun chern i R h ↦ by rw [← h]; rfl
  rw [hβN, hβL]
  refine mk_eq_mk_of_keyFormula C p D hKey hdim βN βL (fun x ↦ ?_) fun x ↦ ?_
  · rw [hβNcoeff x]
    exact finsum_congr fun i ↦ by rw [hc chernN i _ (hchernN i _ _)]
  · rw [hβLcoeff x]
    exact finsum_congr fun i ↦ by rw [hc chernL i _ (hchernL i _ _)]

/-- **The integral case of Stacks 02TI.** On an integral scheme of delta-dimension `k + 2`,
intersecting the principal divisor of a rational function with the first Chern class of an
invertible module gives zero in `A_k(X)`.

This is Stacks 02TH applied with the second invertible module the structure sheaf `𝒪_X` and its
meromorphic section the rational function `f`: the chosen generators of `𝒪_X` at the generic
points `ξ_i` are then units, so the restricted divisors `div_{𝒪_{Z_i}}(t_i|_{Z_i})` vanish, which
is the hypothesis `hzeroN`, while the orders `ord_{B_i}(f)` presenting `div_𝒪(f) = div_X(f)` need
not. The resulting class `c₁(𝒪_X) ∩ div_L(s)` vanishes by
`Stacks.Chow.firstChernClassCap_trivialChernComponentCycleRule`, the second half of Stacks 02SP.

The proof of Stacks 02TI reduces its general statement to this case by proper pushforward along
`⨿ W_j ⟶ X`, which needs Stacks 02SU and through it the proper pushforward of Chow classes of
Stacks 0GU8 and 02S2. That reduction is the one step not available here, which is why the
general vanishing is a hypothesis in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent`. -/
@[stacks 02TI "the integral case α = div_X(f), granting the key formula 0AYC"]
theorem firstChernClassCap_eq_zero_of_keyFormula (hKey : D.KeyFormula C p)
    (hzeroN : ∀ i : D.Index, D.restrictedDivisorN i = 0)
    (chernL : FirstChernComponentCycleRule C p k)
    (hchernL : ∀ (i : D.Index) (hW : IsIntegral (D.component i).subscheme)
      (hDim : schemeDeltaDimension C ((D.component i).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      (chernL (D.component i) hW hDim).1 = D.restrictedDivisorL i)
    (divL divN : CycleGroup C p (k + 1))
    (hdivL : ∀ x : X, divL.1 x = ∑ᶠ i, D.orderL i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x)
    (hdivN : ∀ x : X, divN.1 x = ∑ᶠ i, D.orderN i *
      (cycleAssociatedToClosedSubscheme C p (D.component i).subschemeι (k + 1)).1 x) :
    firstChernClassCap C p k chernL divN = 0 := by
  rw [← firstChernClassCap_comm_of_keyFormula C p hn D hKey chernL
    (trivialChernComponentCycleRule C p k) hchernL
    (fun i _ _ ↦ by rw [hzeroN i]; rfl) divL divN hdivL hdivN,
    firstChernClassCap_trivialChernComponentCycleRule]
  rfl

end Stacks.Chow

end
