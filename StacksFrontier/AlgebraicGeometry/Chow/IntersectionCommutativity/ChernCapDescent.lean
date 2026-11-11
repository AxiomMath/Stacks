module

public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence

/-!
# Descending the first Chern class cap product to Chow groups

Stacks 02TI asserts that the cap product `c₁(L) ∩ - : Z_{k+1}(X) ⟶ A_k(X)` of Stacks 02SO kills
every cycle rationally equivalent to zero, so that it descends to an operation

  `c₁(L) ∩ - : A_{k+1}(X) ⟶ A_k(X)`

on Chow groups, and the Stacks text then writes `c₁(L)^s ∩ -` for its iterates. This file carries
out the descent and builds the iterates.

The cap product of `StacksFrontier.AlgebraicGeometry.Chow.FirstChernClass` is
`Stacks.Chow.IntegralComponentRule.extendChow` of the component rule
`Stacks.Chow.firstChernCapRule`, so the descent is an instance of
`Stacks.Chow.IntegralComponentRule.descend`, exactly as the file introducing that construction
anticipated.

## Main definitions

* `Stacks.Chow.FirstChernClassCapFactorsThroughRationalEquivalence` — the assertion of Stacks
  02TI for a component rule.
* `Stacks.Chow.firstChernClassCapOnChow` — the cap product descended to Chow groups.
* `Stacks.Chow.ChernCapOperator` — a component rule in every degree whose cap product factors
  through rational equivalence: what an invertible module provides by Stacks 02SO and 02TI.
* `Stacks.Chow.iteratedChernCapOnChow` — the composite of such operations for a list of
  operators, the `c₁(L₁) ∩ ⋯ ∩ c₁(L_r) ∩ -` of the Stacks text.

## Main results

* `Stacks.Chow.firstChernClassCapOnChow_mk` — the descended operation agrees with the cap product
  on cycle representatives.
* `Stacks.Chow.eq_firstChernClassCapOnChow` — it is the unique such homomorphism.
* `Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff` — factoring through
  rational equivalence is *equivalent* to the existence of a descended map, so carrying it as a
  hypothesis loses nothing.
* `Stacks.Chow.firstChernClassCapOnChow_finsum` — the locally finite component formula, read on
  Chow classes.

## Implementation notes

### Why the vanishing is a hypothesis here

The cap product here is built from an arbitrary `Stacks.Chow.FirstChernComponentCycleRule`, and
an arbitrary rule on integral components has no reason to kill rational equivalences, so the
generic construction takes the vanishing as an argument. The hypothesis is not a weakening —
`Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff` says it is equivalent to
the existence of the descended operation.

For the component rule of an invertible module the vanishing is proved:
`Stacks.Chow.firstChernCapFactorsEverywhere` in
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapFactors` is Stacks 02TI with no
hypothesis, and `Stacks.Chow.firstChernClassCapChow` there is the descended operation of an
invertible module. Those two carry the `@[stacks 02TI]` attribute; nothing in this file does.

## References

* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (chern : FirstChernComponentCycleRule C p k)

/-! ### The descended cap product -/

/-- The assertion of Stacks 02TI for a component rule: intersecting with the first Chern class
kills every `(k+1)`-cycle rationally equivalent to zero, hence factors through rational
equivalence. For the component rule of an invertible module it is proved by
`Stacks.Chow.firstChernCapFactorsEverywhere`. -/
def FirstChernClassCapFactorsThroughRationalEquivalence : Prop :=
  ∀ α ∈ rationalEquivalences C p (k + 1), firstChernClassCap C p k chern α = 0

/-- The cap product factors through rational equivalence exactly when the rule on integral
components it is built from does. -/
theorem firstChernClassCapFactorsThroughRationalEquivalence_iff_firstChernCapRule :
    FirstChernClassCapFactorsThroughRationalEquivalence C p k chern ↔
      (firstChernCapRule C p k chern).FactorsThroughRationalEquivalence :=
  Iff.rfl

/-- Intersection with the first Chern class of a component rule, descended to Chow groups,
`c₁(L) ∩ - : A_{k+1}(X) ⟶ A_k(X)`, given that it factors through rational equivalence. For an
invertible module this is `Stacks.Chow.firstChernClassCapChow`, with the vanishing proved. -/
def firstChernClassCapOnChow
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern) :
    chowGroup C p (k + 1) →+ chowGroup C p k :=
  (firstChernCapRule C p k chern).descend h

/-- **Stacks 02TI.** The descended operation agrees with the cap product on cycle
representatives. -/
@[simp]
theorem firstChernClassCapOnChow_mk
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern)
    (α : CycleGroup C p (k + 1)) :
    firstChernClassCapOnChow C p k chern h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      firstChernClassCap C p k chern α :=
  rfl

/-- The descended operation, composed with the projection to the Chow group, is the cap product
on cycles. -/
theorem firstChernClassCapOnChow_comp_mk'
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern) :
    (firstChernClassCapOnChow C p k chern h).comp
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      firstChernClassCap C p k chern :=
  rfl

/-- **Stacks 02TI.** The descended operation is the only homomorphism of Chow groups agreeing
with the cap product on cycle representatives. -/
theorem eq_firstChernClassCapOnChow
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern)
    (F : chowGroup C p (k + 1) →+ chowGroup C p k)
    (hF : F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      firstChernClassCap C p k chern) :
    F = firstChernClassCapOnChow C p k chern h :=
  QuotientAddGroup.addMonoidHom_ext _
    (hF.trans (firstChernClassCapOnChow_comp_mk' C p k chern h).symm)

/-- **The hypothesis is exactly the descent.** The cap product factors through rational
equivalence precisely when it descends to a homomorphism of Chow groups, so carrying the
statement of Stacks 02TI as a hypothesis loses no information. -/
theorem firstChernClassCapFactorsThroughRationalEquivalence_iff :
    FirstChernClassCapFactorsThroughRationalEquivalence C p k chern ↔
      ∃ F : chowGroup C p (k + 1) →+ chowGroup C p k,
        F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
          firstChernClassCap C p k chern :=
  (firstChernCapRule C p k chern).factorsThroughRationalEquivalence_iff

/-- **Stacks 02SO, 02TI.** The locally finite component formula for the descended operation: on
the class of a cycle presented as `α = ∑ n_j [W_j]` its value is the class of the cycle whose
coefficients are `∑ n_j` times the component cycles of the `W_j`. -/
theorem firstChernClassCapOnChow_finsum
    (h : FirstChernClassCapFactorsThroughRationalEquivalence C p k chern) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C p k,
      firstChernClassCapOnChow C p k chern h
          (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
        QuotientAddGroup.mk β ∧
      ∀ x : X, β.1 x = ∑ᶠ j : J, n j *
        (firstChernComponentCycle C p k chern (W j) (hW j) (hDim j)).1 x := by
  obtain ⟨β, hβ, hcoeff⟩ := firstChernClassCap_finsum C p k chern W hW hDim hLocal n α hα
  exact ⟨β, by rw [firstChernClassCapOnChow_mk, hβ], hcoeff⟩

/-! ### Iterating the operation -/

/-- A *first Chern class cap operator* on `X`: a component rule of Stacks 02SO in every degree,
together with the assertion of Stacks 02TI that the resulting cap product factors through
rational equivalence.

This is what an invertible module on `X` provides by Stacks 02SJ (the divisor cycle of a
regular meromorphic section, which produces the component rule) and Stacks 02TI
(`Stacks.Chow.firstChernCapFactorsEverywhere`).
Bundling the two is what makes the iterates of the operation definable: iterating moves between
degrees, so a rule in a single degree is not enough. -/
structure ChernCapOperator (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] : Type u where
  /-- The component rule of Stacks 02SO in each degree. -/
  chern : (k : ℤ) → FirstChernComponentCycleRule C p k
  /-- The cap product factors through rational equivalence in each degree: Stacks 02TI. -/
  factors : ∀ k, FirstChernClassCapFactorsThroughRationalEquivalence C p k (chern k)

/-- The operation `A_{k+1}(X) ⟶ A_k(X)` a first Chern class cap operator performs. -/
def ChernCapOperator.capOnChow (O : ChernCapOperator C p) (k : ℤ) :
    chowGroup C p (k + 1) →+ chowGroup C p k :=
  firstChernClassCapOnChow C p k (O.chern k) (O.factors k)

/-- Transport an additive map out of a Chow group along an equality of degrees. Iterating the cap
product `r` times lands in degree `k + r`, which is the same integer as, but not the same term
as, the degree the recursion produces. -/
def chowGroupDegreeCast {k l m : ℤ} (h : k = l)
    (F : chowGroup C p l →+ chowGroup C p m) : chowGroup C p k →+ chowGroup C p m :=
  Eq.mp (congrArg (fun d ↦ chowGroup C p d →+ chowGroup C p m) h.symm) F

@[simp]
theorem chowGroupDegreeCast_rfl {k m : ℤ} (F : chowGroup C p k →+ chowGroup C p m) :
    chowGroupDegreeCast C p rfl F = F :=
  rfl

/-- **Stacks 02TI.** Repeated intersection with first Chern classes,
`A_{k+r}(X) ⟶ A_k(X)`, for a list of `r` first Chern class cap operators: the empty list acts as
the identity, and a nonempty list acts by the operator at its head after the intersections
specified by its tail. The Stacks text writes `c₁(L)^s ∩ -` for the case of a constant list. -/
def iteratedChernCapOnChow : (Os : List (ChernCapOperator C p)) → (k : ℤ) →
    chowGroup C p (k + (Os.length : ℤ)) →+ chowGroup C p k
  | [], k =>
      chowGroupDegreeCast C p (by simp) (AddMonoidHom.id (chowGroup C p k))
  | O :: Os, k =>
      chowGroupDegreeCast C p
        (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring)
        ((O.capOnChow C p k).comp (iteratedChernCapOnChow Os (k + 1)))

end Stacks.Chow

end
