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
  02TI.
* `Stacks.Chow.firstChernClassCapOnChow` — the cap product descended to Chow groups.
* `Stacks.Chow.ChernCapOperator` — a component rule in every degree whose cap product factors
  through rational equivalence: what an invertible module provides once Stacks 02SO and 02TI are
  available.
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

### Why the vanishing is a hypothesis

The proof of Stacks 02TI pushes forward along the proper morphism `⨿ W_j ⟶ X` to reduce to a
single integral `X` and `α = div_X(f)`, which needs Stacks 02SU (that the cap product commutes
with proper pushforward) and through it Stacks 0GU8 and 02S2 (proper pushforward on Chow groups),
none of which is in this repository; the reduced case is then
`Stacks.Chow.firstChernClassCap_eq_zero_of_keyFormula` of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity`, which is proved there from the
key formula. So the vanishing is carried as a hypothesis, exactly as
`Stacks.Chow.GysinFactorsThroughRationalEquivalence` is for Stacks 02TO.

Carrying it is also unavoidable for a reason that has nothing to do with missing inputs: the cap
product here is built from an arbitrary `Stacks.Chow.FirstChernComponentCycleRule`, and an
arbitrary rule on integral components has no reason to kill rational equivalences. The hypothesis
is not a weakening — `Stacks.Chow.firstChernClassCapFactorsThroughRationalEquivalence_iff` says it
is equivalent to the existence of the descended operation that is the content of Stacks 02TI.

### The form of the `@[stacks 02TI]` attribute

`Stacks.Chow.firstChernClassCapOnChow` constructs the operation `A_{k+1}(X) ⟶ A_k(X)` the tag
asserts to exist, out of the vanishing on rational equivalences that the tag's proof establishes;
the vanishing is a hypothesis and the `chern` parameter stands in for Stacks 02SO, so the
attribute records both in its restriction string. The integral case of the vanishing, which is
the case the source's proof reduces the general statement to, is proved in
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity` and carries the tag there with its
own restriction string.

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

/-- **Stacks 02TI.** The assertion that intersecting with the first Chern class kills every
`(k+1)`-cycle rationally equivalent to zero, hence factors through rational equivalence.

Carried as a hypothesis; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.IntersectionCommutativity.ChernCapDescent`. -/
def FirstChernClassCapFactorsThroughRationalEquivalence : Prop :=
  ∀ α ∈ rationalEquivalences C p (k + 1), firstChernClassCap C p k chern α = 0

/-- The cap product factors through rational equivalence exactly when the rule on integral
components it is built from does. -/
theorem firstChernClassCapFactorsThroughRationalEquivalence_iff_firstChernCapRule :
    FirstChernClassCapFactorsThroughRationalEquivalence C p k chern ↔
      (firstChernCapRule C p k chern).FactorsThroughRationalEquivalence :=
  Iff.rfl

/-- **Stacks 02TI.** Intersection with the first Chern class, descended to Chow groups,
`c₁(L) ∩ - : A_{k+1}(X) ⟶ A_k(X)`. -/
@[stacks 02TI "the descended operation, granting the vanishing and the rule of 02SO"]
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

This is what an invertible module on `X` provides once Stacks 02SJ (the divisor cycle of a
regular meromorphic section, which produces the component rule) and Stacks 02TI are available.
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
