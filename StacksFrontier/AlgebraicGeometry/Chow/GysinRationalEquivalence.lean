module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction

/-!
# Descending the Gysin homomorphism to Chow groups

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible module on `X` and let `s ∈ Γ(X, L)` be a global section with
zero scheme `i : D = Z(s) ⟶ X`. Stacks 02T8 constructs the Gysin map

  `i^* : Z_{k+1}(X) ⟶ A_k(D)`

on *cycles*. Stacks 02TO asserts that this map kills cycles rationally equivalent to zero, so
that it descends to a map `A_{k+1}(X) ⟶ A_k(D)` on Chow groups.

The vanishing itself is **not** proved here, and cannot be at present: see the implementation
notes. What this file does is the descent, once the vanishing is granted. Granting it is not a
loss of information — `Stacks.Chow.IntegralComponentRule.factorsThroughRationalEquivalence_iff`
says that the vanishing is *equivalent* to the existence of a descended map, and
`Stacks.Chow.gysinHomomorphismOnChow` is the unique such map
(`Stacks.Chow.eq_gysinHomomorphismOnChow`).

Since the Gysin map is `Stacks.Chow.IntegralComponentRule.extendChow` of the two component rules
of Stacks 02T8, the descent is carried out once at that level of generality, so that the other
chapter-42 operations defined by a rule on integral components — intersection with a first Chern
class (Stacks 02SO, whose factoring through rational equivalence is Stacks 02TI) — can reuse it.

## Main definitions

* `Stacks.Chow.IntegralComponentRule.FactorsThroughRationalEquivalence` — the assertion that the
  coefficientwise extension of a rule on integral components kills rational equivalences.
* `Stacks.Chow.IntegralComponentRule.descend` — the resulting map on Chow groups.
* `Stacks.Chow.GysinFactorsThroughRationalEquivalence` — that assertion for the Gysin rule, i.e.
  the statement of Stacks 02TO.
* `Stacks.Chow.gysinHomomorphismOnChow` — the Gysin homomorphism descended to Chow groups.

## Main results

* `Stacks.Chow.IntegralComponentRule.factorsThroughRationalEquivalence_iff` — factoring through
  rational equivalence is equivalent to the existence of a descended map.
* `Stacks.Chow.IntegralComponentRule.eq_descend` — the descended map is unique.
* `Stacks.Chow.gysinHomomorphismOnChow_mk` — the descended Gysin map agrees with the Gysin
  homomorphism on cycle representatives.
* `Stacks.Chow.gysinHomomorphismOnChow_mk_cycleAssociatedToClosedSubscheme` — its value on the
  class of an integral closed subscheme not contained in the zero scheme is the class of the
  scheme-theoretic intersection.
* `Stacks.Chow.gysinHomomorphismOnChow_finsum` — the locally finite component formula, read on
  Chow classes.

## Implementation notes

### Why the vanishing is a hypothesis

The proof of Stacks 02TO reduces, by proper pushforward along `⨿ W_j ⟶ X`, to the case of a
single integral `X` and `α = div(f)`, and then evaluates the two sides with the key formula.
Precisely, it uses

* Stacks 02TA, that the Gysin map commutes with proper pushforward — unformalized, and stated in
  terms of proper pushforward on *Chow* groups (Stacks 0GU8), which this repository does not have
  either, since that rests on Stacks 02S2;
* Stacks 02S2, that proper pushforward preserves rational equivalence — unformalized;
* Stacks 02TM, that `i^* div_N(t) = c_1(N|_D) ∩ [D]_{n-1}` — unformalized, and resting on the key
  formula of Stacks 0AYC, on Stacks 02SJ (the divisor of a meromorphic section) and on Stacks
  02SK;
* Stacks 02TI and 02SP, both of which are statements about the first Chern class cap product of
  Stacks 02SO, which is likewise not in this repository.

Every one of these is a genuine gap, not a matter of effort here. So the vanishing is carried as
an explicit hypothesis `Stacks.Chow.GysinFactorsThroughRationalEquivalence`, in the same way that
`StacksFrontier.AlgebraicGeometry.Chow.Vocabulary` carries the dimension function of the missing
Stacks 02JW as an explicit hypothesis, and that
`StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction` carries the first Chern class of the
missing Stacks 02SO as the explicit argument `chern`. Whoever proves Stacks 02TO discharges the
hypothesis and recovers the unconditional statements; until then nothing below is tainted.

The hypothesis is genuinely needed for an arbitrary `chern`: the Gysin map of Stacks 02T8 is
built here from an arbitrary `Stacks.Chow.FirstChernComponentClassRule`, and its values on
components contained in the zero scheme are whatever that rule says, so it has no reason to kill
rational equivalences unless the rule really is the first Chern class.

### Where Stacks 02TO is carried

The declarations below quantify over the `chern` parameter of Stacks 02T8, so they are statements
about an arbitrary rule on integral components rather than about `L` and `s`. The tag is carried
two steps further on, in
`StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceReduction`: there `chern` is the first
Chern class component rule of `L`, the vanishing is *derived* rather than assumed, and what is
granted in its place is the single-component statement the source's proof reduces to.

## References

* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Descending a rule on integral components through rational equivalence -/

namespace IntegralComponentRule

variable {C : ChowSituation.{u}} {X Y : Scheme.{u}} {p : X ⟶ C.S} [LocallyOfFiniteType p]
  {q : Y ⟶ C.S} [LocallyOfFiniteType q] {g : Y ⟶ X} {k : ℤ}
  (R : IntegralComponentRule C p q g k)

/-- The coefficientwise extension of a rule on integral components *factors through rational
equivalence* when it kills every `(k+1)`-cycle rationally equivalent to zero. For the Gysin rule
of Stacks 02T8 this is the content of Stacks 02TO; for the first Chern class rule of Stacks 02SO
it is the content of Stacks 02TI. -/
def FactorsThroughRationalEquivalence : Prop :=
  ∀ α ∈ rationalEquivalences C p (k + 1), R.extendChow α = 0

/-- The map on Chow groups induced by a rule on integral components that factors through rational
equivalence. -/
def descend (h : R.FactorsThroughRationalEquivalence) :
    chowGroup C p (k + 1) →+ chowGroup C q k :=
  QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) R.extendChow h

/-- On the class of a cycle, the descended map is the extension of the rule. -/
@[simp]
theorem descend_mk (h : R.FactorsThroughRationalEquivalence) (α : CycleGroup C p (k + 1)) :
    R.descend h (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) = R.extendChow α :=
  rfl

/-- The descended map, composed with the projection to the Chow group, is the extension of the
rule. -/
theorem descend_comp_mk' (h : R.FactorsThroughRationalEquivalence) :
    (R.descend h).comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      R.extendChow :=
  rfl

/-- The descended map is the only homomorphism on Chow groups that agrees with the extension of
the rule on cycle representatives. -/
theorem eq_descend (h : R.FactorsThroughRationalEquivalence)
    (F : chowGroup C p (k + 1) →+ chowGroup C q k)
    (hF : F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) = R.extendChow) :
    F = R.descend h :=
  QuotientAddGroup.addMonoidHom_ext _ (hF.trans (R.descend_comp_mk' h).symm)

/-- **The hypothesis is exactly the descent.** A rule on integral components factors through
rational equivalence precisely when its coefficientwise extension descends to a homomorphism of
Chow groups. So carrying the factoring as a hypothesis, as Stacks 02TO must be carried in this
repository, loses nothing: the hypothesis *is* the existence of the descended map. -/
theorem factorsThroughRationalEquivalence_iff :
    R.FactorsThroughRationalEquivalence ↔
      ∃ F : chowGroup C p (k + 1) →+ chowGroup C q k,
        F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) = R.extendChow := by
  refine ⟨fun h ↦ ⟨R.descend h, R.descend_comp_mk' h⟩, fun ⟨F, hF⟩ α hα ↦ ?_⟩
  rw [← DFunLike.congr_fun hF α, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
    (QuotientAddGroup.eq_zero_iff α).2 hα, map_zero]

end IntegralComponentRule

/-! ### The Gysin homomorphism on Chow groups -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)

/-- **Stacks 02TO.** The assertion that the Gysin homomorphism of the zero scheme of `s` kills
every `(k+1)`-cycle rationally equivalent to zero, hence factors through rational equivalence.

This is the statement of Stacks 02TO, carried as a hypothesis because its proof needs Stacks
02TA, 02S2, 02TM, 02TI and 02SP, none of which is formalized in this repository; see the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalence`. -/
def GysinFactorsThroughRationalEquivalence : Prop :=
  ∀ α ∈ rationalEquivalences C p (k + 1), gysinHomomorphism C p k L s chern α = 0

/-- The Gysin map factors through rational equivalence exactly when the rule on integral
components it is built from does. -/
theorem gysinFactorsThroughRationalEquivalence_iff_gysinRule :
    GysinFactorsThroughRationalEquivalence C p k L s chern ↔
      (gysinRule C p k L s chern).FactorsThroughRationalEquivalence :=
  Iff.rfl

/-- **Stacks 02TO.** The Gysin homomorphism descended to Chow groups,
`i^* : A_{k+1}(X) ⟶ A_k(D)`, granted that it factors through rational equivalence. -/
def gysinHomomorphismOnChow (h : GysinFactorsThroughRationalEquivalence C p k L s chern) :
    chowGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  QuotientAddGroup.lift (rationalEquivalences C p (k + 1)) (gysinHomomorphism C p k L s chern) h

/-- **Stacks 02TO.** The descended Gysin map agrees with the Gysin homomorphism on cycle
representatives. -/
@[simp]
theorem gysinHomomorphismOnChow_mk (h : GysinFactorsThroughRationalEquivalence C p k L s chern)
    (α : CycleGroup C p (k + 1)) :
    gysinHomomorphismOnChow C p k L s chern h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
      gysinHomomorphism C p k L s chern α :=
  rfl

/-- The descended Gysin map, composed with the projection to the Chow group of `X`, is the Gysin
homomorphism on cycles. -/
theorem gysinHomomorphismOnChow_comp_mk'
    (h : GysinFactorsThroughRationalEquivalence C p k L s chern) :
    (gysinHomomorphismOnChow C p k L s chern h).comp
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      gysinHomomorphism C p k L s chern :=
  rfl

/-- **Stacks 02TO.** The descended Gysin map is the only homomorphism of Chow groups agreeing
with the Gysin homomorphism on cycle representatives. -/
theorem eq_gysinHomomorphismOnChow (h : GysinFactorsThroughRationalEquivalence C p k L s chern)
    (F : chowGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)
    (hF : F.comp (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))) =
      gysinHomomorphism C p k L s chern) :
    F = gysinHomomorphismOnChow C p k L s chern h :=
  (gysinRule C p k L s chern).eq_descend h F hF

/-- **Stacks 02T8, 02TO.** The descended Gysin map sends the class of an integral closed
subscheme `W` of delta-dimension `k + 1` *not* contained in the zero scheme to the class of the
fundamental cycle of the scheme-theoretic intersection `W ∩ D`. -/
theorem gysinHomomorphismOnChow_mk_cycleAssociatedToClosedSubscheme
    (h : GysinFactorsThroughRationalEquivalence C p k L s chern) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hle : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphismOnChow C p k L s chern h
        (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1))
          (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k) := by
  rw [gysinHomomorphismOnChow_mk, gysinHomomorphism_of_not_le C p k L s chern W hW hDim hle]

/-- **Stacks 02T8, 02TO.** The locally finite component formula for the descended Gysin map: on
the class of a cycle presented as `α = ∑ n_j [W_j]` by a locally finite family of integral closed
subschemes of delta-dimension `k + 1`, its value is the class of the cycle whose coefficients are
`∑ n_j` times the Gysin component cycles of the `W_j`. -/
theorem gysinHomomorphismOnChow_finsum
    (h : GysinFactorsThroughRationalEquivalence C p k L s chern) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X))) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      gysinHomomorphismOnChow C p k L s chern h
          (QuotientAddGroup.mk' (rationalEquivalences C p (k + 1)) α) =
        QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycle C p k L s chern (W j) (hW j) (hDim j)).1 x := by
  obtain ⟨β, hβ, hcoeff⟩ := gysinHomomorphism_finsum C p k L s chern W hW hDim hLocal n α hα
  exact ⟨β, by rw [gysinHomomorphismOnChow_mk, hβ], hcoeff⟩

end Stacks.Chow

end
