module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ComponentDecomposition
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreFamilyReduction
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDropImage
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg

/-!
# What the dimension-drop branch closes: Stacks 02S2 in general, and 02S4 part (2), hence 02S5

`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne` is
the one statement two developments in this chapter were each carrying as a hypothesis:

* `Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_vanishing_of_dimension_drop` asks exactly
  for it, with the subscheme spelled as `V.map p` rather than as the scheme-theoretic image of
  `V.subschemeι ≫ p` — the same ideal sheaf by definition. Discharging it makes
  `Stacks.Chow.ProperPushforwardKillsPrincipalDivisor` a theorem for an arbitrary proper morphism
  over the base, hence makes
  `Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` — **Stacks 02S2** — hold
  unconditionally.
* `Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop`
  asks for the vanishing of `Stacks.Chow.fibreDifference` in the same case. Since
  `Stacks.Chow.fibreDifference_eq_properPushforward` writes that difference as the pushforward of a
  principal divisor along the first projection `W ⟶ X`, the same theorem discharges it, making
  `Stacks.Chow.FibreCyclesRationallyEquivalentWithin` — **Stacks 02S4 part (2)** — a theorem, hence
  also part (3) and, with the decomposition rule, **Stacks 02S5**.

## Main results

* `Stacks.Chow.properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_map_ne` — the
  dimension-drop branch in the vocabulary of `Stacks.Chow.properPushforwardPrincipalDivisor`.
* `Stacks.Chow.properPushforwardKillsPrincipalDivisor_of_isProper` — the one-subscheme content of
  Stacks 02S2, for an arbitrary proper morphism over the base, with no hypothesis.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence` — **Stacks 02S2**: proper
  pushforward carries cycles rationally equivalent to zero to cycles rationally equivalent to
  zero.
* `Stacks.Chow.fibreCyclesRationallyEquivalentWithin` — **Stacks 02S4 part (2)**, in the
  carrier-refined one-member form.
* `Stacks.Chow.fibreCycles_rationallyEquivalent` — part (2) in the two-cycle form the tag states.
* `Stacks.Chow.familyFibreDifferencesRationallyEquivalentToZero` — **Stacks 02S4 part (3)**.
* `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent` — **Stacks 02S5**.
* `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_fieldChowSituation` — the
  dimension-drop hypothesis is satisfiable: a proper integral curve over a field satisfies it, and
  there the general branch specialises back to Stacks 02RU.

## Implementation notes

### Two cycle groups, one cycle

`Stacks.Chow.fibrePrincipalDivisorCycle` is `Stacks.Chow.principalDivisorCycle` re-indexed from
`k + 1 - 1` to `k`; the two live in different cycle groups but have the same underlying
`AlgebraicCycle`. `Stacks.Chow.properPushforward_eq_zero_of_val_eq` is the transport: proper
pushforward only ever uses the underlying cycle, so a vanishing at one index gives a vanishing at
the other.

### No `@[stacks]` attribute

Stacks 02S2, 02S4 and 02S5 are registered at their own statements elsewhere, so no attribute is
placed here.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Transport between two indices of one cycle -/

/-- Proper pushforward depends only on the underlying cycle, not on the index of the cycle group
it is taken in: if two cycles at two indices have the same underlying `AlgebraicCycle` and one
pushes forward to zero, so does the other. -/
theorem properPushforward_eq_zero_of_val_eq (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) {k k' : ℤ}
    (c : CycleGroup C sX k) (c' : CycleGroup C sX k') (hcc : c.1 = c'.1)
    (h : properPushforward C sX sY p hp k' c' = 0) :
    properPushforward C sX sY p hp k c = 0 := by
  have hval : (properPushforward C sX sY p hp k c).1 =
      (properPushforward C sX sY p hp k' c').1 := by
    show AlgebraicCycle.map p (relativeDimension C.dimensionFunction sX)
        (relativeDimension C.dimensionFunction sY) c.1 =
      AlgebraicCycle.map p (relativeDimension C.dimensionFunction sX)
        (relativeDimension C.dimensionFunction sY) c'.1
    rw [hcc]
  refine Subtype.ext (hval.trans ?_)
  rw [h]
  rfl

/-! ### Stacks 02S2 -/

section TwoSTwo

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)

include hp

/-- **The dimension-drop branch of Stacks 02S2, in the vocabulary of
`Stacks.Chow.properPushforwardPrincipalDivisor`.** For an integral closed subscheme `V ⊆ X` of
delta-dimension `k + 1` whose scheme-theoretic image `V.map p` does not have delta-dimension
`k + 1`, the proper pushforward along `p` of the principal divisor of a rational function on `V`
is zero.

`V.map p` is by definition the scheme-theoretic image of `V.subschemeι ≫ p`, so this is
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne`
applied to that morphism; the identification of the two cycles is functoriality of the weighted
pushforward along `V.subschemeι ≫ p = V.subschemeι ≫ p`. -/
theorem properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_map_ne (k : ℤ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (hne : schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) ≠ ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    properPushforwardPrincipalDivisor C sX sY p V hV g = 0 := by
  have _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  have hfac : (V.subschemeι ≫ p) ≫ sY = V.subschemeι ≫ sX := by rw [Category.assoc, hp]
  calc properPushforwardPrincipalDivisor C sX sY p V hV g
      = AlgebraicCycle.map (V.subschemeι ≫ p)
          (relativeDimension C.dimensionFunction (V.subschemeι ≫ sX))
          (relativeDimension C.dimensionFunction sY)
          (principalCycle V.subscheme
            ((rationalFunctionsEquivFunctionField V.subscheme).1
              (g : rationalFunctions V.subscheme))) :=
        algebraicCycle_map_comp_relativeDimension C (V.subschemeι ≫ sX) sX sY V.subschemeι p
          rfl hp _
    _ = 0 := congrArg Subtype.val
      (properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne
        C (V.subschemeι ≫ sX) sY hdim (V.subschemeι ≫ p) hfac hne
        ((rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme)))

/-- **The one-subscheme content of Stacks 02S2, for an arbitrary proper morphism, with no
hypothesis.** The Stacks 02RT branch is
`Stacks.Chow.exists_principalDivisorPushforward_eq_of_schemeDeltaDimension_eq` and the Stacks
02RU branch is now
`Stacks.Chow.properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_map_ne`. -/
theorem properPushforwardKillsPrincipalDivisor_of_isProper (k : ℤ) :
    ProperPushforwardKillsPrincipalDivisor C sX sY p k :=
  properPushforwardKillsPrincipalDivisor_of_vanishing_of_dimension_drop C sX sY p hp k
    (properPushforwardPrincipalDivisor_eq_zero_of_schemeDeltaDimension_map_ne C sX sY p hp k)

/-- **Stacks 02S2.** Proper pushforward along a proper morphism over the base carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero. -/
theorem properPushforwardFactorsThroughRationalEquivalence (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k :=
  properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor C sX sY p hp k
    (properPushforwardKillsPrincipalDivisor_of_isProper C sX sY p hp k)

/-- **Stacks 02S2 with the carrier of the resulting rational equivalence retained.** The
witnessing family of the pushed-forward equivalence lies in the closure of the image of `p`. -/
theorem properPushforward_isRationallyEquivalentToZeroWithin (k : ℤ) {α : CycleGroup C sX k}
    (hα : IsRationallyEquivalentToZero C sX k α) :
    IsRationallyEquivalentToZeroWithin C sY k (properPushforward C sX sY p hp k α)
      (closure (Set.range p.base)) :=
  properPushforward_isRationallyEquivalentToZeroWithin_of_killsPrincipalDivisor C sX sY p hp k
    (properPushforwardKillsPrincipalDivisor_of_isProper C sX sY p hp k) hα

end TwoSTwo

/-! ### Stacks 02S4 part (2) and its consequences -/

section TwoSFour

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (k : ℤ)

/-- **The fibre difference of `W` vanishes when the projection `W ⟶ X` drops
delta-dimension.** This is the hypothesis of
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_fibreDifference_eq_zero_of_dimension_drop`:
by `Stacks.Chow.fibreDifference_eq_properPushforward` the difference is the proper pushforward of
a principal divisor along the first projection, and the dimension-drop branch of Stacks 02S2 kills
it. -/
theorem fibreDifference_eq_zero_of_schemeDeltaDimension_ker_ne
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    (hdim : schemeDeltaDimension C (familyBase f W) = ((k + 1 : ℤ) : EInt))
    (hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) ≠
      ((k + 1 : ℤ) : EInt))
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    fibreDifference C f k W = 0 := by
  rw [fibreDifference_eq_properPushforward C f W k hdim h₀ hInf]
  exact properPushforward_eq_zero_of_val_eq C (familyBase f W) f (fibreBaseProjection f W)
    (fibreBaseProjection_comp f W) _
    (principalDivisorCycle C (familyBase f W) hdim (fibreCoordinate C f W hInf)) rfl
    (properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne C
      (familyBase f W) f hdim (fibreBaseProjection f W) (fibreBaseProjection_comp f W) hker
      (fibreCoordinate C f W hInf))

/-- **Stacks 02S4 part (2), in the carrier-refined one-member form, with no hypothesis.** For an
integral closed subscheme `W ⊆ X ×_S ℙ¹_S` of relative dimension `k + 1` contained in neither
distinguished section, the difference of the cycles of its two fibres is rationally equivalent to
zero within `Stacks.Chow.fibreCarrier`.

The dominant case is
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq`; the
remaining case is `Stacks.Chow.fibreDifference_eq_zero_of_schemeDeltaDimension_ker_ne`, where the
difference is zero and the empty family witnesses the equivalence. -/
theorem fibreCyclesRationallyEquivalentWithin : FibreCyclesRationallyEquivalentWithin C f k := by
  intro W hW hDim h₀ hInf
  have hdim := schemeDeltaDimension_familyBase C f W hDim
  by_cases hker : schemeDeltaDimension C ((fibreBaseProjection f W).ker.subschemeι ≫ f) =
      ((k + 1 : ℤ) : EInt)
  · exact fibreCyclesRationallyEquivalentWithin_of_schemeDeltaDimension_ker_eq C f W k hdim hker
      h₀ hInf
  · rw [fibreDifference_eq_zero_of_schemeDeltaDimension_ker_ne C f k W hdim hker h₀ hInf]
    exact isRationallyEquivalentToZeroWithin_zero C f k _

/-- **Stacks 02S4 part (2), in the two-cycle form the tag states.** -/
@[stacks 02S4 "part (2)"]
theorem fibreCycles_rationallyEquivalent
    (W : (projectiveLineProduct f).IdealSheafData) [IsIntegral W.subscheme]
    (hDim : ∀ ξ : genericPoints W.subscheme,
      relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1)
    (h₀ : ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f))
    (hInf : ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k) :=
  (fibreCyclesRationallyEquivalentWithin C f k W inferInstance hDim h₀
    hInf).isRationallyEquivalentToZero

/-- **Stacks 02S4 part (3).** The family form, for a locally finite family of integral closed
subschemes of `X ×_S ℙ¹_S`. -/
@[stacks 02S4 "part (3)"]
theorem familyFibreDifferencesRationallyEquivalentToZero :
    FamilyFibreDifferencesRationallyEquivalentToZero C f k :=
  familyFibreDifferencesRationallyEquivalentToZero_of_within C f k
    (fibreCyclesRationallyEquivalentWithin C f k)

/-- **Stacks 02S5.** For a closed subscheme `Z ⊆ X ×_S ℙ¹_S` whose relative dimension is at most
`k + 1`, whose two fibres have delta-dimension at most `k`, and each of whose associated points
either misses both distinguished sections or has relative dimension below `k`, the cycles of the
two fibres are rationally equivalent on `X`.

Both inputs are now theorems: the decomposition rule is
`Stacks.Chow.fibreCycleComponentDecompositionRule` and part (2) of Stacks 02S4 is
`Stacks.Chow.fibreCyclesRationallyEquivalentWithin`.

The source states its hypothesis (3) for the *embedded* points of `Z` rather than for all of
its associated points. That reading is strictly weaker and the lemma is false under it; the two
differ exactly at the generic points of the irreducible components of `Z` of relative dimension
`k`, which the source's proof silently assumes away when it reads `dim(A/I) = 1` off
`δ(ξ) = k`. `Stacks.Chow.cycleAssociatedToFibres_rationallyEquivalent_of_isEmbeddedPoint`
(`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/EmbeddedPointHypothesis.lean`) states the
hypothesis in the source's two-clause shape and documents the counterexample. -/
@[stacks 02S5]
theorem cycleAssociatedToFibres_rationallyEquivalent
    (Z : (projectiveLineProduct f).IdealSheafData)
    (hZ : ∀ ζ : Z.subscheme,
      relativeDimension C.dimensionFunction (familyBase f Z) ζ ≤ k + 1)
    (h₀ : schemeDeltaDimension C ((zeroFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hInf : schemeDeltaDimension C ((infinityFiber f Z).subschemeι ≫ f) ≤ (k : EInt))
    (hAssociated : ∀ ζ : Z.subscheme,
      ζ ∈ Stacks.Divisors.schemeAssociatedPoints Z.subscheme →
      ((Z.subschemeι ζ ∉ Set.range (zeroSection f) ∧
          Z.subschemeι ζ ∉ Set.range (infinitySection f)) ∨
        relativeDimension C.dimensionFunction (familyBase f Z) ζ < k)) :
    RationallyEquivalent C f k
      (cycleAssociatedToClosedSubscheme C f (zeroFiber f Z).subschemeι k)
      (cycleAssociatedToClosedSubscheme C f (infinityFiber f Z).subschemeι k) :=
  cycleAssociatedToFibres_rationallyEquivalent_of_within C f k Z hZ h₀ hInf hAssociated
    (fibreCyclesRationallyEquivalentWithin C f k)

end TwoSFour

/-! ### The dimension-drop hypothesis is satisfied -/

section NonVacuity

/-- The delta-dimension of the scheme-theoretic image of a proper morphism to the spectrum of a
field is zero: the image is a closed subscheme of a point, so the inclusion is a preimmersion and
contributes no transcendence degree, while the base dimension function vanishes. -/
theorem schemeDeltaDimension_image_eq_zero_of_fieldChowSituation (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ (fieldChowSituation k).S) [IsProper c] :
    schemeDeltaDimension (fieldChowSituation k) (c.imageι ≫ 𝟙 (fieldChowSituation k).S) =
      ((0 : ℤ) : EInt) := by
  have _ : IsIntegral c.image := isIntegral_image c
  rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_eq_add_trdeg,
    residueTrdeg_eq_zero_of_isPreimmersion, relativeDimension_id,
    fieldChowSituation_dimensionFunction]
  simp

/-- **The dimension-drop hypothesis is not vacuous, and the general branch specialises back to
Stacks 02RU.** A proper integral curve over a field has scheme-theoretic image the base, of
delta-dimension `0 ≠ 1`, so
`Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne`
applies and gives exactly Stacks 02RU over a field.

This is the satisfiability check for the hypothesis `hne`, and simultaneously a check on the
plumbing of the general proof — the generic fibre of a curve over a field is the curve itself, so
the two sums that proof identifies are identified correctly only if the indices, the order of
vanishing and the residue degrees all line up. It is **not** independent evidence for Stacks
02RU, which the general proof consumes. -/
theorem properPushforward_principalDivisorCycle_eq_zero_of_fieldChowSituation (k : Type u)
    [Field k] {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ (fieldChowSituation k).S) [IsProper c]
    (hdim : schemeDeltaDimension (fieldChowSituation k) c = ((1 : ℤ) : EInt))
    (g : X.functionField) :
    properPushforward (fieldChowSituation k) c (𝟙 (fieldChowSituation k).S) c
      (Category.comp_id c) (1 - 1)
      (principalDivisorCycle (fieldChowSituation k) c hdim g) = 0 := by
  have _ : IsIntegral ((fieldChowSituation k).S) :=
    inferInstanceAs (IsIntegral (AlgebraicGeometry.Spec (.of k)))
  exact properPushforward_principalDivisorCycle_eq_zero_of_schemeDeltaDimension_image_ne
    (fieldChowSituation k) c (𝟙 (fieldChowSituation k).S) hdim c (Category.comp_id c)
    (by
      rw [schemeDeltaDimension_image_eq_zero_of_fieldChowSituation]
      exact fun h ↦ absurd (WithBotTop.coe_injective h) (by decide)) g

end NonVacuity

end Stacks.Chow

end
