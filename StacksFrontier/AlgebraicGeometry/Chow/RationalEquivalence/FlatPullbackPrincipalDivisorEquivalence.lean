module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor
public import StacksCore.Tactic.StacksAttribute

/-!
# The flat pullback of a principal divisor is rationally equivalent to zero

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` and `Y` be
schemes locally of finite type over `S` with `Y` integral of delta-dimension `k`, and let
`f : X ⟶ Y` be flat of constant relative dimension `r`. For a nonzero rational function `g` on
`Y` the flat pullback `f^* div_Y(g)` of the principal divisor of `g` is rationally equivalent to
zero as a `(k + r - 1)`-cycle on `X`.

This is the case of **Stacks 02S1** — flat pullback preserves rational equivalence — in which the
rational equivalence on `Y` is presented by the one-element family consisting of `Y` itself. It is
the step of the proof of that tag which carries the mathematical weight; the passage from a general
member `W ⊆ Y` of a presenting family to `Y` itself is the closed-immersion case of Stacks 02RG,
`Stacks.Chow.flatPullback_properPushforward_comap`, and the general case is
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZero_of_coe_eq_flatPullback_principalDivisorCycle` — the
  statement above.

## Implementation notes

The conclusion is taken in the flexible form "`α` is a `j`-cycle on `X` whose coefficients are
those of `f^* div_Y(g)`, and `j = k + r - 1`" rather than literally about
`Stacks.Chow.flatPullback` applied to `Stacks.Chow.principalDivisorCycle`. That pullback is built
in `Z_{(k-1)+r}(X)` while the components of `X` carry their principal divisors in
`Z_{(k+r)-1}(X)`; the two indices are equal integers but distinct terms, and every consumer has
its own spelling. This follows
`Stacks.Chow.isRationallyEquivalentToZero_of_eq_principalCycle` and
`Stacks.Chow.flatPullback_principalDivisorCycle`, which are stated on underlying cycles for the
same reason.

The proof assembles three results.

* Stacks 0EPH, `Stacks.Chow.flatPullback_principalDivisor_eq_sum_components`, writes the
  coefficient of `f^* div_Y(g)` at a point of `X` as the locally finite sum over the irreducible
  components `X_j` of `X` of `n_j` times the coefficient of the pushforward of
  `div_{X_j}(g ∘ f|_{X_j})`, where `n_j` is the multiplicity of `X_j` in the fundamental cycle
  `[X]_{k+r}`.
* Each term is rationally equivalent to zero on `X_j`: the component is integral of
  delta-dimension `k + r`, so Stacks 02RW for a principal divisor on the scheme itself,
  `Stacks.Chow.isRationallyEquivalentToZero_principalDivisorCycle`, applies, and the multiplicity
  `n_j` is absorbed because the cycles rationally equivalent to zero form a subgroup.
* Stacks 02RZ in the form `Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion`
  sums the pushforwards. Its local finiteness hypothesis is Stacks 0BE1,
  `AlgebraicGeometry.locallyFinite_irreducibleComponents_image`, the range of the inclusion of a
  component being the component itself.

The index type of the family is the irreducible components of `X`, which live in the universe of
the schemes, as `Stacks.Chow.IsRationallyEquivalentToZero` requires.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0EPH](https://stacks.math.columbia.edu/tag/0EPH)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-- The coefficient of the proper pushforward of an integer multiple of a cycle. -/
theorem properPushforward_zsmul_apply_aux (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (g : X ⟶ Y)
    [IsProper g] (hg : g ≫ sY = sX) (k : ℤ) (n : ℤ) (c : CycleGroup C sX k) (y : Y) :
    (properPushforward C sX sY g hg k (n • c)).1 y =
      n * (properPushforward C sX sY g hg k c).1 y := by
  rw [show properPushforward C sX sY g hg k (n • c) = n • properPushforward C sX sY g hg k c from
    map_zsmul (properPushforwardHom C sX sY g hg k) n c]
  rfl

/-! ### Stacks 02S1 for a principal divisor on the target -/

/-- **Stacks 02S1 for a principal divisor on an integral target.** Let `X` and `Y` be locally of
finite type over the base of chapter 42 with `Y` integral of delta-dimension `k`, let
`f : X ⟶ Y` be flat of relative dimension `r`, and let `g` be a nonzero rational function on `Y`.
Then the flat pullback `f^* div_Y(g)` of the principal divisor of `g` is rationally equivalent to
zero, as a `(k + r - 1)`-cycle on `X`.

Stacks 0EPH writes that pullback as the locally finite sum `∑_j n_j (i_j)_* div_{X_j}(g)` over the
irreducible components `X_j` of `X` taken with their reduced structure. Each `X_j` is integral of
delta-dimension `k + r`, so `div_{X_j}(g)` is rationally equivalent to zero on `X_j` by Stacks
02RW, and the multiplicity `n_j` is absorbed by the subgroup. The components form a locally finite
family by Stacks 0BE1, so Stacks 02RZ sums the pushforwards into a single rational equivalence
on `X`. -/
@[stacks 02S1 "the case of a principal divisor on an integral target"]
theorem isRationallyEquivalentToZero_of_coe_eq_flatPullback_principalDivisorCycle
    (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] [IsIntegral Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sY = sX) (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) {k j : ℤ}
    (hY : schemeDeltaDimension C sY = (k : EInt)) {g : Y.functionField} (hg : g ≠ 0)
    (hj : j = k + (r : ℤ) - 1) (α : CycleGroup C sX j)
    (hα : ∀ x : X, α.1 x =
      (flatPullback C sX sY f hbase r hf (k - 1) (principalDivisorCycle C sY hY g)).1 x) :
    IsRationallyEquivalentToZero C sX j α := by
  subst hj
  have hNX : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  -- The reduced irreducible components of `X`, each integral of delta-dimension `k + r`.
  have hdim : ∀ W : irreducibleComponents X,
      schemeDeltaDimension C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) =
        ((k + (r : ℤ) : ℤ) : EInt) :=
    fun W ↦ schemeDeltaDimension_integralComponentAt_comp C sX sY f hbase r hf hY W
  -- The restriction of `g` to a component, and its principal divisor there.
  let dcyc : ∀ W : irreducibleComponents X,
      CycleGroup C ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
        (k + (r : ℤ) - 1) := fun W ↦
    let : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
      isIntegral_integralComponentAt _
    let := isDominant_subschemeι_integralComponentAt_comp f W
    principalDivisorCycle C _ (hdim W)
      (dominantFunctionFieldMap
        ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) g)
  -- The multiplicity of the component in the fundamental cycle of `X`.
  let mult : irreducibleComponents X → ℤ := fun W ↦
    (cycleAssociatedToClosedSubscheme C sX (𝟙 X) (k + (r : ℤ))).1 W.2.1.genericPoint
  refine rationallyEquivalentToZero_finsum_of_isClosedImmersion C sX (k + (r : ℤ) - 1)
    (fun W : irreducibleComponents X ↦
      (integralComponentAt W.2.1.genericPoint).subschemeι) ?_
    (fun W ↦ mult W • dcyc W) ?_ α ?_
  · -- Stacks 0BE1: the components of a locally Noetherian scheme are locally finite.
    have hLF : LocallyFinite fun W : irreducibleComponents X ↦ (W : Set X) := by
      simpa using AlgebraicGeometry.locallyFinite_irreducibleComponents_image (𝟙 X)
    refine hLF.subset fun W ↦ ?_
    rw [range_subschemeι_integralComponentAt_genericPoint W]
  · -- Stacks 02RW on each component, with the multiplicity absorbed by the subgroup.
    intro W
    let _ : IsIntegral (integralComponentAt W.2.1.genericPoint).subscheme :=
      isIntegral_integralComponentAt _
    let _ := isDominant_subschemeι_integralComponentAt_comp f W
    have _hNW : IsLocallyNoetherian (integralComponentAt W.2.1.genericPoint).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian
        ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX)
    have hgne : dominantFunctionFieldMap
        ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ f) g ≠ 0 :=
      (map_ne_zero _).2 hg
    exact (rationalEquivalences C
      ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) (k + (r : ℤ) - 1)).zsmul_mem
      (isRationallyEquivalentToZero_principalDivisorCycle C _ (hdim W) hgne) (mult W)
  · -- Stacks 0EPH, with the multiplicity moved inside the pushforward.
    intro x
    rw [hα x, flatPullback_principalDivisor_eq_sum_components C sX sY f hbase r hf hY g hg x]
    refine finsum_congr fun W ↦ ?_
    exact (properPushforward_zsmul_apply_aux C
      ((integralComponentAt W.2.1.genericPoint).subschemeι ≫ sX) sX
      (integralComponentAt W.2.1.genericPoint).subschemeι rfl (k + (r : ℤ) - 1)
      (mult W) (dcyc W) x).symm

end Stacks.Chow

end
