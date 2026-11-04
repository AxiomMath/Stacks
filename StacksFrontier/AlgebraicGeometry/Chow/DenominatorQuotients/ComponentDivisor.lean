module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.PrimeDivisorDimension
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.DivisorCycle
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.PullbackCriteria
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullbackRegular

/-!
# The divisor of the restricted section on a component, pushed forward to a `k`-cycle

The right-hand side of part (4) of
[Stacks, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW) is

  `∑ᵢ mᵢ (Xᵢ → X)_* div_{ℒ|_{Xᵢ}}(sᵢ)`,

a sum over the irreducible components `Xᵢ` of `X` of delta-dimension `k + 1`. This file builds
the summand: for `η` a generic point of an irreducible component of `X` of delta-dimension
`k + 1`, the divisor cycle of the restriction of `s` to the integral closed subscheme
`Xη = Stacks.Chow.integralComponentAt η`, pushed forward along the closed immersion `Xη → X` as
an element of `Z_k(X)`.

Three inputs make the restriction available.

* `Xη → X` carries pullbacks of meromorphic functions, by
  [Stacks, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU) for an **integral source**:
  `Xη` is integral and its generic point maps to `η`, which is a generic point of an irreducible
  component of `X`. `AlgebraicGeometry.HasNoEmbeddedPoints X` is not needed for this case.
* The restriction `sη` of `s` therefore exists, by Tag 02OY part (1), and is a regular
  meromorphic section of `ℒ|_{Xη}` by Tag 02OY part (2).
* `ℒ|_{Xη}` is invertible, the pullback of an invertible module being invertible.

Pushforward along `Xη → X` is `Stacks.Chow.properPushforward`, available because a closed
immersion is proper.

## Main definitions

* `Stacks.Chow.componentMeromorphicSection` — the restriction `sη` of `s` to the component
  through `η`.
* `Stacks.Chow.componentDivisorCycle` — the pushforward of `div_{ℒ|_{Xη}}(sη)` as a `k`-cycle
  on `X`.

## Main results

* `Stacks.Chow.pullbacksMeromorphicSections_subschemeι_integralComponentAt` — Tag 02OU for the
  closed immersion of the component.
* `Stacks.Chow.isRegularMeromorphicSection_componentMeromorphicSection` — Tag 02OY part (2) for
  the restriction, which is the assertion of part (3) of Tag 02SW for the components indexed by
  generic points.
* `Stacks.Chow.componentDivisorCycleOn_apply_of_coheight_eq_one` — the coefficient of
  `div_{ℒ|_{Xη}}(sη)` at a point of codimension one of the component is the order of vanishing of
  `sη` along the prime divisor it generates.
* `Stacks.Chow.componentDivisorCycle_apply_image` — the coefficient of the pushforward at a point
  of the component is that coefficient at the point above it.
* `Stacks.Chow.componentDivisorCycle_apply_eq_zero_of_notMem_range` — the coefficient of the
  pushforward vanishes off the component.

## Implementation notes

The delta-dimension of the component through `η` is supplied by
`Stacks.Chow.schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq` of
`StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction`, which takes the point explicitly.

`AlgebraicGeometry.pullbackMeromorphicSection` and
`AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection` are stated for the
pullback functor `AlgebraicGeometry.RingedSpaceModuleAdjunction.modulePullback` on the underlying
morphism of locally ringed spaces, while the divisor cycle of
`StacksFrontier.AlgebraicGeometry.Chow.MeromorphicCascade.DivisorCycle` is stated for
`AlgebraicGeometry.Scheme.Modules.pullback`; the two agree, and the restriction below is stated
at the second spelling so that the divisor cycle applies to it directly.

Part (2) of Tag 02OY is taken from
`StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionPullbackRegular` in the form proved
there for schemes, whose two hypotheses beyond Tag 02OT are an integral source and a generic
point lying over a generic point of the target. Both hold here, and they are the same two facts
that `Stacks.Chow.pullbacksMeromorphicSections_subschemeι_integralComponentAt` below already
needs: `Stacks.Chow.isIntegral_integralComponentAt` and
`Stacks.Chow.subschemeι_genericPoint_integralComponentAt` of
`StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange`, rewritten
against `hη`.

The divisor cycle of a section on a scheme of delta-dimension `n` lives in `Z_{n-1}`, so with
`n = k + 1` it lives in `Z_{(k+1)-1}`; `add_sub_cancel_right` moves it to `Z_k`, which is where
part (4) reads it. The pushforward is taken there rather than before the move, so that the
grading of the pushforward is `k` on the nose.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02OU](https://stacks.math.columbia.edu/tag/02OU)
* [Stacks Project, Tag 02OY](https://stacks.math.columbia.edu/tag/02OY)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]

/-! ### The component through a generic point -/

/-- **[Stacks, Tag 02OU] for the closed immersion of an irreducible component.** Pullbacks of
meromorphic functions are defined along the closed immersion of the integral component through a
generic point of an irreducible component of `X`: the source is integral, and its generic point
maps to that generic point. -/
theorem pullbacksMeromorphicSections_subschemeι_integralComponentAt {η : X}
    (hη : η ∈ genericPoints X) :
    PullbacksMeromorphicSections (integralComponentAt η).subschemeι.toLRSHom :=
  let := isIntegral_integralComponentAt η
  pullbacksMeromorphicSections_of_isIntegral (integralComponentAt η).subschemeι
    ((subschemeι_genericPoint_integralComponentAt η).symm ▸ hη)

/-! ### The restricted section -/

variable (L : X.Modules)

/-- The restriction of `ℒ` to the integral component through `η` is invertible. -/
theorem isInvertible_componentModule
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (η : X) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (integralComponentAt η).subscheme.sheaf.obj
      (integralComponentAt η).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L) :=
  Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry
    (integralComponentAt η).subschemeι.toLRSHom.toShHom L hL

variable (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)

/-- **The restriction of a meromorphic section to the component through `η`** (Tag 02OY part
(1)): the pullback of `s` along the closed immersion of `Stacks.Chow.integralComponentAt η`, a
meromorphic section of `ℒ|_{Xη}`. -/
def componentMeromorphicSection {η : X} (hη : η ∈ genericPoints X) :
    AlgebraicGeometry.MeromorphicSection (integralComponentAt η).subscheme.sheaf
      ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L) :=
  AlgebraicGeometry.pullbackMeromorphicSection (integralComponentAt η).subschemeι.toLRSHom
    (pullbacksMeromorphicSections_subschemeι_integralComponentAt hη) L s

/-- **Part (3) of [Stacks, Tag 02SW]: `s` restricts to a regular meromorphic section on an
irreducible component of `X`.** The component is `Stacks.Chow.integralComponentAt η`, the reduced
induced structure on the closure of a generic point `η` of `X`; the restriction `sη` is
`Stacks.Chow.componentMeromorphicSection`, at the `AlgebraicGeometry.Scheme.Modules.pullback`
spelling the Chow development consumes. That `sη` exists is Tag 02OU, and that it is regular is
Tag 02OY part (2).

The source states this for the components of delta-dimension `k + 1`, which are among the
components indexed here: on a scheme of delta-dimension at most `k + 1` a point of
delta-dimension `k + 1` is a generic point, by
`Stacks.Chow.mem_genericPoints_of_relativeDimension_eq`. So this is the assertion of part (3)
with the delta-dimension restriction dropped, and part (4) reads it at exactly the components
the source names. -/
theorem isRegularMeromorphicSection_componentMeromorphicSection
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) {η : X}
    (hη : η ∈ genericPoints X) :
    AlgebraicGeometry.IsRegularMeromorphicSection (integralComponentAt η).subscheme.sheaf
      ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
      (componentMeromorphicSection L s hη) :=
  let := isIntegral_integralComponentAt η
  AlgebraicGeometry.isRegularMeromorphicSection_pullbackMeromorphicSection
    (integralComponentAt η).subschemeι
    (pullbacksMeromorphicSections_subschemeι_integralComponentAt hη)
    ((subschemeι_genericPoint_integralComponentAt η).symm ▸ hη) L hL s hs

/-! ### The divisor of the restricted section, as a `k`-cycle on the component -/

variable
  (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
  (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s)

/-- **The divisor `div_{ℒ|_{Xη}}(sη)` of the restricted section, read as a `k`-cycle on the
component through `η`.** The divisor cycle of a regular meromorphic section on a scheme of
delta-dimension `n` lives in `Z_{n-1}`; here `n = k + 1`, and `add_sub_cancel_right` moves the
grading to `k` without changing the coefficient function. -/
def componentDivisorCycleOn {k : ℤ} {η : X} (hη : η ∈ genericPoints X)
    (hδ : relativeDimension C.dimensionFunction f η = k + 1) :
    CycleGroup C ((integralComponentAt η).subschemeι ≫ f) k :=
  letI := isIntegral_integralComponentAt η
  letI := isInvertible_componentModule L hL η
  ⟨(divisorOfMeromorphicSectionCycle C ((integralComponentAt η).subschemeι ≫ f) (k + 1)
      (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ)
      ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
      (componentMeromorphicSection L s hη)
      (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη)).1,
    by
      simpa only [add_sub_cancel_right] using
        (divisorOfMeromorphicSectionCycle C ((integralComponentAt η).subschemeι ≫ f) (k + 1)
          (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ)
          ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
          (componentMeromorphicSection L s hη)
          (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη)).2⟩

/-- **The coefficient of `div_{ℒ|_{Xη}}(sη)` at a point of codimension one of the component** is
the order of vanishing of `sη` along the prime divisor that point generates. -/
theorem componentDivisorCycleOn_apply_of_coheight_eq_one {k : ℤ} {η : X}
    (hη : η ∈ genericPoints X) (hδ : relativeDimension C.dimensionFunction f η = k + 1)
    (z : (integralComponentAt η).subscheme) (hco : Order.coheight z = 1) :
    (componentDivisorCycleOn C f L s hL hs hη hδ).1 z =
      letI := isIntegral_integralComponentAt η
      letI := isInvertible_componentModule L hL η
      letI := LocallyOfFiniteType.isLocallyNoetherian
        ((integralComponentAt η).subschemeι ≫ f)
      Stacks.Divisors.orderOfVanishingMeromorphic (integralComponentAt η).subscheme
        ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
        (componentMeromorphicSection L s hη)
        (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη)
        (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco) := by
  have := isIntegral_integralComponentAt η
  have := isInvertible_componentModule L hL η
  have hgen := Stacks.Divisors.PrimeDivisor.genericPoint_ofCoheightOne z hco
  refine Eq.trans (congrArg _ hgen.symm) ?_
  exact divisorOfMeromorphicSectionCycle_genericPoint C
    ((integralComponentAt η).subschemeι ≫ f) (k + 1)
    (schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ)
    ((Scheme.Modules.pullback (integralComponentAt η).subschemeι).obj L)
    (componentMeromorphicSection L s hη)
    (isRegularMeromorphicSection_componentMeromorphicSection L s hL hs hη)
    (Stacks.Divisors.PrimeDivisor.ofCoheightOne z hco)

/-- The coefficient of `div_{ℒ|_{Xη}}(sη)` vanishes at a point of the component which is not of
codimension one there: it is a cycle of delta-dimension `k` on a scheme of delta-dimension
`k + 1`. -/
theorem componentDivisorCycleOn_apply_eq_zero_of_coheight_ne_one {k : ℤ} {η : X}
    (hη : η ∈ genericPoints X) (hδ : relativeDimension C.dimensionFunction f η = k + 1)
    (z : (integralComponentAt η).subscheme) (hco : Order.coheight z ≠ 1) :
    (componentDivisorCycleOn C f L s hL hs hη hδ).1 z = 0 := by
  have := isIntegral_integralComponentAt η
  by_contra hne
  refine hco ?_
  have hdimZ := schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C f η hδ
  have hz := (mem_cyclesOfDimension_iff_forall_point C
    ((integralComponentAt η).subschemeι ≫ f) k _).1
      (componentDivisorCycleOn C f L s hL hs hη hδ).2 z hne
  exact (relativeDimension_eq_sub_one_iff_coheight_eq_one C
    ((integralComponentAt η).subschemeι ≫ f) hdimZ z).1 (by rw [hz]; ring)

/-! ### Its pushforward -/

/-- **The divisor of the restricted section on the component through `η`, pushed forward to a
`k`-cycle on `X`.** This is the summand of the right-hand side of part (4) of
[Stacks, Tag 02SW]: `(Xη → X)_* div_{ℒ|_{Xη}}(sη)`, for `Xη` the integral component through `η`,
which has delta-dimension `k + 1`. Being an element of `Stacks.Chow.CycleGroup C f k` it is a
locally finite `k`-cycle on `X`. -/
def componentDivisorCycle {k : ℤ} {η : X} (hη : η ∈ genericPoints X)
    (hδ : relativeDimension C.dimensionFunction f η = k + 1) : CycleGroup C f k :=
  properPushforward C ((integralComponentAt η).subschemeι ≫ f) f
    (integralComponentAt η).subschemeι rfl k (componentDivisorCycleOn C f L s hL hs hη hδ)

/-- **The coefficient of the pushforward at a point of the component** is the coefficient of
`div_{ℒ|_{Xη}}(sη)` at the point of the component above it: a closed immersion is injective and
preserves both the relative dimension and the residue field. -/
theorem componentDivisorCycle_apply_image {k : ℤ} {η : X} (hη : η ∈ genericPoints X)
    (hδ : relativeDimension C.dimensionFunction f η = k + 1)
    (z : (integralComponentAt η).subscheme) :
    (componentDivisorCycle C f L s hL hs hη hδ).1
        ((integralComponentAt η).subschemeι.base z) =
      (componentDivisorCycleOn C f L s hL hs hη hδ).1 z :=
  properPushforward_apply_image_of_isClosedImmersion C
    ((integralComponentAt η).subschemeι ≫ f) f (integralComponentAt η).subschemeι rfl k _ z

/-- **The coefficient of the pushforward vanishes off the component.** -/
theorem componentDivisorCycle_apply_eq_zero_of_notMem_range {k : ℤ} {η : X}
    (hη : η ∈ genericPoints X) (hδ : relativeDimension C.dimensionFunction f η = k + 1)
    {x : X} (hx : x ∉ Set.range (integralComponentAt η).subschemeι.base) :
    (componentDivisorCycle C f L s hL hs hη hδ).1 x = 0 :=
  properPushforward_apply_of_notMem_range C ((integralComponentAt η).subschemeι ≫ f) f
    (integralComponentAt η).subschemeι rfl k _ hx

end Stacks.Chow

end
