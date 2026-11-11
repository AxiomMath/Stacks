module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.FunctionFieldAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InvertibleSheafDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardCycles

/-!
# Pushforward of the divisor of a meromorphic section along a dominant morphism

In Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be proper, let `ℒ` be an
invertible sheaf on `Y`, assume `X` and `Y` integral, `f` dominant and
`dim_δ(X) = dim_δ(Y) = n`, and let `s` be a nonzero meromorphic section of `ℒ` on `Y`. Stacks
0EQS is the pair of assertions

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`

and, in `CH_{n-1}(Y)`,

`f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]`.

The source writes the right side of the second assertion as `c₁(ℒ) ∩ f_*[Y]`, which is a slip:
`f` goes from `X` to `Y`, and the source's own derivation of the second assertion from the first
uses `f_*[X] = [R(X) : R(Y)] [Y]`, so the right side is `c₁(ℒ) ∩ f_*[X]`.

This file contains the definition of the degree `[R(X) : R(Y)]`, the identity
`f_*[X] = [R(X) : R(Y)] [Y]`, and the reduction of the cycle identity to its coefficients at the
prime divisors of `Y`, for an arbitrary module `LX` and meromorphic section `σX` on `X` and an
arbitrary ratio family. Stacks 0EQS itself, both conclusions, with `f^*ℒ` the inverse image of
modules, `f^*s` the pullback of meromorphic sections and nothing assumed beyond the hypotheses
of the source, is `AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`
in `StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperPushforwardOfDivisorCanonical`, where the
coefficient identity at a prime divisor of `Y` is proved on an étale chart.

## Main definitions

* `AlgebraicGeometry.Space.functionFieldDegreeAtGenericPoint`: the degree `[R(X) : R(Y)]` of
  the extension of function fields which a morphism of integral good algebraic spaces induces
  at the generic point of `X`.
* `AlgebraicGeometry.Space.integralClosedSubspaceUniv`: the integral closed subspace of an
  integral good algebraic space on the whole of its space of points, whose cycle is the
  fundamental cycle `[X]`.
* `AlgebraicGeometry.Space.ProperPushforwardNormRule`: the coefficientwise form, at the prime
  divisors of `Y`, of the first conclusion of Stacks 0EQS, for the parameters `LX`, `σX` and the
  ratio families. It is a hypothesis of the reductions below, not a proved input.

## Main results

* `AlgebraicGeometry.Space.properPushforward_integralCycle_integralClosedSubspaceUniv`:
  `f_*[X] = [R(X) : R(Y)] [Y]` in `Z_n(Y)`, the identity the source uses to read its second
  assertion.
* `AlgebraicGeometry.Space.properPushforwardCoeff_divisorCycleCoefficients_eq_zero`: at an
  integral closed subspace of `Y` which is not a prime divisor the coefficient of
  `f_*(div_{f^*ℒ}(f^*s))` vanishes. This is where equality of the δ-dimensions is used.
* `AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection_eq_iff`: the cycle identity
  holds in `Z_{n-1}(Y)` if and only if it holds coefficientwise at every prime divisor of `Y`.
* `AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection` and
  `AlgebraicGeometry.Space.properPushforward_firstChernClassCapFundamental_of_normRule`:
  reductions of the two identities, for the parameters `LX`, `σX`, to the coefficientwise form
  `AlgebraicGeometry.Space.ProperPushforwardNormRule` of the first identity.
* `AlgebraicGeometry.Space.properPushforward_firstChernClassCapFundamental`: the reduction of
  the identity in the Chow group to the identity of cycles, which is how the source derives its
  second assertion from its first.

None of these is Stacks 0EQS: they carry the coefficientwise form of its first conclusion, or
the first conclusion itself, as a hypothesis. Stacks 0EQS, both conclusions, is
`AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`.

## Implementation notes

### How `[R(X) : R(Y)]` is read

The function field of an integral good algebraic space is the residue field at its generic
point, by Stacks 0END, and the extension `R(X)/R(Y)` which `f` induces is the homomorphism of
residue fields at the generic point of `X`; that is how Stacks 0ENY phrases the extension — in
the namespace `AlgebraicGeometry.Space`, under the name
`factorsThrough_properIntegralClosedSubspace_or_isDominant_and_finite_functionField` — and
0ENY is what makes it finite under the hypotheses of the source. So `[R(X) : R(Y)]` is
`Module.finrank` of that extension, which is exactly `AlgebraicGeometry.Space.functionFieldDegree`
— the degree Stacks 0EP1 uses for the coefficients of the pushforward — evaluated at the
integral closed subspace of `X` whose generic point is the generic point of `X`. The definition
below is that evaluation, so the degree in the statements is literally the same constant that
the pushforward of cycles uses. Since `Module.finrank` is `0` on an extension which is not
finite, no finiteness hypothesis is needed to form it.

### The parameters `LX`, `σX` and the ratio families

The statements of this file take a module `LX` and a meromorphic section `σX` on `X`, and ratio
families on both sides, as free parameters; nothing here needs `LX` to be `f^*ℒ` or `σX` to be
`f^*s`, so the equivalence `properPushforward_divisorCycleOfSection_eq_iff` holds in that
generality. Properness of `f` enters the pushforward of cycles of Stacks 0EP1 only through
quasi-compactness, which is what these statements ask for.

### Agreement away from the prime divisors of `Y`

An integral closed subspace `Z ⊆ X` with a nonzero `div`-coefficient is a prime divisor of `X`,
hence has δ-dimension `n - 1` by Stacks 0EPZ; a nonzero degree forces its image closure to have
the same δ-dimension by Stacks 0EP1, part (1); and `dim_δ(Y) = n` then makes that image closure
a prime divisor of `Y`, again by Stacks 0EPZ. So off the prime divisors of `Y` the pushforward
has no contribution at all, while the right side vanishes because `div_ℒ(s)` does.

### `c₁(ℒ) ∩ [X]` and the second identity

The second identity is the image of the first under the class map of the Chow group, which is
how the source derives it. On the left, `c₁(f^*ℒ) ∩ [X]` is by definition — Stacks 0EQE,
part (2) — the class of `div_{f^*ℒ}(f^*s)`, so `f_*(c₁(f^*ℒ) ∩ [X])` is the class on `Y` of the
pushforward cycle (proper pushforward respects rational equivalence by Stacks 0EQC). On the
right, `c₁(ℒ) ∩ f_*[X]` is `[R(X) : R(Y)] · (c₁(ℒ) ∩ [Y])`, by `f_*[X] = [R(X) : R(Y)] [Y]`.

### `List.TFAE.out` is one-based here

`List.TFAE.out i j` in this repository elaborates its side conditions at `l[i - 1]?` and
`l[j - 1]?`, so on the three-clause `AlgebraicGeometry.Space.isPrimeDivisor_tfae_of_isIntegralSpace`
the clause `codimension … = 1` is index `2` and `deltaDimension … = n - 1` is index `3`.

## References

* [Stacks Project, Tag 0EQS](https://stacks.math.columbia.edu/tag/0EQS)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0ENY](https://stacks.math.columbia.edu/tag/0ENY)
* [Stacks Project, Tag 0EPZ](https://stacks.math.columbia.edu/tag/0EPZ)
* [Stacks Project, Tag 0EP1](https://stacks.math.columbia.edu/tag/0EP1)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
* [Stacks Project, Tag 0EQC](https://stacks.math.columbia.edu/tag/0EQC)
* [Stacks Project, Tag 0EQE](https://stacks.math.columbia.edu/tag/0EQE)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u w v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology
attribute [local instance] Classical.propDecidable

/-! ### The degree of the extension of function fields at the generic point -/

section Degree

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- The degree `[R(X) : R(Y)]` of the extension of function fields which a morphism
`f : X ⟶ Y` of good algebraic spaces induces at the generic point of an integral `X`.

The function field of an integral good algebraic space is its residue field at its generic
point, by Stacks 0END, so this is the degree of the extension of residue fields that Stacks
0ENY asserts to be finite when `Y` is integral, `f` is dominant and the δ-dimensions agree. It
is `AlgebraicGeometry.Space.functionFieldDegree` — the degree Stacks 0EP1 uses for the
coefficients of the pushforward of cycles — at the integral closed subspace of `X` whose
generic point is the generic point of `X`, so it is the same constant and not a second
spelling of it; hence it too is `0` when the extension is not finite. -/
def functionFieldDegreeAtGenericPoint (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hXInt : IsIntegralSpace D.site D.base D.base_mem X) (f : X ⟶ Y) : ℕ :=
  functionFieldDegree D sX hX sY hY f
    (integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX)
      (genericPoint D.site D.base D.base_mem hX.1 hXInt))

end Degree

/-! ### The fundamental cycle and its pushforward -/

section FundamentalCycle

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hXInt : IsIntegralSpace D.site D.base D.base_mem X)

/-- The integral closed subspace of an integral good algebraic space on the whole of its space
of points: the one whose generic point is the generic point of the space. Its cycle is the
fundamental cycle `[X]`. -/
abbrev integralClosedSubspaceUniv : IntegralClosedSubspace D.site D.base D.base_mem X :=
  integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
    (D.isDecentSpace_of_isGood sX hX) (genericPoint D.site D.base D.base_mem hX.1 hXInt)

/-- The δ-dimension of the whole of an integral good algebraic space of δ-dimension `n` is `n`:
the generic point of the space is the generic point of its own point set, and the δ-dimension of
the whole space is the induced dimension function there. -/
theorem deltaDimension_integralClosedSubspaceUniv {n : ℤ}
    (hn : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt)) :
    deltaDimension D sX (integralClosedSubspaceUniv D sX hX hXInt) = n := by
  rw [deltaDimension_eq_of_isGenericPoint D sX hX.1 _
    (genericPoint D.site D.base D.base_mem hX.1 hXInt)
    (isGenericPoint_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) (genericPoint D.site D.base D.base_mem hX.1 hXInt))]
  exact WithBotTop.coe_injective
    ((deltaDimensionClosed_univ_eq_inducedDimensionValue_genericPoint D sX hX hXInt).symm.trans hn)

/-- Under a dominant morphism the whole of `X` has the whole of `Y` for the closure of the image
of its point set: the image is dense, so that closure is everything, and an integral closed
subspace is determined by a generic point of its point set. -/
theorem closureImage_integralClosedSubspaceUniv
    (hYInt : IsIntegralSpace D.site D.base D.base_mem Y) (f : X ⟶ Y)
    (hdom : IsDominant D.site D.base D.base_mem f) :
    IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f (integralClosedSubspaceUniv D sX hX hXInt) =
      integralClosedSubspaceUniv D sY hY hYInt := by
  refine eq_integralClosedSubspaceOfPoint D.site D.base D.base_mem hY.1
    (D.isDecentSpace_of_isGood sY hY) _ _ ?_
  rw [IntegralClosedSubspace.subspacePointSet_closureImage D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY) f (integralClosedSubspaceUniv D sX hX hXInt),
    subspacePointSet_integralClosedSubspaceOfPoint D.site D.base D.base_mem hX.1
      (D.isDecentSpace_of_isGood sX hX) (genericPoint D.site D.base D.base_mem hX.1 hXInt),
    isGenericPoint_genericPoint D.site D.base D.base_mem hX.1 hXInt, Set.image_univ,
    hdom.closure_range]
  exact isGenericPoint_genericPoint D.site D.base D.base_mem hY.1 hYInt

/-- The degree of Stacks 0EP1, part (1), at the whole of `X` is the degree `[R(X) : R(Y)]`: the
δ-dimension does not drop, both the whole of `X` and the whole of `Y` having δ-dimension `n`. -/
theorem properCycleDegree_integralClosedSubspaceUniv
    (hYInt : IsIntegralSpace D.site D.base D.base_mem Y) {f : X ⟶ Y}
    (hdom : IsDominant D.site D.base D.base_mem f) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) :
    properCycleDegree D sX hX sY hY f (integralClosedSubspaceUniv D sX hX hXInt) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hXInt f : ℤ) := by
  have hc : deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
        hY.1 (D.isDecentSpace_of_isGood sY hY) f (integralClosedSubspaceUniv D sX hX hXInt)) =
      deltaDimension D sX (integralClosedSubspaceUniv D sX hX hXInt) := by
    rw [closureImage_integralClosedSubspaceUniv D sX hX sY hY hXInt hYInt f hdom,
      deltaDimension_integralClosedSubspaceUniv D sY hY hYInt hnY,
      deltaDimension_integralClosedSubspaceUniv D sX hX hXInt hnX]
  change (if deltaDimension D sY (IntegralClosedSubspace.closureImage D.site D.base D.base_mem
      hY.1 (D.isDecentSpace_of_isGood sY hY) f (integralClosedSubspaceUniv D sX hX hXInt)) =
        deltaDimension D sX (integralClosedSubspaceUniv D sX hX hXInt) then
    ((functionFieldDegree D sX hX sY hY f (integralClosedSubspaceUniv D sX hX hXInt) : ℤ))
    else 0) = _
  split_ifs
  rfl

/-- The coefficient of an integer multiple of a cycle is the multiple of the coefficient. -/
private theorem cycleGroup_zsmul_apply {k : ℤ} (c : CycleGroup D sY k) (d : ℤ)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) : (d • c).1 Z = d * c.1 Z := by
  change d • c.1 Z = d * c.1 Z
  rw [zsmul_eq_mul, Int.cast_id]

/-- **Stacks 0EP1 at the fundamental cycle.** For a dominant quasi-compact morphism `f : X ⟶ Y`
over `B` of integral good algebraic spaces with `dim_δ(X) = dim_δ(Y) = n`,

`f_*[X] = [R(X) : R(Y)] [Y]` in `Z_n(Y)`.

The whole of `X` is the only integral closed subspace carrying a coefficient of `[X]`, its image
closure is the whole of `Y`, and the degree there is `[R(X) : R(Y)]` because the δ-dimension does
not drop. This is the identity the source uses to read its second conclusion. -/
@[stacks 0EP1 "f_*[X] = [R(X):R(Y)] [Y]: the pushforward of the fundamental cycle of an integral
good X along a dominant quasi-compact morphism to an integral good Y of the same δ-dimension"]
theorem properPushforward_integralCycle_integralClosedSubspaceUniv
    (hYInt : IsIntegralSpace D.site D.base D.base_mem Y) {f : X ⟶ Y}
    (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) :
    properCyclePushforward D sX hX sY hY hfB hf n (integralCycle D sX n
          (integralClosedSubspaceUniv D sX hX hXInt)
          (deltaDimension_integralClosedSubspaceUniv D sX hX hXInt hnX)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hXInt f : ℤ) •
        integralCycle D sY n (integralClosedSubspaceUniv D sY hY hYInt)
          (deltaDimension_integralClosedSubspaceUniv D sY hY hYInt hnY) := by
  refine Subtype.ext (funext fun Z' => ?_)
  have hlhs : (properCyclePushforward D sX hX sY hY hfB hf n (integralCycle D sX n
        (integralClosedSubspaceUniv D sX hX hXInt)
        (deltaDimension_integralClosedSubspaceUniv D sX hX hXInt hnX))).1 Z' =
      properCycleMult D sX hX sY hY f (integralClosedSubspaceUniv D sX hX hXInt) Z' := by
    rw [properPushforward_apply, integralCycle_coe,
      finsum_eq_single _ (integralClosedSubspaceUniv D sX hX hXInt) fun W hW => by
        rw [integralCycleCoeff_eq_zero D _ hW, zero_mul],
      integralCycleCoeff_self, one_mul]
  have hmult : properCycleMult D sX hX sY hY f (integralClosedSubspaceUniv D sX hX hXInt) Z' =
      if integralClosedSubspaceUniv D sY hY hYInt = Z' then
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hXInt f : ℤ) else 0 := by
    change (if IntegralClosedSubspace.closureImage D.site D.base D.base_mem hY.1
        (D.isDecentSpace_of_isGood sY hY) f (integralClosedSubspaceUniv D sX hX hXInt) = Z' then
      properCycleDegree D sX hX sY hY f (integralClosedSubspaceUniv D sX hX hXInt) else 0) = _
    rw [closureImage_integralClosedSubspaceUniv D sX hX sY hY hXInt hYInt f hdom,
      properCycleDegree_integralClosedSubspaceUniv D sX hX sY hY hXInt hYInt hdom hnX hnY]
  rw [hlhs, hmult]
  rw [cycleGroup_zsmul_apply]
  change _ = _ * integralCycleCoeff D (integralClosedSubspaceUniv D sY hY hYInt) Z'
  split_ifs with h
  · rw [← h, integralCycleCoeff_self, mul_one]
  · rw [integralCycleCoeff_eq_zero D _ (fun hc => h hc.symm), mul_zero]

end FundamentalCycle

/-! ### Away from the prime divisors of the target -/

section Reduction

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]

variable (LX : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (σX : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 LX)
    (ratioX : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdecX LX)

/-- **The content of the reduction of Stacks 0EQS.** At an integral closed subspace `Z' ⊆ Y`
which is not a prime divisor the coefficient of `f_*(div_{LX}(σX))` is zero, for any module
`LX` on `X` and any nonzero meromorphic section `σX` of it — in particular for `f^*ℒ` and
`f^*s`.

An integral closed subspace `Z ⊆ X` contributing to that coefficient has a nonzero
`div`-coefficient, hence is a prime divisor of `X` and so has δ-dimension `n - 1` by Stacks
0EPZ, and has a nonzero degree, which forces its image closure `Z'` to have the same
δ-dimension by Stacks 0EP1, part (1). Since `dim_δ(Y) = n` as well, Stacks 0EPZ on `Y` makes
`Z'` a prime divisor of `Y`. -/
theorem properPushforwardCoeff_divisorCycleCoefficients_eq_zero
    (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    (dY : DimensionFunction (points D.site D.base D.base_mem Y))
    (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt)) (f : X ⟶ Y)
    {Z' : IntegralClosedSubspace D.site D.base D.base_mem Y}
    (hZ' : codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z') ≠ 1) :
    properCyclePushforwardCoeff D sX hX sY hY f
      (divisorCycleCoefficients D sX hX hdecX LX σX ratioX) Z' = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun Z => ?_
  by_cases hα : divisorCycleCoefficients D sX hX hdecX LX σX ratioX Z = 0
  · rw [hα, zero_mul]
  by_cases hm : properCycleMult D sX hX sY hY f Z Z' = 0
  · rw [hm, mul_zero]
  obtain ⟨him, hdeg⟩ := (properCycleMult_ne_zero_iff D sX hX sY hY f Z Z').1 hm
  have hcodX :
      codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hX.1 Z) = 1 := by
    by_contra hc
    exact hα (divisorCycleCoefficients_of_codimension_ne_one D sX hX hdecX LX σX ratioX hc)
  have hδX : deltaDimension D sX Z = n - 1 :=
    ((isPrimeDivisor_tfae_of_isIntegralSpace D sX hX hintX dX hdX hnX Z).out 2 3).mp hcodX
  have hδY := deltaDimension_closureImage_of_properCycleDegree_ne_zero D sX hX sY hY f hdeg
  rw [him, hδX] at hδY
  exact absurd
    (((isPrimeDivisor_tfae_of_isIntegralSpace D sY hY hintY dY hdY hnY Z').out 3 2).mp hδY) hZ'

end Reduction

/-! ### The two identities of Stacks 0EQS -/

section Identities

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY)
    (hdecX : IsDecentSpace D.site D.base D.base_mem X)
    (hdecY : IsDecentSpace D.site D.base D.base_mem Y)

variable [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem X,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hX.1 hdecX)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Nontrivial ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    IsNoetherianRing ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]
  [∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    Ring.KrullDimLE 1 ↥(W.genericHenselianLocalRing D.site D.base D.base_mem hY.1 hdecY)]

variable (LX : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (σX : MeromorphicSection.{u, u} D.site D.base D.base_mem X hX.1 LX)
    (ratioX : LocalRatioFamily.{u, u} D.site D.base D.base_mem hX.1 hdecX LX)
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (σ : MeromorphicSection.{u, u} D.site D.base D.base_mem Y hY.1 L)
    (ratio : LocalRatioFamily.{u, u} D.site D.base D.base_mem hY.1 hdecY L)

variable (hintX : IsIntegralSpace D.site D.base D.base_mem X)
    (hintY : IsIntegralSpace D.site D.base D.base_mem Y)
    (dX : DimensionFunction (points D.site D.base D.base_mem X))
    (hdX : ∀ x, dX x = D.deltaValue sX x)
    (dY : DimensionFunction (points D.site D.base D.base_mem Y))
    (hdY : ∀ y, dY y = D.deltaValue sY y) {n : ℤ}
    (hnX : deltaDimensionClosed D sX hX Set.univ isClosed_univ = (n : EInt))
    (hnY : deltaDimensionClosed D sY hY Set.univ isClosed_univ = (n : EInt))

/-- **Reduction of the cycle identity of Stacks 0EQS to its coefficients at the prime divisors
of `Y`.** For arbitrary parameters `LX`, `σX` on `X` and ratio families (not required to be
`f^*ℒ`, `f^*s`), in Situation 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be dominant
and quasi-compact over `B`, let `X` and `Y` be integral with `dim_δ(X) = dim_δ(Y) = n`, let `ℒ`
be an invertible `𝒪_Y`-module and let `s` be a nonzero meromorphic section of `ℒ`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`

holds exactly when it holds coefficientwise at every prime divisor of `Y`, that is when

`∑_Z ord_{Z, f^*ℒ}(f^*s) · deg(Z/Z') = [R(X) : R(Y)] · ord_{Z', ℒ}(s)`

for every prime divisor `Z' ⊆ Y`, the sum being over the integral closed subspaces `Z ⊆ X`.

Both sides are coefficient families on the integral closed subspaces of `Y`, and away from the
prime divisors of `Y` both vanish: the coefficient of `div_ℒ(s)` at an integral closed subspace
whose point set does not have codimension one is zero by Stacks 0EQE, part (1), and the
pushforward has no contribution there by
`AlgebraicGeometry.Space.properPushforwardCoeff_divisorCycleCoefficients_eq_zero`, which is
where the equality of the δ-dimensions is used. For `f` proper, `LX = f^*ℒ`, `σX = f^*s` and
the canonical generators, the coefficient identity at a prime divisor of `Y` is
`AlgebraicGeometry.Space.finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq`, and
Stacks 0EQS itself is `AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`.
-/
theorem properPushforward_divisorCycleOfSection_eq_iff (_hL : IsInvertibleSheaf D sY hY L)
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (_hdom : IsDominant D.site D.base D.base_mem f)
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX LX σX ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
          (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX) =
        (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
          divisorCycleOfSection D sY hY hdecY L σ ratio hDvY hintY dY hdY hnY ↔
      ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
        (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
            divisorCycleCoefficients D sX hX hdecX LX σX ratioX Z *
              properCycleMult D sX hX sY hY f Z
                (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
          (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
            divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W := by
  constructor
  · intro heq W
    have h := congrArg (fun c : CycleGroup D sY (n - 1) =>
      c.1 (W.toIntegralClosedSubspace D.site D.base D.base_mem)) heq
    rw [properPushforward_apply, divisorCycleOfSection_coe, cycleGroup_zsmul_apply,
      divisorCycleOfSection_coe,
      divisorCycleCoefficients_toIntegralClosedSubspace] at h
    exact h
  · intro hW
    refine Subtype.ext (funext fun Z' => ?_)
    rw [cycleGroup_zsmul_apply, divisorCycleOfSection_coe]
    have hlhs : (properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX)).1 Z' =
        ∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
          divisorCycleCoefficients D sX hX hdecX LX σX ratioX Z *
            properCycleMult D sX hX sY hY f Z Z' := by
      rw [properPushforward_apply, divisorCycleOfSection_coe]
    rw [hlhs]
    by_cases hcod :
        codimension (integralClosedSubspaceSupport D.site D.base D.base_mem hY.1 Z') = 1
    · have h := hW (Z'.toPrimeDivisor D.site D.base D.base_mem hY.1 hcod)
      rw [IntegralClosedSubspace.toIntegralClosedSubspace_toPrimeDivisor] at h
      rw [h, divisorCycleCoefficients_of_codimension_eq_one D sY hY hdecY L σ ratio hcod]
    · rw [divisorCycleCoefficients_of_codimension_ne_one D sY hY hdecY L σ ratio hcod, mul_zero,
        ← properCyclePushforwardCoeff]
      exact properPushforwardCoeff_divisorCycleCoefficients_eq_zero D sX hX sY hY hdecX LX σX
        ratioX hintX hintY dX hdX dY hdY hnX hnY f hcod

/-- **The first conclusion of Stacks 0EQS, coefficientwise at the prime divisors of `Y`**, for
the parameters `LX`, `σX` and the ratio families. For every prime divisor `Z' ⊆ Y`,

`∑_Z ord_{Z, LX}(σX) · deg(Z/Z') = [R(X) : R(Y)] · ord_{Z', ℒ}(s)`,

the sum being over the integral closed subspaces `Z ⊆ X`, which is effectively over the prime
divisors of `X` whose image closure is `Z'`.

By `AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection_eq_iff` this is equivalent to
the cycle identity `f_*(div_{LX}(σX)) = [R(X) : R(Y)] div_ℒ(s)` itself, so it is not an
independent input: a statement taking it as a hypothesis assumes the first conclusion of Stacks
0EQS. Since `LX`, `σX` are free, it does not hold in general; for `f` proper, `LX = f^*ℒ`,
`σX = f^*s` and the canonical generators it is proved, as
`AlgebraicGeometry.Space.finsum_canonicalDivisorCycle_pullback_mul_properCycleMult_eq` (the input
the source obtains from Stacks 0EQ4), and Stacks 0EQS itself is
`AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`. -/
structure ProperPushforwardNormRule (f : X ⟶ Y) : Prop where
  /-- The coefficient of `f_*(div_{LX}(σX))` at each prime divisor of `Y` is `[R(X) : R(Y)]`
  times the coefficient of `div_ℒ(s)` there. -/
  coeff_eq : ∀ W : PrimeDivisor D.site D.base D.base_mem Y,
    (∑ᶠ Z : IntegralClosedSubspace D.site D.base D.base_mem X,
        divisorCycleCoefficients D sX hX hdecX LX σX ratioX Z *
          properCycleMult D sX hX sY hY f Z
            (W.toIntegralClosedSubspace D.site D.base D.base_mem)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) *
        divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W

/-- **Reduction of the cycle identity of Stacks 0EQS to its coefficientwise form.** This is not
Stacks 0EQS: `LX`, `σX` are free and the hypothesis `hnorm` is the conclusion read at each
prime divisor of `Y`. In Situation 0EDT let
`X/B` and `Y/B` be good, let `f : X ⟶ Y` be dominant and quasi-compact over `B`, let `X` and
`Y` be integral with `dim_δ(X) = dim_δ(Y) = n`, let `ℒ` be an invertible `𝒪_Y`-module and let
`s` be a nonzero meromorphic section of `ℒ`. Then

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`.

Here `LX`, `σX` and the ratio families are parameters and the coefficient identity at the prime
divisors of `Y` is the argument `hnorm`; the agreement away from the prime divisors of `Y` is
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection_eq_iff`. Stacks 0EQS itself is
`AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`. -/
theorem properPushforward_divisorCycleOfSection (hL : IsInvertibleSheaf D sY hY L)
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX LX σX ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    (hnorm : ProperPushforwardNormRule D sX hX sY hY hdecX hdecY LX σX ratioX L σ ratio
      hintX f) :
    properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        divisorCycleOfSection D sY hY hdecY L σ ratio hDvY hintY dY hdY hnY :=
  (properPushforward_divisorCycleOfSection_eq_iff D sX hX sY hY hdecX hdecY LX σX ratioX L σ
    ratio hintX hintY dX hdX dY hdY hnX hnY hL hfB hf hdom hDvX hDvY).mpr hnorm.coeff_eq

/-- **Reduction of the Chow-group identity of Stacks 0EQS to the coefficientwise form of the
cycle identity.** This is not Stacks 0EQS: `LX`, `σX` are free and `hnorm` is the first
conclusion read at each prime divisor of `Y`. In the situation above,

`f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]` in `CH_{n-1}(Y)`,

the right side being `[R(X) : R(Y)] · (c₁(ℒ) ∩ [Y])` by
`AlgebraicGeometry.Space.properPushforward_integralCycle_integralClosedSubspaceUniv`, which is
`f_*[X] = [R(X) : R(Y)] [Y]`.

It follows from the coefficient identity `hnorm` through
`AlgebraicGeometry.Space.properPushforward_divisorCycleOfSection`. Stacks 0EQS itself is
`AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`. -/
theorem properPushforward_firstChernClassCapFundamental_of_normRule
    (hL : IsInvertibleSheaf D sY hY L)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sY hY (n - 1) CH)
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (hdom : IsDominant D.site D.base D.base_mem f)
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX LX σX ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    (hnorm : ProperPushforwardNormRule D sX hX sY hY hdecX hdecY LX σX ratioX L σ ratio
      hintX f) :
    chow.cls (properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        firstChernClassCapFundamental D sY hY hdecY L chow σ ratio hDvY hintY dY hdY hnY := by
  rw [properPushforward_divisorCycleOfSection D sX hX sY hY hdecX hdecY LX σX ratioX L σ ratio
    hintX hintY dX hdX dY hdY hnX hnY hL hfB hf hdom hDvX hDvY hnorm, map_zsmul]
  rfl

/-- **Reduction of the Chow-group identity of Stacks 0EQS to the cycle identity.** This is not
Stacks 0EQS: `LX`, `σX` are free and the first conclusion is the hypothesis `heq`. In the
situation above, if

`f_*(div_{f^*ℒ}(f^*s)) = [R(X) : R(Y)] div_ℒ(s)` in `Z_{n-1}(Y)`,

which is the first conclusion of the source, given as `heq`, then

`f_*(c₁(f^*ℒ) ∩ [X]) = c₁(ℒ) ∩ f_*[X]` in `CH_{n-1}(Y)`,

the right side being `[R(X) : R(Y)] · (c₁(ℒ) ∩ [Y])` by `f_*[X] = [R(X) : R(Y)] [Y]`.

This is the source's own derivation of its second conclusion from its first. On the left,
`c₁(f^*ℒ) ∩ [X]` is by Stacks 0EQE, part (2), the class of `div_{f^*ℒ}(f^*s)`, and the left
side is the class on `Y` of the pushforward cycle (proper pushforward respects rational
equivalence by Stacks 0EQC). On the right, `c₁(ℒ) ∩ [Y]` is again Stacks 0EQE, part (2),
`AlgebraicGeometry.Space.firstChernClassCapFundamental`, a class independent of the chosen
nonzero meromorphic section by
`AlgebraicGeometry.Space.firstChernClassCapFundamental_eq`, so the second identity is the image
of the first under the class map of the Chow group. Stacks 0EQS itself, with the first
conclusion proved, is `AlgebraicGeometry.Space.properCyclePushforward_sectionWeilDivisor_pullback`.
-/
theorem properPushforward_firstChernClassCapFundamental (_hL : IsInvertibleSheaf D sY hY L)
    {CH : Type w} [AddCommGroup CH] (chow : ChowTarget.{u, w, v} D sY hY (n - 1) CH)
    {f : X ⟶ Y} (hfB : f ≫ sY = sX) (hf : IsQuasiCompact D.site D.base D.base_mem f)
    (_hdom : IsDominant D.site D.base D.base_mem f)
    (hDvX : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem X =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hX.1 hdecX LX σX ratioX W = 0 then ∅
      else W.support D.site D.base D.base_mem X)
    (hDvY : LocallyFinite fun W : PrimeDivisor D.site D.base D.base_mem Y =>
      if divisorCoefficients.{u, u} D.site D.base D.base_mem hY.1 hdecY L σ ratio W = 0 then ∅
      else W.support D.site D.base D.base_mem Y)
    (heq : properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        divisorCycleOfSection D sY hY hdecY L σ ratio hDvY hintY dY hdY hnY) :
    chow.cls (properCyclePushforward D sX hX sY hY hfB hf (n - 1)
        (divisorCycleOfSection D sX hX hdecX LX σX ratioX hDvX hintX dX hdX hnX)) =
      (functionFieldDegreeAtGenericPoint D sX hX sY hY hintX f : ℤ) •
        firstChernClassCapFundamental D sY hY hdecY L chow σ ratio hDvY hintY dY hdY hnY := by
  rw [heq, map_zsmul]
  rfl

end Identities

end AlgebraicGeometry.Space

end
