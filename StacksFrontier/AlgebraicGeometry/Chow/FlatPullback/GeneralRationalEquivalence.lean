module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.RationalEquivalenceFinsum
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisorEquivalence
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat pullback preserves rational equivalence

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X'` and `X` be
schemes locally of finite type over `S` and let `f : X' ⟶ X` be flat and locally of finite type of
relative dimension `r`. This file proves that flat pullback of `k`-cycles along `f` carries cycles
rationally equivalent to zero to cycles rationally equivalent to zero, so that it descends to a
map `A_k(X) ⟶ A_{k+r}(X')` of Chow groups.

A rational equivalence on `X` is presented, by Stacks 02RW, by a locally finite family `(W_j)_j` of
integral closed subschemes of `X` of delta-dimension `k + 1` together with nonzero rational
functions `g_j` on them: the given cycle has coefficients `∑_j (i_j)_* div_{W_j}(g_j)`. The
pullback of a single term is rewritten by the closed-immersion case of Stacks 02RG as a pushforward
from the scheme-theoretic inverse image `f^{-1}(W_j)`,

  `f^*((i_j)_* div_{W_j}(g_j)) = (i'_j)_* (g_j^* div_{W_j}(g_j))`,

where `g_j : f^{-1}(W_j) ⟶ W_j` is the restriction of `f`, again flat of relative dimension `r`.
Each summand on the right is a pushforward of a cycle *living on* `f^{-1}(W_j)` which is rationally
equivalent to zero there, by the case of Stacks 02S1 for a principal divisor on an integral target;
and the inverse images form a locally finite family because their supports are the preimages of the
supports of the `W_j` (Stacks 02R9). So Stacks 02RZ assembles the sum into a single rational
equivalence on `X'`.

## Main results

* `Stacks.Chow.exists_rationallyEquivalentToZero_comap_principalDivisor` — the pullback of one
  term of a presentation, as a pushforward from the inverse image of a cycle rationally equivalent
  to zero.
* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general` — **Stacks 02S1 for an
  arbitrary flat morphism of relative dimension `r`**.
* `Stacks.Chow.flatPullbackChowOfRelativeDimension` — the induced map `A_k(X) ⟶ A_{k+r}(X')` on
  Chow groups, carrying no hypothesis.

## Implementation notes

`Stacks.Chow.principalDivisorCycle` reads `div(g)` on a scheme of delta-dimension `n` as an element
of `Z_{n-1}(X)`. Applied to a member of a presentation, whose delta-dimension is `k + 1`, that is
`Z_{(k+1)-1}(W_j)` while everything downstream is graded by `k`; the two indices are equal integers
and distinct terms. Rather than transport along that equality,
`Stacks.Chow.exists_rationallyEquivalentToZero_comap_principalDivisor` builds `div(g_j)` directly
in `Z_k(W_j)` from `Stacks.Chow.principalCycle_mem_cyclesOfDimension`, so that the
closed-immersion case of Stacks 02RG applies at the index `k` on the nose and no cast appears in
the assembly. The case of Stacks 02S1 for a principal divisor is stated in the flexible
coefficientwise form precisely so that it can be read against that cycle.

The index type of the presenting family is carried unchanged from the hypothesis to the conclusion,
so no universe bookkeeping is needed: `Stacks.Chow.IsRationallyEquivalentToZero` quantifies the
index type over `Type u` and
`Stacks.Chow.rationallyEquivalentToZero_finsum_of_isClosedImmersion` consumes one from `Type u`.

## References

* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02R9](https://stacks.math.columbia.edu/tag/02R9)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The pullback of one term of a presentation -/

/-- **The flat pullback of one term of a presentation of a rational equivalence.** Let `W ⊆ X` be
an integral closed subscheme of delta-dimension `k + 1` carrying a nonzero rational function `g`,
and let `f : X' ⟶ X` be flat of relative dimension `r`. There is a `(k + r)`-cycle on the
scheme-theoretic inverse image `f^{-1}(W)`, rationally equivalent to zero there, whose pushforward
to `X'` has the coefficients of `f^*((i)_* div_W(g))`.

The cycle is the flat pullback of `div_W(g)` along the restriction `f^{-1}(W) ⟶ W`, which is
rationally equivalent to zero by the case of Stacks 02S1 for a principal divisor on an integral
target; that its pushforward has the stated coefficients is the closed-immersion case of
Stacks 02RG. -/
theorem exists_rationallyEquivalentToZero_comap_principalDivisor (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ)
    (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    ∃ β : CycleGroup C ((V.comap f).subschemeι ≫ sX') (k + (r : ℤ)),
      IsRationallyEquivalentToZero C ((V.comap f).subschemeι ≫ sX') (k + (r : ℤ)) β ∧
        ∀ x' : X', (properPushforward C ((V.comap f).subschemeι ≫ sX') sX'
              (V.comap f).subschemeι rfl (k + (r : ℤ)) β).1 x' =
            principalDivisorPushforward C sX V hV g (f.base x') *
              flatPullbackWeight C sX' f (k + (r : ℤ)) x' := by
  let _ := hV
  let _ : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ sX)
  let _ := locallyOfFiniteType_comapRestrict V f
  let _ := flat_comapRestrict V f
  have hune : (rationalFunctionsEquivFunctionField V.subscheme).1
      (g : rationalFunctions V.subscheme) ≠ 0 := fun h ↦
    g.ne_zero ((rationalFunctionsEquivFunctionField V.subscheme).1.injective
      (h.trans (map_zero _).symm))
  -- `div(g)` read as a `k`-cycle on `W`, rather than as a `((k + 1) - 1)`-cycle.
  have hmem : principalCycle V.subscheme ((rationalFunctionsEquivFunctionField V.subscheme).1
      (g : rationalFunctions V.subscheme)) ∈ cyclesOfDimension C (V.subschemeι ≫ sX) k := by
    rw [show k = k + 1 - 1 from by ring]
    exact principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ sX) hdim _
  refine ⟨flatPullback C ((V.comap f).subschemeι ≫ sX') (V.subschemeι ≫ sX) (comapRestrict V f)
    (comapRestrict_comp_base C sX' sX f hbase V) r (relativeDimension_comapRestrict V f hf) k
    ⟨_, hmem⟩, ?_, ?_⟩
  · -- Stacks 02S1 for a principal divisor on an integral target.
    refine isRationallyEquivalentToZero_of_coe_eq_flatPullback_principalDivisorCycle C
      ((V.comap f).subschemeι ≫ sX') (V.subschemeι ≫ sX) (comapRestrict V f)
      (comapRestrict_comp_base C sX' sX f hbase V) r (relativeDimension_comapRestrict V f hf)
      hdim hune (by ring) _ fun z ↦ ?_
    rw [flatPullback_apply, flatPullback_apply,
      show (k + 1 : ℤ) - 1 + (r : ℤ) = k + (r : ℤ) from by ring]
    rfl
  · intro x'
    -- The term of the presentation, read as a pushforward of a cycle on `W`.
    have hbridge : principalDivisorPushforward C sX V hV g (f.base x') =
        (properPushforward C (V.subschemeι ≫ sX) sX V.subschemeι rfl k
          (⟨_, hmem⟩ : CycleGroup C (V.subschemeι ≫ sX) k)).1 (f.base x') := by
      by_cases hy : f.base x' ∈ Set.range V.subschemeι.base
      · obtain ⟨z, hz⟩ := hy
        rw [← hz, properPushforward_apply_image_of_isClosedImmersion,
          principalDivisorPushforward_eq, closedSubschemeCyclePushforward_apply]
      · rw [principalDivisorPushforward_eq,
          closedSubschemeCyclePushforward_apply_of_notMem_range C sX V _ hy,
          properPushforward_apply_of_notMem_range C (V.subschemeι ≫ sX) sX V.subschemeι rfl k
            _ hy]
    rw [← flatPullback_properPushforward_comap C sX' sX f hbase r hf k V ⟨_, hmem⟩,
      flatPullback_apply, hbridge]

/-! ### Stacks 02S1 -/

/-- **Stacks 02S1.** Flat pullback of `k`-cycles along a morphism `f : X' ⟶ X` of schemes locally
of finite type over the base which is flat and locally of finite type of relative dimension `r`
carries cycles rationally equivalent to zero to cycles rationally equivalent to zero.

A presentation `∑_j (i_j)_* div_{W_j}(g_j)` of a rational equivalence on `X` by a locally finite
family of integral closed subschemes `W_j ⊆ X` of delta-dimension `k + 1` is pulled back term by
term. The closed-immersion case of Stacks 02RG rewrites the pullback of each term as a pushforward
from the scheme-theoretic inverse image `f^{-1}(W_j)` of a cycle on `f^{-1}(W_j)`, which is
rationally equivalent to zero there by the case of Stacks 02S1 for a principal divisor on an
integral target. Those inverse images have as supports the preimages of the supports of the `W_j`,
so they form a locally finite family by Stacks 02R9, and Stacks 02RZ sums the pushforwards into a
single rational equivalence. -/
@[stacks 02S1 "the general case: an arbitrary flat morphism of relative dimension r"]
theorem flatPullbackFactorsThroughRationalEquivalence_general (C : ChowSituation.{u})
    {X' X : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f]
    (hbase : f ≫ sX = sX') (r : ℕ) (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) :
    FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase r hf k := by
  intro α hα
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  choose β hβzero hβcoeff using fun j : J ↦
    exists_rationallyEquivalentToZero_comap_principalDivisor C sX' sX f hbase r hf k
      (W j) (hW j) (hDim j) (g j)
  refine rationallyEquivalentToZero_finsum_of_isClosedImmersion C sX' (k + (r : ℤ))
    (fun j : J ↦ ((W j).comap f).subschemeι) ?_ β hβzero _ fun x' ↦ ?_
  · -- Stacks 02R9: the inverse images are the preimages of a locally finite family.
    refine (hLocal.preimage_continuous f.continuous).subset fun j ↦ ?_
    have hrange : Set.range (((W j).comap f).subschemeι.base) =
        f.base ⁻¹' ((W j).support : Set X) := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap,
        Closeds.coe_preimage]
    exact hrange.subset
  · rw [flatPullback_apply, hg (f.base x')]
    simp only [principalDivisorFamilyCoefficient]
    rw [finsum_mul]
    exact finsum_congr fun j ↦ (hβcoeff j x').symm

/-! ### Flat pullback on Chow groups -/

/-- **Stacks 0FVK.** Flat pullback on Chow groups, `f^* : A_k(X) ⟶ A_{k+r}(X')`, along a morphism
flat and locally of finite type of relative dimension `r`.

This is `Stacks.Chow.flatPullbackChow` with its hypothesis discharged by
`Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_general`. -/
def flatPullbackChowOfRelativeDimension (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C sX' (k + (r : ℤ)) :=
  flatPullbackChow C sX' sX f hbase r hf k
    (flatPullbackFactorsThroughRationalEquivalence_general C sX' sX f hbase r hf k)

/-- On the class of a cycle, flat pullback on Chow groups is the class of the flat pullback of
that cycle. -/
@[simp]
theorem flatPullbackChowOfRelativeDimension_mk (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (r : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (α : CycleGroup C sX k) :
    flatPullbackChowOfRelativeDimension C sX' sX f hbase r hf k
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sX' (k + (r : ℤ)))
        (flatPullback C sX' sX f hbase r hf k α) :=
  rfl

end Stacks.Chow

end
