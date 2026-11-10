module

public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.FibreDifference

/-!
# The degree of a principal divisor on a proper curve: the non-dominant branch

Let `C = (S, δ)` be a Chow situation whose dimension function vanishes identically, let `X` be
integral and locally of finite type over `S` of delta-dimension `n`, and let `f` be an
invertible rational function on `X`, represented by a unit section `g` on a dense open
`U ⊆ X`. The graph construction of Stacks 02RQ attaches to that datum the curve
`Y = graphClosure`, the closure of the graph of `g` inside `X ×_S ℙ¹_S`, and two projections
`p : Y ⟶ X` and `q : Y ⟶ ℙ¹_S`.

The proof of Stacks 02RU splits on whether `q` is dominant. This file settles the branch where
it is **not**, and settles it in the strong form `div(f) = 0` rather than only
`c_*div(f) = 0`:

* if `ℙ¹_S` has delta-dimension one, then every point of `ℙ¹_S` is either its generic point or
  closed (`Stacks.Chow.eq_genericPoint_or_isClosed`);
* a morphism out of an integral scheme into such a scheme which is not dominant misses the
  generic point of the target, so its image is a single closed point: it is constant
  (`Stacks.Chow.constant_of_not_isDominant`);
* a constant `q` carries the generic point of `Y` to the image of every point of `Y`, and the
  generic point of `Y` lies in neither `Y₀ = q⁻¹D₀` nor `Y_∞ = q⁻¹D_∞`, so both of those
  closed subschemes are **empty** (`Stacks.Chow.isEmpty_subscheme_comap_of_constant`);
* the cycle of an empty closed subscheme is zero
  (`Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty`), so by part (4) of
  Stacks 02RQ the principal divisor of the induced rational function on `Y` vanishes, and by
  part (5) so does the principal divisor of `f` on `X`.

## Main results

* `Stacks.Chow.eq_genericPoint_or_isClosed` — on an integral scheme of delta-dimension one over
  a base with vanishing dimension function, every point is the generic point or is closed.
* `Stacks.Chow.constant_of_not_isDominant` — a non-dominant morphism from an integral scheme to
  such a scheme is constant.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty` — the cycle of an empty
  closed subscheme is zero.
* `Stacks.Chow.isEmpty_subscheme_comap_of_constant` — the pullback of an ideal sheaf along a
  constant morphism from an integral scheme is empty as soon as the generic point avoids it.
* `Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant` — **the non-dominant branch of
  Stacks 02RU**: `div(f) = 0` when the graph projection to `ℙ¹_S` is not dominant.

## Implementation notes

### Why this is a branch and not the tag

`Stacks.Chow.principalDivisorCycle_eq_zero_of_not_isDominant` is one of the two cases of the
proof of Stacks 02RU, so it bears no Stacks attribute. It hypothesises non-dominance of `q`,
which is exactly the case distinction, together with the delta-dimension of `ℙ¹_S`. The
complementary case — `q` dominant, hence finite locally free, where the degree of the two
fibres is the rank of `q` — needs the push-pull formula of Stacks 02RH, which the repository
does not have.

The delta-dimension of `ℙ¹_S` is carried as the hypothesis `hPdim` because the repository does
not prove it; it is used only through `Stacks.Chow.eq_genericPoint_or_isClosed`, that is, only
to know that `ℙ¹_S` is a curve. `[IsIntegral (relativeProjectiveLine C.S)]` is an instance
binder rather than a hypothesis on `C.S` so that the statement applies verbatim once that
instance is available; for `C.S` integral it is
`Stacks.Chow.isIntegral_relativeProjectiveLine`.

### No part of this branch needs the projective line's arithmetic

Nothing here identifies the closed points of `ℙ¹_S`, its function field, or the orders of
vanishing on it. Only *irreducibility* of `ℙ¹_S` and the *value of its delta-dimension* are
used, together with parts (4) and (5) of Stacks 02RQ, which are proved in the library.

### The quasi-compactness hypothesis

`[QuasiCompact U.ι]` is inherited from part (2) of Stacks 02RQ and is not stated by Stacks
02RU; it holds automatically for `X` locally of finite type over a locally Noetherian base.

## References

* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02JW](https://stacks.math.columbia.edu/tag/02JW)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- On an integral scheme `X` of delta-dimension one, locally of finite type over a base whose
dimension function vanishes identically, every point is either the generic point of `X` or a
closed point.

The relative dimension function of `X` is a dimension function (Stacks 02JW); it is nonnegative
because the base dimension function is zero and a transcendence degree is, and it takes the
value one at the generic point. So it takes the value zero at every other point, and a point
where a dimension function vanishes and which is nonnegative everywhere has no proper
specialisation. -/
theorem eq_genericPoint_or_isClosed (C : ChowSituation.{u})
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X]
    (hdim : schemeDeltaDimension C sX = (1 : EInt)) (x : X) :
    x = genericPoint X ∨ IsClosed ({x} : Set X) := by
  obtain ⟨d, hd⟩ :=
    relativeDimension_isDimensionFunction C.isUniversallyCatenary C.dimensionFunction sX
  have hnonneg (y : X) : 0 ≤ d y := by
    rw [hd, relativeDimension, hδ]
    positivity
  have hη : d (genericPoint X) = 1 := by
    rw [hd]
    exact WithBotTop.coe_injective
      ((schemeDeltaDimension_eq_genericPoint C sX).symm.trans hdim)
  by_cases hx : x = genericPoint X
  · exact Or.inl hx
  right
  have hx0 : d x = 0 := by
    have hlt := d.strictAnti_specializes (genericPoint_specializes x) (Ne.symm hx)
    have := hnonneg x
    omega
  rw [← closure_eq_iff_isClosed]
  apply Set.Subset.antisymm _ subset_closure
  intro y hy
  change y = x
  by_contra hyx
  have hlt := d.strictAnti_specializes (specializes_iff_mem_closure.mpr hy) (Ne.symm hyx)
  have := hnonneg y
  omega

/-- A morphism from an integral scheme to an integral scheme of delta-dimension one over a base
with vanishing dimension function is constant as soon as it is not dominant.

If the image of the generic point were the generic point of the target, the closure of the range
would be everything. So it is a closed point, and the whole range, being contained in the
closure of that image, is that single point. -/
theorem constant_of_not_isDominant (C : ChowSituation.{u})
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (hdim : schemeDeltaDimension C sY = (1 : EInt))
    (f : X ⟶ Y) (hf : ¬ IsDominant f) (x : X) :
    f.base x = f.base (genericPoint X) := by
  have hne : f.base (genericPoint X) ≠ genericPoint Y := by
    intro he
    apply hf
    rw [isDominant_iff, denseRange_iff_closure_range]
    apply Set.Subset.antisymm (Set.subset_univ _)
    rw [← genericPoint_closure Y, ← he]
    exact closure_mono (Set.singleton_subset_iff.mpr (Set.mem_range_self _))
  have hclosed :=
    (eq_genericPoint_or_isClosed C hδ sY hdim (f.base (genericPoint X))).resolve_left hne
  exact ((genericPoint_specializes x).map f.continuous).mem_closed hclosed
    (Set.mem_singleton _)

/-- The cycle of an empty closed subscheme is zero: there is no generic point to carry a
coefficient. -/
theorem cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (i : Z ⟶ X) [IsClosedImmersion i] [IsEmpty Z] (n : ℤ) :
    cycleAssociatedToClosedSubscheme C sX i n = 0 := by
  apply Subtype.ext
  ext x
  apply cycleAssociatedToClosedSubscheme_apply_eq_zero
  rintro ⟨ξ, _⟩
  exact isEmptyElim ξ.1

/-- Let `q : X ⟶ Y` be constant, in the sense that it sends every point of the integral scheme
`X` to the image of the generic point, and let `D` be an ideal sheaf on `Y` whose pullback
misses the generic point of `X`. Then the pullback of `D` is the empty closed subscheme.

A point of the pullback lies in its support, so its image lies in the support of `D`; but that
image is the image of the generic point, so the generic point would lie in the support of the
pullback. -/
theorem isEmpty_subscheme_comap_of_constant {X Y : Scheme.{u}} [IsIntegral X] (q : X ⟶ Y)
    (hq : ∀ x : X, q.base x = q.base (genericPoint X)) (D : Y.IdealSheafData)
    (hη : genericPoint X ∉ ((D.comap q).support : Set X)) :
    IsEmpty (D.comap q).subscheme := by
  refine ⟨fun z ↦ ?_⟩
  have hz : (D.comap q).subschemeι.base z ∈ ((D.comap q).support : Set X) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self z
  apply hη
  rw [Scheme.IdealSheafData.support_comap] at hz ⊢
  change q.base (genericPoint X) ∈ ((D.support : Set Y))
  change q.base ((D.comap q).subschemeι.base z) ∈ ((D.support : Set Y)) at hz
  rwa [hq] at hz

/-- **The non-dominant branch of Stacks 02RU.** With the hypotheses of the graph construction of
Stacks 02RQ, if the projection `q : Y ⟶ ℙ¹_S` out of the graph closure is *not* dominant then
the principal divisor of `f` on `X` is zero.

`q` is then constant, so both distinguished fibres `Y₀ = q⁻¹D₀` and `Y_∞ = q⁻¹D_∞` are empty —
their supports would have to contain the generic point of `Y`, which lies in neither. Part (4)
of Stacks 02RQ writes the principal divisor on `Y` as the difference of their cycles, hence as
zero, and part (5) writes the principal divisor on `X` as its proper pushforward along `p`.

This is the easy case of the Stacks proof, and it is the case that really occurs: for `f` a
constant in `k^*` the graph is horizontal and `q` is constant. The complementary case needs the
push-pull formula of Stacks 02RH. -/
theorem principalDivisorCycle_eq_zero_of_not_isDominant (C : ChowSituation.{u})
    (hδ : ∀ p : C.S, C.dimensionFunction p = 0)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] [IsIntegral X]
    [IsIntegral (relativeProjectiveLine C.S)]
    (hPdim : schemeDeltaDimension C (relativeProjectiveLine C.S ↘ C.S) = (1 : EInt))
    (U : X.Opens) (g : (Γ(X, U))ˣ) [QuasiCompact U.ι] (n : ℤ)
    (hn : schemeDeltaDimension C sX = (n : EInt))
    (f : (rationalFunctions X)ˣ) (hU : Dense (U : Set X))
    (hf : ofSection X ⟨U, hU⟩ ↑g = (f : rationalFunctions X))
    (hd : GraphPreimageDense sX U ↑g)
    (hYint : IsIntegral (graphClosure sX U ↑g))
    (hYft : LocallyOfFiniteType (graphBaseMorphism sX U ↑g))
    (hp : IsProper (graphProjection sX U ↑g))
    (hYdim : schemeDeltaDimension C (graphBaseMorphism sX U ↑g) = (n : EInt))
    (hdom : ¬ IsDominant (graphLineProjection sX U ↑g)) :
    principalDivisorCycle C sX hn ((rationalFunctionsEquivFunctionField X).1 ↑f) = 0 := by
  have hUne : Nonempty U.toScheme := by
    obtain ⟨y, hy⟩ := hd.nonempty
    exact ⟨⟨graphProjection sX U ↑g y, hy⟩⟩
  have := hYint
  have := hYft
  have := hp
  have hconst := constant_of_not_isDominant C hδ (relativeProjectiveLine C.S ↘ C.S) hPdim
    (graphLineProjection sX U ↑g) hdom
  have h0 : IsEmpty (graphZeroFiber sX U ↑g).subscheme :=
    isEmpty_subscheme_comap_of_constant (graphLineProjection sX U ↑g) hconst
      (lineZeroDivisor C.S) (notMem_support_graphZeroFiber_genericPoint sX U g)
  have hinf : IsEmpty (graphInfinityFiber sX U ↑g).subscheme :=
    isEmpty_subscheme_comap_of_constant (graphLineProjection sX U ↑g) hconst
      (lineInfinityDivisor C.S) (notMem_support_graphInfinityFiber_genericPoint sX U g)
  rw [principalDivisorCycle_eq_properPushforward C sX U g n hn f hU hf hd hYint hYft hp hYdim,
    principalDivisorCycle_graphClosure_eq_sub C sX U g n hd hYint hYft hYdim,
    cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty C _ _ (n - 1),
    cycleAssociatedToClosedSubscheme_eq_zero_of_isEmpty C _ _ (n - 1),
    sub_zero, properPushforward_zero]

end Stacks.Chow

end
