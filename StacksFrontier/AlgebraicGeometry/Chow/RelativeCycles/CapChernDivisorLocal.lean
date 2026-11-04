module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapChernDivisorUnit
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GysinAction

/-!
# Pushed-forward principal divisors across an open immersion

Let `j : U ⟶ X` be an open immersion of schemes locally of finite type over the base of a Chow
situation, `Wx ⊆ X` an integral closed subscheme and `I = Wx ∩ U`, also integral. The
pushforward to `U` of the principal divisor of the restriction to `I` of a rational function on
`Wx` has, at every point of `U`, the coefficient at the image point of the pushforward to `X` of
the principal divisor of that function. This is the comparison that carries the action of a
relative cycle on a principal divisor from an open subscheme of the base back to the base.

## Main results

* `Stacks.Chow.properPushforward_principalDivisorCycle_apply_of_isOpenImmersion` — the comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Principal divisors across an open immersion -/

/-- **A pushed-forward principal divisor read on an open subscheme.** Let `j : U ⟶ X` be an open
immersion, `Wx ⊆ X` an integral closed subscheme and `I = Wx ∩ U`, integral. If the rational
function `fI` on `I` is the restriction of `fW` on `Wx`, then the pushforward to `U` of `div(fI)`
has at `y` the coefficient of the pushforward to `X` of `div(fW)` at `j y`. -/
theorem properPushforward_principalDivisorCycle_apply_of_isOpenImmersion (C : ChowSituation.{u})
    {U X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sU : U ⟶ C.S)
    [LocallyOfFiniteType sU] (j : U ⟶ X) [IsOpenImmersion j] (hU : j ≫ sX = sU)
    (Wx : X.IdealSheafData) [IsIntegral Wx.subscheme] (I : U.IdealSheafData)
    [IsIntegral I.subscheme] (hI : I = Wx.comap j) {n m : ℤ}
    (hnW : schemeDeltaDimension C (Wx.subschemeι ≫ sX) = (n : EInt))
    (hnI : schemeDeltaDimension C (I.subschemeι ≫ sU) = (m : EInt))
    (fW : Wx.subscheme.functionField) (fI : I.subscheme.functionField)
    (hf : ∀ (μ : I.subscheme ⟶ Wx.subscheme) [IsOpenImmersion μ] [IsDominant μ],
      μ ≫ Wx.subschemeι = I.subschemeι ≫ j → dominantFunctionFieldMap μ fW = fI)
    (y : U) :
    (properPushforward C (I.subschemeι ≫ sU) sU I.subschemeι rfl (m - 1)
        (principalDivisorCycle C (I.subschemeι ≫ sU) hnI fI)).1 y =
      (properPushforward C (Wx.subschemeι ≫ sX) sX Wx.subschemeι rfl (n - 1)
        (principalDivisorCycle C (Wx.subschemeι ≫ sX) hnW fW)).1 (j.base y) := by
  subst hU
  subst hI
  have : IsLocallyNoetherian Wx.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (Wx.subschemeι ≫ sX)
  have : IsLocallyNoetherian (Wx.comap j).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian ((Wx.comap j).subschemeι ≫ j ≫ sX)
  have : IsDominant (comapOpenImmersionMap j Wx) :=
    isDominant_comapOpenImmersionMap j Wx inferInstance inferInstance
  have hμ := comapOpenImmersionMap_comp_subschemeι j Wx
  by_cases hy : y ∈ Set.range (Wx.comap j).subschemeι.base
  · obtain ⟨z, rfl⟩ := hy
    have hpt : j.base ((Wx.comap j).subschemeι.base z) =
        Wx.subschemeι.base ((comapOpenImmersionMap j Wx).base z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hμ]
    rw [hpt, properPushforward_apply_image_of_isClosedImmersion,
      properPushforward_apply_image_of_isClosedImmersion, principalDivisorCycle_apply,
      principalDivisorCycle_apply, ← hf _ hμ]
    exact ord_dominantFunctionFieldMap_of_isOpenImmersion _ fW z
  · rw [properPushforward_apply_eq_zero_of_notMem_range C _ _ _ rfl _ _ y hy,
      properPushforward_apply_eq_zero_of_notMem_range C _ _ _ rfl _ _ _ ?_]
    refine fun hmem ↦ hy ?_
    rw [Scheme.IdealSheafData.range_subschemeι] at hmem
    rwa [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]

end Stacks.Chow

end
