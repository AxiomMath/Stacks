module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinPushforwardChernCap
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ChernCapDischarge

/-!
# The Gysin cycle of a component inside the zero scheme

Let `L` be an invertible `𝒪_X`-module, `s ∈ Γ(X, L)` a global section with zero scheme
`i : D = Z(s) ⟶ X` and `W ⊆ X` an integral closed subscheme of delta-dimension `k + 1` which is
*contained* in `D`, i.e. `D ≤ W` as ideal sheaves. The Gysin component rule of Stacks 02T8 then
takes the branch `Stacks.Chow.gysinComponentCycle_of_le`: its value is the pushforward to `D` of
the representative `Quotient.out` of the class `c₁(L|_W) ∩ [W]` chosen by the component rule.

That representative is arbitrary, while a consumer — the key formula Stacks 0AYC — supplies the
specific cycle `div_{L|_W}(m|_W)` of the restriction of a generator `m` of `L_ξ`, `ξ` the generic
point of `W`. The two agree only in `A_k(W)`, and this file bounds the discrepancy: it is the
pushforward along the closed immersion `W ⟶ D` of a cycle rationally equivalent to zero on `W`,
hence is rationally equivalent to zero on `D` *with witnesses inside `i^{-1}(W)`*
(`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion`). That
carrier is the one `Stacks.Chow.GysinKillsPrincipalDivisorOnComponent` asks for, so the
comparisons may be summed over a locally finite family of components.

## Main results

* `Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin` — the pushforward along
  a closed immersion of two rationally equivalent cycles differs by a cycle rationally equivalent
  to zero within the image of the immersion.
* `Stacks.Chow.gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le`
  — **the contained-component comparison**, for an arbitrary representative of the value of the
  component rule at `W`.
* `Stacks.Chow.gysinComponentCycle_sub_restrictedStalkCycle_isRationallyEquivalentToZeroWithin` —
  the same with the representative `div_{L|_W}(m|_W)` of the restriction of a stalk generator,
  which is `Stacks.Chow.chernCycleOfRestrictedStalk` and is the cycle the key formula supplies.
* `Stacks.Chow.firstChernComponentCycleRule_tensorObj_sub_isRationallyEquivalentToZeroWithin` and
  its `_of_le` specialization — the additivity of Stacks 02SP in the same localized shape.

## The localized form of the additivity

The dévissage of Stacks 0F98 compares the Gysin cycle of a component `W ⊆ D` against the
component rules of two invertible modules and of their tensor product, and must then sum those
comparisons over the locally finite family of components of a cycle. Every term of that sum has
therefore to be presented as an `IsRationallyEquivalentToZeroWithin` on the ambient `D` with its
witnesses confined to `i^{-1}(W)`, which is the carrier the contained-component comparison above
already produces.

Stacks 02SP is in the library as the Chow-class identity
`Stacks.Chow.firstChernClassCapOfInvertible_tensorObj` and, one component at a time, as the
cycle-level rational equivalence *on `W`*
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_tensorObj`. Neither has that
shape: a class identity has no cycle to carry and a rational equivalence on `W` has its witnesses
on `W` rather than on `D`. Pushing the second through
`Stacks.Chow.properPushforward_sub_isRationallyEquivalentToZeroWithin` supplies the missing shape,
and that is all this section does — no new mathematics, so no `@[stacks 02SP]` attribute joins the
two the tag already carries.

*The spelling of the tensor product.* The 0F97 branch construction writes the tensor product as
`Stacks.Divisors.tensorModules` and Stacks 02SP is stated at
`AlgebraicGeometry.Scheme.Modules.tensorObj`. Both are `abbrev`s for
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf X.sheaf.obj
X.ringCatSheaf.property`, i.e. for one and the same term, so the two spellings are
interchangeable with no comparison isomorphism and no transport: a consumer holding the 0F97
spelling may apply the lemmas below directly.

## References

* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Pushing a rational equivalence forward along a closed immersion -/

/-- **Two rationally equivalent cycles have rationally equivalent pushforwards, with a carrier.**
Along a closed immersion `j` the difference of the pushforwards is the pushforward of the
difference, which is rationally equivalent to zero within the image of `j`. -/
theorem properPushforward_sub_isRationallyEquivalentToZeroWithin (C : ChowSituation.{u})
    {Z Y : Scheme.{u}} (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (j : Z ⟶ Y) [IsClosedImmersion j] (hj : j ≫ sY = sZ) (k : ℤ)
    {a b : CycleGroup C sZ k} (hab : RationallyEquivalent C sZ k a b) :
    IsRationallyEquivalentToZeroWithin C sY k
      (properPushforward C sZ sY j hj k a - properPushforward C sZ sY j hj k b)
      (Set.range j.base) := by
  rw [← properPushforward_sub]
  exact properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C sZ sY j hj k
    hab

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- Rationally equivalent cycles on a component `W ⊆ D = Z(s)` have pushforwards to `D` differing
by a cycle rationally equivalent to zero, witnessed inside the preimage of `W`. -/
private theorem sub_properPushforward_inclusion_isRationallyEquivalentToZeroWithin
    {W : X.IdealSheafData} (h : Stacks.Divisors.zeroScheme X L s ≤ W)
    {a b : CycleGroup C (W.subschemeι ≫ p) k} (hab : RationallyEquivalent C _ k a b) :
    IsRationallyEquivalentToZeroWithin C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (properPushforward C (W.subschemeι ≫ p) _ (Scheme.IdealSheafData.inclusion h) (by simp) k a -
        properPushforward C (W.subschemeι ≫ p) _ (Scheme.IdealSheafData.inclusion h) (by simp) k b)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X)) := by
  refine (properPushforward_sub_isRationallyEquivalentToZeroWithin C _ _ _ (by simp) k
    hab).mono ?_
  rintro y ⟨w, rfl⟩
  have hbase : (Stacks.Divisors.zeroScheme X L s).subschemeι.base
      ((Scheme.IdealSheafData.inclusion h).base w) = W.subschemeι.base w :=
    congrArg (fun f : W.subscheme ⟶ X ↦ f.base w) (Scheme.IdealSheafData.inclusion_subschemeι h)
  rw [Set.mem_preimage, hbase, ← W.range_subschemeι]
  exact ⟨w, rfl⟩

/-! ### The contained-component comparison -/

/-- **The contained-component comparison of Stacks 02T8.** For an integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1` contained in the zero scheme `D = Z(s)` and any cycle `c` on
`W` representing the value of the component rule at `W`, the Gysin component cycle of `W` differs
from the pushforward of `c` to `D` by a cycle rationally equivalent to zero on `D`, witnessed
inside the preimage of `W`.

The Gysin component cycle is the pushforward of the representative `Quotient.out`, which is
rationally equivalent to `c` because the two have the same class. -/
theorem gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le
    (chern : FirstChernComponentClassRule C p k) (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) (c : CycleGroup C (W.subschemeι ≫ p) k)
    (hc : chern W hW hDim = QuotientAddGroup.mk c) :
    IsRationallyEquivalentToZeroWithin C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinComponentCycle C p k L s chern W hW hDim -
        properPushforward C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (Scheme.IdealSheafData.inclusion h) (by simp) k c)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X)) := by
  rw [gysinComponentCycle_of_le C p k L s chern W hW hDim h]
  exact sub_properPushforward_inclusion_isRationallyEquivalentToZeroWithin C p k L s h
    (QuotientAddGroup.eq_iff_sub_mem.mp ((Quotient.out_eq _).trans hc))

/-- **The contained-component comparison against the divisor of a restricted generator.** For a
point `ξ` whose integral component `Z_ξ` has delta-dimension `k + 1` and is contained in the zero
scheme `D = Z(s)`, and a generator `m` of `L_ξ`, the Gysin component cycle of `Z_ξ` differs from
the pushforward to `D` of `div_{L|Z_ξ}(m|_{Z_ξ})` by a cycle rationally equivalent to zero on `D`,
witnessed inside the preimage of `Z_ξ`.

The restriction `m|_{Z_ξ}` is a nonzero meromorphic section of `L|_{Z_ξ}`, so its divisor cycle
`Stacks.Chow.chernCycleOfRestrictedStalk` represents `c₁(L|_{Z_ξ}) ∩ [Z_ξ]` by Stacks 02SJ (2). -/
theorem gysinComponentCycle_sub_restrictedStalkCycle_isRationallyEquivalentToZeroWithin
    (ξ : X) (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) (h : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ)
    {m : L.presheaf.stalk ξ} (hm : IsStalkBasis L ξ m) :
    IsRationallyEquivalentToZeroWithin C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinComponentCycle C p k L s (firstChernComponentClass C p k L) (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim -
        properPushforward C ((integralComponentAt ξ).subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (Scheme.IdealSheafData.inclusion h) (by simp) k
          (chernCycleOfRestrictedStalk C p k L (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
        ((integralComponentAt ξ).support : Set X)) := by
  have _ := isIntegral_integralComponentAt ξ
  have _ := isLocallyNoetherian_integralComponentAt C p ξ
  refine gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le C p k
    L s (firstChernComponentClass C p k L) (integralComponentAt ξ)
    (isIntegral_integralComponentAt ξ) hDim h _ ?_
  exact firstChernComponentClass_eq_mk_of_ne_zero C p k L (integralComponentAt ξ) hDim
    (restrictStalk_ne_zero L (integralComponentAt ξ) (genericPointOf_integralComponentAt ξ) hm)

/-! ### The additivity of Stacks 02SP in the localized shape -/

/-- **The additivity of Stacks 02SP, pushed forward with a carrier.** Let `W ⊆ X` be an integral
closed subscheme of delta-dimension `k + 1`, let `j : W ⟶ Y` be a closed immersion over the base
and let `M`, `N` be invertible `𝒪_X`-modules. The pushforward to `Y` of the component cycle rule
of `M ⊗_{𝒪_X} N` at `W` differs from the pushforward of the sum of the rules of `M` and of `N` by
a cycle rationally equivalent to zero on `Y`, witnessed inside the image of `j`.

The two cycles on `W` are rationally equivalent by Stacks 02SP on a single integral component,
`Stacks.Chow.rationallyEquivalent_firstChernComponentCycleRule_tensorObj`, and pushing a rational
equivalence forward along a closed immersion confines its witnesses to the image. -/
theorem firstChernComponentCycleRule_tensorObj_sub_isRationallyEquivalentToZeroWithin
    (M N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (j : W.subscheme ⟶ Y) [IsClosedImmersion j] (hj : j ≫ sY = W.subschemeι ≫ p) :
    IsRationallyEquivalentToZeroWithin C sY k
      (properPushforward C (W.subschemeι ≫ p) sY j hj k
          (firstChernComponentCycleRule C p k (Scheme.Modules.tensorObj M N) W hW hDim) -
        properPushforward C (W.subschemeι ≫ p) sY j hj k
          (firstChernComponentCycleRule C p k M W hW hDim +
            firstChernComponentCycleRule C p k N W hW hDim))
      (Set.range j.base) :=
  properPushforward_sub_isRationallyEquivalentToZeroWithin C (W.subschemeι ≫ p) sY j hj k
    (rationallyEquivalent_firstChernComponentCycleRule_tensorObj C p k M N W hW hDim)

/-- **The additivity of Stacks 02SP for a component contained in the zero scheme.** For an
integral closed subscheme `W ⊆ X` of delta-dimension `k + 1` contained in the zero scheme
`D = Z(s)`, the pushforward to `D` of the component rule of `M ⊗_{𝒪_X} N` at `W` differs from the
pushforward of the sum of the rules of `M` and of `N` by a cycle rationally equivalent to zero on
`D`, witnessed inside the preimage of `W`.

This is the carrier the contained-component comparison
`Stacks.Chow.gysinComponentCycle_sub_properPushforward_isRationallyEquivalentToZeroWithin_of_le`
produces, so the two may be added with
`Stacks.Chow.isRationallyEquivalentToZeroWithin_add`. -/
theorem firstChernComponentCycleRule_tensorObj_sub_isRationallyEquivalentToZeroWithin_of_le
    (M N : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property M]
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    IsRationallyEquivalentToZeroWithin C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (properPushforward C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (Scheme.IdealSheafData.inclusion h) (by simp) k
          (firstChernComponentCycleRule C p k (Scheme.Modules.tensorObj M N) W hW hDim) -
        properPushforward C (W.subschemeι ≫ p)
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          (Scheme.IdealSheafData.inclusion h) (by simp) k
          (firstChernComponentCycleRule C p k M W hW hDim +
            firstChernComponentCycleRule C p k N W hW hDim))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X)) :=
  sub_properPushforward_inclusion_isRationallyEquivalentToZeroWithin C p k L s h
    (rationallyEquivalent_firstChernComponentCycleRule_tensorObj C p k M N W hW hDim)

end Stacks.Chow

end
