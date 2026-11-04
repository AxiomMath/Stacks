module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapCompatible

/-!
# The component case of Stacks 02SS, localized to a carrier on the ambient

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `f : X' ⟶ X` be flat
and locally of finite type of relative dimension `r` between schemes locally of finite type over
`S`, let `L` be an invertible `𝒪_X`-module and let `W ⊆ X` be an integral closed subscheme of
delta-dimension `k + 1`. Then

  `c₁(f^*L) ∩ f^*[W] - f^*(c₁(L) ∩ [W])`

is rationally equivalent to zero on `X'` **within `f^{-1}(W)`**.

## Why the carrier is the point

`Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible` already proves the
component case of Stacks 02SS for an invertible module, unconditionally. But it localizes in a
different currency: it produces a cycle on the *closed subscheme* `f^{-1}(W)` which is rationally
equivalent to zero there, and compares the two sides of Stacks 02SS through the pushforward of
that cycle along `f^{-1}(W) ⟶ X'`. A consumer which has to *add* this comparison to others on
`X'` — as the dévissage of Stacks 0F98 does, over the components of a cycle — cannot use it in
that shape: the closure properties of rational equivalence it needs, `Stacks.Chow.
isRationallyEquivalentToZeroWithin_add`, `_neg` and `Stacks.Chow.
IsRationallyEquivalentToZeroWithin.mono`, are all stated for
`Stacks.Chow.IsRationallyEquivalentToZeroWithin` on a fixed ambient.

This file performs that one translation and nothing else. The rational equivalence on `f^{-1}(W)`
is pushed into `X'` along the closed immersion `f^{-1}(W) ⟶ X'`, which by
`Stacks.Chow.properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion` confines
its witnesses to the image of that immersion, and the image is exactly `f^{-1}(W)` as a subset of
`X'` by `Stacks.Chow.coe_support_integralComponentPreimage`. So the carrier produced is
`f.base ⁻¹' W.support`, which is the shape the carriers of
`StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ContainedComponentComparison` already have — a
preimage of the support of `W` under the structure morphism of the ambient — and the pieces
therefore combine.

## Main results

* `firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin`
  — **the component case of Stacks 02SS for an invertible module, with a carrier on `X'`.**
* `firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_base`
  — the same with the structure morphism of `X'` an independent morphism `sX'` and the
  factorisation `f ≫ p = sX'` a hypothesis, which is the shape a consumer that reaches `X'` as a
  closed subscheme of something else has.

## Implementation notes

### The subscheme and its generic point

Stacks 02SS's component case is indexed by `W` in this file and by a point `x` of relative
dimension `k + 1` in `Stacks.Chow.FirstChernCapRationallyCompatibleWithFlatPullback`. The two are
the same datum: `Stacks.Chow.integralComponentAt_genericPointOf` and
`Stacks.Chow.relativeDimension_genericPointOf` take `W` to its generic point and back, and
`Stacks.Chow.firstChernComponentCycleAt_genericPointOf` identifies the two spellings of the cycle
`c₁(L) ∩ [W]`. No transport along an equality of subschemes enters the proof: the witness `a` is
left at `f^{-1}(closure {ξ})` and only the *carrier set* is rewritten, which is an equality of
subsets of `X'`.

### No `@[stacks 02SS]`

The tag is already carried, at the level of cycles and unconditionally, by
`Stacks.Chow.flatPullback_firstChernCapOfInvertible_rationallyEquivalent`. What is below is one
component of that statement in a different presentation, so no attribute joins it.

## References

* [Stacks Project, Tag 02SS](https://stacks.math.columbia.edu/tag/02SS)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0EPJ](https://stacks.math.columbia.edu/tag/0EPJ)
* [Stacks Project, Tag 0F98](https://stacks.math.columbia.edu/tag/0F98)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X' X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (r : ℕ)
  (hf : AlgebraicGeometry.RelativeDimension f r) (k : ℤ) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]

/-- **The component case of Stacks 02SS for an invertible module, with a carrier.** For `L` an
invertible `𝒪_X`-module, `f : X' ⟶ X` flat of relative dimension `r` and `W ⊆ X` an integral
closed subscheme of delta-dimension `k + 1`, the cycle `c₁(f^*L) ∩ f^*[W]` and the flat pullback
of the cycle `c₁(L) ∩ [W]` differ by a cycle rationally equivalent to zero on `X'`, witnessed
inside the preimage `f^{-1}(W)`.

The rational equivalence on `f^{-1}(W)` is the one
`Stacks.Chow.firstChernCapRationallyCompatibleWithFlatPullback_invertible` produces; pushing it
into `X'` along the closed immersion of `f^{-1}(W)` confines its witnesses to the image of that
immersion, which is `f^{-1}(W)`. -/
theorem firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C (f ≫ p) (k + (r : ℤ))
      ((firstChernCapRule C (f ≫ p) (k + (r : ℤ))
            (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
          ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
            flatPullback C (f ≫ p) p f rfl r hf (k + 1)
              (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) -
        flatPullback C (f ≫ p) p f rfl r hf k
          (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L) W hW hDim))
      (f.base ⁻¹' (W.support : Set X)) := by
  set ξ := genericPointOf W hW
  have hx : relativeDimension C.dimensionFunction p ξ = k + 1 :=
    relativeDimension_genericPointOf C p W hW hDim
  obtain ⟨a, ha, hval⟩ :=
    firstChernCapRationallyCompatibleWithFlatPullback_invertible C p f r hf k L ξ hx
  have hWeq : integralComponentAt ξ = W := integralComponentAt_genericPointOf W hW
  have hA := extendCycleGroup_flatPullback_cycleAssociatedToClosedSubscheme_apply C p f r hf k
    (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ)) ((Scheme.Modules.pullback f).obj L))
    (show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ξ hx
  rw [hWeq] at hA
  have hB : firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) ξ =
      firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L) W hW hDim :=
    firstChernComponentCycleAt_genericPointOf C p k (firstChernComponentCycleRule C p k L) W hW
      hDim
  have hcarrier : Set.range ((integralComponentAt ξ).comap f).subschemeι.base =
      f.base ⁻¹' (W.support : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentPreimage f ξ,
      support_eq_closure_genericPointOf W hW]
  have heq : (firstChernCapRule C (f ≫ p) (k + (r : ℤ))
          (firstChernComponentCycleRule C (f ≫ p) (k + (r : ℤ))
            ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
        ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
          flatPullback C (f ≫ p) p f rfl r hf (k + 1)
            (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) -
      flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L) W hW hDim) =
      properPushforward C (((integralComponentAt ξ).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
        ((integralComponentAt ξ).comap f).subschemeι rfl (k + (r : ℤ)) a := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro y'
    rw [← hval y', ← hB]
    exact congrArg (fun z : ℤ ↦ z -
      (flatPullback C (f ≫ p) p f rfl r hf k
        (firstChernComponentCycleAt C p k (firstChernComponentCycleRule C p k L) ξ)).1 y')
      (hA y')
  rw [heq, ← hcarrier]
  exact properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
    (((integralComponentAt ξ).comap f).subschemeι ≫ (f ≫ p)) (f ≫ p)
    ((integralComponentAt ξ).comap f).subschemeι rfl (k + (r : ℤ)) ha

/-- **The component case of Stacks 02SS with a carrier, with the structure morphism of the source
an independent morphism.** The factorisation `f ≫ p = sX'` is a hypothesis, which is how a
consumer reaching `X'` as a closed subscheme of a larger scheme holds it; both base morphisms
being locally of finite type is a `Prop`, so substituting the factorisation costs nothing. -/
theorem
    firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin_of_base
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (hbase : f ≫ p = sX')
    (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    IsRationallyEquivalentToZeroWithin C sX' (k + (r : ℤ))
      ((firstChernCapRule C sX' (k + (r : ℤ))
            (firstChernComponentCycleRule C sX' (k + (r : ℤ))
              ((Scheme.Modules.pullback f).obj L))).extendCycleGroup
          ((show k + 1 + (r : ℤ) = k + (r : ℤ) + 1 by omega) ▸
            flatPullback C sX' p f hbase r hf (k + 1)
              (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) -
        flatPullback C sX' p f hbase r hf k
          (firstChernComponentCycle C p k (firstChernComponentCycleRule C p k L) W hW hDim))
      (f.base ⁻¹' (W.support : Set X)) := by
  subst hbase
  exact firstChernCapRule_extendCycleGroup_sub_flatPullback_isRationallyEquivalentToZeroWithin C p
    f r hf k L W hW hDim

end Stacks.Chow

end
