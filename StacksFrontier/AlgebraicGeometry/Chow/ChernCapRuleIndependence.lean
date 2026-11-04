module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionCarrier

/-!
# The cap product depends on its component rule only through the classes of the components

Let `X` be locally of finite type over the base scheme `S` of chapter 42 of the Stacks Project.
The cap product `Stacks.Chow.firstChernClassCap` is built from a component rule
`Stacks.Chow.FirstChernComponentCycleRule`, a `k`-cycle on every integral closed subscheme
`W ⊆ X` of delta-dimension `k + 1`. The rule is *cycle*-valued, so two rules whose values agree
only in the Chow group `A_k(W)` produce different cycles. Their cap products nevertheless agree
in `A_k(X)`: the difference of the two extended cycles is the locally finite sum, over the
integral components of the cycle being capped, of the differences over each component, and
those are rationally equivalent to zero by hypothesis, so Stacks 02RZ assembles them into a
single rational equivalence on `X`.

## Main results

* `Stacks.Chow.firstChernCapRule_extendCycleGroup_rationallyEquivalent` — the two extended
  cycles are rationally equivalent.
* `Stacks.Chow.firstChernClassCap_congr` — the two cap products are equal.

## References

* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)

/-- A locally finite sum over all of `X` is the sum over the support of a weight function, when
every term with vanishing weight vanishes. -/
public theorem finsum_subtype_support_eq {α : Type*} {M : Type*} [AddCommMonoid M]
    {β : Type*} [Zero β] (c : α → β) (f : α → M) (hf : ∀ a, c a = 0 → f a = 0) :
    ∑ᶠ i : ↥(Function.support c), f (i : α) = ∑ᶠ a : α, f a := by
  classical
  rw [finsum_set_coe_eq_finsum_mem,
    finsum_mem_inter_support_eq' f (Function.support c) Set.univ fun x hx ↦ ?_,
    finsum_mem_univ]
  exact ⟨fun _ ↦ trivial, fun _ ↦ fun hc ↦ hx (hf x hc)⟩

/-- The coefficient of the extension of a component rule, written as the locally finite sum over
the support of the cycle being capped of the pushforwards along `closure {x} ⟶ X` of the
component cycles. -/
theorem firstChernCapRule_extendCycleGroup_apply_support
    (chern : FirstChernComponentCycleRule C p k) (α : CycleGroup C p (k + 1))
    (hW : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      IsIntegral (integralComponentAt (i : X)).subscheme)
    (hDim : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      schemeDeltaDimension C ((integralComponentAt (i : X)).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt))
    (x : X) :
    ((firstChernCapRule C p k chern).extendCycleGroup α).1 x =
      ∑ᶠ i : ↥(Function.support (α.1 : X → ℤ)),
        (properPushforward C ((integralComponentAt (i : X)).subschemeι ≫ p) p
          (integralComponentAt (i : X)).subschemeι rfl k
          (α.1 (i : X) • chern _ (hW i) (hDim i))).1 x := by
  classical
  have hterm : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      (properPushforward C ((integralComponentAt (i : X)).subschemeι ≫ p) p
          (integralComponentAt (i : X)).subschemeι rfl k
          (α.1 (i : X) • chern _ (hW i) (hDim i))).1 x =
        α.1 (i : X) * (firstChernCapRule C p k chern).totalize
          (integralComponentAt (i : X)) x := by
    intro i
    rw [show properPushforward C ((integralComponentAt (i : X)).subschemeι ≫ p) p
          (integralComponentAt (i : X)).subschemeι rfl k
          (α.1 (i : X) • chern _ (hW i) (hDim i)) =
        α.1 (i : X) • properPushforward C ((integralComponentAt (i : X)).subschemeι ≫ p) p
          (integralComponentAt (i : X)).subschemeι rfl k (chern _ (hW i) (hDim i)) from
      map_zsmul (properPushforwardHom C ((integralComponentAt (i : X)).subschemeι ≫ p) p
        (integralComponentAt (i : X)).subschemeι rfl k) _ _,
      (firstChernCapRule C p k chern).totalize_eq _ (hW i) (hDim i)]
    rfl
  calc ((firstChernCapRule C p k chern).extendCycleGroup α).1 x
      = ∑ᶠ z : X, α.1 z * (firstChernCapRule C p k chern).totalize (integralComponentAt z) x :=
        rfl
    _ = _ := (finsum_subtype_support_eq (α.1 : X → ℤ) _ fun z hz ↦ by rw [hz, zero_mul]).symm
    _ = _ := finsum_congr fun i ↦ (hterm i).symm

/-- **The cap product cycle of a component rule is determined up to rational equivalence by the
classes of its components.** If two component rules take rationally equivalent values on every
integral closed subscheme of delta-dimension `k + 1`, then for every `(k+1)`-cycle the two
extended cycles are rationally equivalent. -/
theorem firstChernCapRule_extendCycleGroup_rationallyEquivalent
    (chern chern' : FirstChernComponentCycleRule C p k)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      RationallyEquivalent C (W.subschemeι ≫ p) k (chern W hW hDim) (chern' W hW hDim))
    (α : CycleGroup C p (k + 1)) :
    RationallyEquivalent C p k
      ((firstChernCapRule C p k chern).extendCycleGroup α)
      ((firstChernCapRule C p k chern').extendCycleGroup α) := by
  classical
  have hdim : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      relativeDimension C.dimensionFunction p (i : X) = k + 1 := fun i ↦
    (mem_cyclesOfDimension_iff_forall_point C p (k + 1) α.1).1 α.2 i i.2
  have hW : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      IsIntegral (integralComponentAt (i : X)).subscheme := fun i ↦
    isIntegral_integralComponentAt _
  have hDim : ∀ i : ↥(Function.support (α.1 : X → ℤ)),
      schemeDeltaDimension C ((integralComponentAt (i : X)).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt) := fun i ↦ by
    rw [schemeDeltaDimension_integralComponentAt C p (i : X), hdim i]
  refine rationallyEquivalent_finsum_of_closedSupports C p k
    (fun i : ↥(Function.support (α.1 : X → ℤ)) ↦ integralComponentAt (i : X)) ?_
    (fun i ↦ α.1 (i : X) • chern _ (hW i) (hDim i))
    (fun i ↦ α.1 (i : X) • chern' _ (hW i) (hDim i)) (fun i ↦ ?_)
    (firstChernCapRule_extendCycleGroup_apply_support C p k chern α hW hDim)
    (firstChernCapRule_extendCycleGroup_apply_support C p k chern' α hW hDim)
  · refine (locallyFinite_closure_support α.1.locallyFiniteSupport).subset fun i ↦ ?_
    rw [coe_support_integralComponentAt]
  · simpa only [smul_sub] using (rationalEquivalences C
      ((integralComponentAt (i : X)).subschemeι ≫ p) k).zsmul_mem
      (h _ (hW i) (hDim i)) (α.1 (i : X))

/-- **The cap product is determined by the classes of its component rule.** Two component rules
taking rationally equivalent values on every integral closed subscheme of delta-dimension
`k + 1` define the same cap product `Z_{k+1}(X) ⟶ A_k(X)`. -/
theorem firstChernClassCap_congr (chern chern' : FirstChernComponentCycleRule C p k)
    (h : ∀ (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
      (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)),
      RationallyEquivalent C (W.subschemeι ≫ p) k (chern W hW hDim) (chern' W hW hDim))
    (α : CycleGroup C p (k + 1)) :
    firstChernClassCap C p k chern α = firstChernClassCap C p k chern' α :=
  QuotientAddGroup.eq_iff_sub_mem.2
    (firstChernCapRule_extendCycleGroup_rationallyEquivalent C p k chern chern' h α)

end Stacks.Chow

end
