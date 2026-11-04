module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.ClosedImmersionPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinCommute

/-!
# The descended divisor of the inner Gysin map, presented on the intersection

The outer Gysin cycle of the descended divisor of the inner Gysin map, written as an explicit
locally finite combination and compared on the ambient scheme.

Let `W = Z_ξ ⊆ X` be integral of delta-dimension `k + 2`, let `m` be a generator of `L_ξ` which
is the germ of `s` whenever `W` is not contained in `D = Z(s)`, and let

  `γ = (W → X)_* div_{L|W}(m|_W)`

be its divisor cycle pushed forward to `X`. Then

* `γ` vanishes off `D`, so its canonical presentation by integral components (Stacks 02RW) has
  every member's generic point in `D`, and that presentation descends to `D`;
* the outer Gysin map, being a rule on the integral components of `D`, is therefore the
  corresponding combination of its values on the components of `D` above the members of the
  presentation.

Moreover the iterated Gysin cycle of `W` and the outer Gysin cycle of the descended divisor,
pushed forward to `X`, differ by a cycle rationally equivalent to zero within `W ∩ D ∩ D'`.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub`
  — the iterated Gysin cycle of `W` and the outer Gysin cycle of the descended divisor, pushed
  forward to `X`, differ by a cycle rationally equivalent to zero within `W ∩ D ∩ D'`.
* `Stacks.Chow.extendCycleGroup_descendedComponentDivisorCycle_apply` — the outer Gysin cycle of
  the descended divisor, as a locally finite combination of the outer Gysin cycles of the
  components of `D` above the members of the divisor's presentation.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinRuleInter_cycle_sub` —
  the outer Gysin cycle of a single integral component of `D`, compared on `X` with the divisor
  cycle of a prescribed generator of `L'|_D` there, carried over the component and `D ∩ D'`.

## References

* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤))

/-- **The divisor cycle of a prescribed generator on an integral component, pushed forward to the
ambient scheme.** -/
abbrev componentDivisorPushforward (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (m : L.presheaf.stalk ξ) : CycleGroup C p (k + 1) :=
  properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
    (integralComponentAt ξ).subschemeι rfl (k + 1)
    (chernCycleOfRestrictedStalk C p (k + 1) L (integralComponentAt ξ)
      (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m)

/-- The descended divisor cycle is the inverse image on `Z(s)` of the divisor cycle pushed
forward to `X`. -/
theorem descendedComponentDivisorCycle_eq_cyclePullback (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) (m : L.presheaf.stalk ξ) :
    descendedComponentDivisorCycle C p k L s ξ hDim m =
      cyclePullbackAlongClosedImmersion C
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
        (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
        (componentDivisorPushforward C p k L ξ hDim m) :=
  rfl

/-! ### The iterated Gysin cycle and the descended divisor, on the ambient scheme -/

/-- The image of the inverse image of `W ∩ D` under the closed immersion of the intersection
`D ∩ D'` into `X` lies inside `W ∩ D ∩ D'`. -/
theorem image_preimage_zeroSchemeInter_subset (ξ : X) :
    ((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι).base ''
        (((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι).base ⁻¹'
          (((integralComponentAt ξ).support : Set X) ∩
            ((Stacks.Divisors.zeroScheme X L s).support : Set X))) ⊆
      ((integralComponentAt ξ).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) := by
  intro x hx
  rw [Set.image_preimage_eq_inter_range, range_zeroSchemeInter_subschemeι_comp] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2.1⟩

/-- A difference of cycles rationally equivalent to zero within a closed set stays so, after
pushing both forward along a closed immersion, within any set containing the image. -/
private theorem isRationallyEquivalentToZeroWithin_properPushforward_sub_of_image_subset
    {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S)
    [LocallyOfFiniteType sB] (f : A ⟶ B) [IsClosedImmersion f] (hf : f ≫ sB = sA)
    {α β : CycleGroup C sA k} {T : Set A} {T' : Set B} (hT : IsClosed T)
    (h : IsRationallyEquivalentToZeroWithin C sA k (α - β) T) (hsub : f.base '' T ⊆ T') :
    IsRationallyEquivalentToZeroWithin C sB k
      (properPushforward C sA sB f hf k α - properPushforward C sA sB f hf k β) T' := by
  rw [← properPushforward_sub]
  exact (properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    sA sB f hf k hT h).mono hsub

/-- The iterated Gysin cycle of an integral component `W = Z_ξ` and the outer Gysin cycle of the
descended divisor of a prescribed generator have, after pushing both forward to `X`, a difference
rationally equivalent to zero with witnesses inside `W ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    {m : L.presheaf.stalk ξ} (hm : Stacks.Divisors.IsStalkBasis L ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (gysinGysinComponentCycle C p k L L' s s' (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim) -
        properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          ((gysinRuleInter C p k L L' s s').extendCycleGroup
            (descendedComponentDivisorCycle C p k L s ξ hDim m)))
      (((integralComponentAt ξ).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  refine isRationallyEquivalentToZeroWithin_properPushforward_sub_of_image_subset C k _ _
    ((zeroSchemeInter L L' s s').subschemeι ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι)
    (Category.assoc _ _ _) (((integralComponentAt ξ).support.isClosed.inter
      (Stacks.Divisors.zeroScheme X L s).support.isClosed).preimage
        (((zeroSchemeInter L L' s s').subschemeι ≫
          (Stacks.Divisors.zeroScheme X L s).subschemeι).continuous))
    (isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub C p k L L' s s' ξ hDim hm
      hmt)
    (image_preimage_zeroSchemeInter_subset L L' s s' ξ)

/-! ### The outer Gysin cycle of the descended divisor, presented -/

/-- **The members of the presentation of the divisor cycle lie in `D`.** A point at which the
pushed-forward divisor cycle of the prescribed generator does not vanish is a point of the zero
scheme. -/
theorem mem_range_subschemeι_cycleSupportIndex_componentDivisorPushforward (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt)) {m : L.presheaf.stalk ξ}
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s)
    (x : cycleSupportIndex (componentDivisorPushforward C p k L ξ hDim m)) :
    genericPointOf (integralComponentAt x.1) (isIntegral_integralComponentAt x.1) ∈
      Set.range (Stacks.Divisors.zeroScheme X L s).subschemeι.base := by
  rw [genericPointOf_integralComponentAt]
  by_contra hr
  exact x.2 (properPushforward_chernCycleOfRestrictedStalk_apply_eq_zero_of_notMem C p (k + 1) L s
    ξ hDim hmt x.1 hr)

/-- **The outer Gysin cycle of the descended divisor, presented by the components of `D` above
the members of the divisor's presentation.** At a point `z` of `D ∩ D'`, the outer Gysin cycle
of the descended divisor is the locally finite sum, over the points `x` of the support of the
divisor cycle on `X`, of the multiplicity of `x` times the outer Gysin cycle of the integral
component of `D` above the closure of `x`. -/
theorem extendCycleGroup_descendedComponentDivisorCycle_apply (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    {m : L.presheaf.stalk ξ}
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s)
    (z : (zeroSchemeInter L L' s s').subscheme) :
    ((gysinRuleInter C p k L L' s s').extendCycleGroup
        (descendedComponentDivisorCycle C p k L s ξ hDim m)).1 z =
      ∑ᶠ x : cycleSupportIndex (componentDivisorPushforward C p k L ξ hDim m),
        (componentDivisorPushforward C p k L ξ hDim m).1 x.1 *
          ((gysinRuleInter C p k L L' s s').cycle
            (integralComponentAbove (Stacks.Divisors.zeroScheme X L s).subschemeι
              (integralComponentAt x.1) (isIntegral_integralComponentAt x.1)
              (mem_range_subschemeι_cycleSupportIndex_componentDivisorPushforward C p k L s ξ hDim
                hmt x))
            (isIntegral_integralComponentAbove _ _ _ _)
            (schemeDeltaDimension_integralComponentAbove C p
              ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
              (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (integralComponentAt x.1)
              (isIntegral_integralComponentAt x.1) _
              (schemeDeltaDimension_cycleSupportIndex
                (componentDivisorPushforward C p k L ξ hDim m) x))).1 z :=
  extendCycleGroup_cyclePullbackAlongClosedImmersion_apply_of_presentation C p
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (gysinRuleInter C p k L L' s s')
    (fun x : cycleSupportIndex (componentDivisorPushforward C p k L ξ hDim m) ↦
      integralComponentAt x.1)
    (fun x ↦ isIntegral_integralComponentAt x.1)
    (fun x ↦ schemeDeltaDimension_cycleSupportIndex
      (componentDivisorPushforward C p k L ξ hDim m) x)
    (mem_range_subschemeι_cycleSupportIndex_componentDivisorPushforward C p k L s ξ hDim hmt)
    (locallyFinite_support_integralComponentAt (componentDivisorPushforward C p k L ξ hDim m))
    (fun x ↦ (componentDivisorPushforward C p k L ξ hDim m).1 x.1) _
    (cycle_eq_finsum_primeCycles (componentDivisorPushforward C p k L ξ hDim m)) z

/-! ### The outer Gysin cycle of a single component of `D`, compared on the ambient scheme -/

/-- The intersection of the integral component of `D` at `z` with the zero scheme of `s'|_D`
maps into the intersection of the integral component of `X` at the image of `z` with
`D ∩ D'`. -/
theorem image_support_inter_zeroSchemeInter_subset
    (z : (Stacks.Divisors.zeroScheme X L s).subscheme) :
    (Stacks.Divisors.zeroScheme X L s).subschemeι.base ''
        (((integralComponentAt z).support :
            Set (Stacks.Divisors.zeroScheme X L s).subscheme) ∩
          ((zeroSchemeInter L L' s s').support :
            Set (Stacks.Divisors.zeroScheme X L s).subscheme)) ⊆
      ((integralComponentAt
            ((Stacks.Divisors.zeroScheme X L s).subschemeι.base z)).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X)) := by
  rintro x ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
  rw [coe_support_integralComponentAt] at hw₁
  refine ⟨?_, ?_, ?_⟩
  · rw [coe_support_integralComponentAt]
    refine (IsClosed.closure_subset_iff (isClosed_closure.preimage
      (Stacks.Divisors.zeroScheme X L s).subschemeι.continuous)).mpr ?_ hw₁
    exact Set.singleton_subset_iff.mpr (subset_closure rfl)
  · rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨w, rfl⟩
  · rwa [zeroSchemeInter_eq_comap L L' s s', Scheme.IdealSheafData.support_comap] at hw₂

/-- **The outer component comparison, read on the ambient scheme.** For a point `z` of `D` whose
integral component there has delta-dimension `k + 1`, and a generator `m'` of the stalk of
`L'|_D` at `z` which is the germ of `s'|_D` whenever that component is not contained in the
inverse image of `D'`, the outer Gysin cycle of the component and the divisor cycle of the
restricted generator agree on `X` up to a rational equivalence carried over the intersection of
the component's image with `D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinRuleInter_cycle_sub
    (z : (Stacks.Divisors.zeroScheme X L s).subscheme)
    (hDim : schemeDeltaDimension C ((integralComponentAt z).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {m' : (zeroSchemeRestrictModule L L' s).presheaf.stalk z}
    (hm' : Stacks.Divisors.IsStalkBasis (zeroSchemeRestrictModule L L' s) z m')
    (hmt' : ¬ zeroSchemeInter L L' s s' ≤ integralComponentAt z →
      m' = (zeroSchemeRestrictModule L L' s).presheaf.germ ⊤ z trivial
        (restrictSectionToZeroScheme L L' s s')) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((zeroSchemeInter L L' s s').subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          ((gysinRuleInter C p k L L' s s').cycle (integralComponentAt z)
            (isIntegral_integralComponentAt z) hDim) -
        properPushforward C ((integralComponentAt z).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          ((integralComponentAt z).subschemeι ≫
            (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
          (chernCycleOfRestrictedStalk C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
            (zeroSchemeRestrictModule L L' s) (integralComponentAt z)
            (isIntegral_integralComponentAt z) hDim (genericPointOf_integralComponentAt z) m'))
      (((integralComponentAt
            ((Stacks.Divisors.zeroScheme X L s).subschemeι.base z)).support : Set X) ∩
        (((Stacks.Divisors.zeroScheme X L s).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L' s').support : Set X))) := by
  have h := isRationallyEquivalentToZeroWithin_properPushforward_sub_of_image_subset C k _ _
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl
    ((integralComponentAt z).support.isClosed.inter (zeroSchemeInter L L' s s').support.isClosed)
    (isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s') k z hDim hm' hmt')
    (image_support_inter_zeroSchemeInter_subset L L' s s' z)
  rwa [properPushforward_properPushforward, properPushforward_properPushforward] at h

end Stacks.Chow

end
