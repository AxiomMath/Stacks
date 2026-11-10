module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.IsoComponentEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.InvertibleChernCapComponent
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullbackRationallyCompatible
public import StacksFrontier.AlgebraicGeometry.Chow.GysinGysinDescendedPresentation
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionIndependence
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme

/-!
# The divisor of a prescribed generator, with the generator prescribed only where it is needed

Let `M` be an invertible module on a scheme `Y` with a global section `t`, and let `m` be an
element of the stalk `M_ξ` which generates it whenever the integral component `Z_ξ` is contained
in the zero scheme `Z(t)`, and is the germ of `t` whenever it is not. The Gysin component cycle of
`Z_ξ` and the divisor cycle of `m` on `Z_ξ`, pushed forward to `Y`, differ by a cycle rationally
equivalent to zero with witnesses inside `Z_ξ ∩ Z(t)`. This file proves that comparison, its
descended and iterated forms, and the independence of the divisor cycle of such an `m` from the
ambient closed subscheme inside which it is formed.

## Main definitions

* `Stacks.Chow.componentGeneratorAt`: an arbitrary generator of `L_x` where the integral
  component `Z_x` is contained in the zero scheme `Z(s)`, and the germ of `s` where it is not.

## Main results

* `Stacks.Chow.isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub_of_le`:
  the component comparison on the ambient scheme.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback_of_le`:
  the same comparison inside the zero scheme.
* `Stacks.Chow.isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_le`: the
  iterated form, after the outer Gysin map has been applied.
* `isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_of_le`: the
  iterated form pushed forward to the ambient scheme.
* `isRationallyEquivalentToZeroWithin_properPushforward_gysinRuleInter_cycle_sub_of_le`: the
  outer component comparison on the ambient scheme.
* `Stacks.Chow.isStalkBasis_pullbackStalkAt_componentGeneratorAt`: the restriction of
  `componentGeneratorAt` to an integral closed subscheme generates.
* `isRationallyEquivalentToZeroWithin_properPushforward_chernCycleOfRestrictedStalk_ambient`: the
  divisor cycle of such an `m` does not depend on the ambient closed subscheme, up to a rational
  equivalence carried by the component and the zero scheme.

## References

* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Closure properties of rational equivalence within a carrier -/

/-- The negative of a cycle rationally equivalent to zero within a subset is rationally
equivalent to zero within it. -/
theorem isRationallyEquivalentToZeroWithin_of_eq_neg (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β : CycleGroup C p k} {T : Set X}
    (h : IsRationallyEquivalentToZeroWithin C p k α T) (hβ : ∀ x : X, β.1 x = -α.1 x) :
    IsRationallyEquivalentToZeroWithin C p k β T :=
  isRationallyEquivalentToZeroWithin_zsmul C p k h (-1) fun x ↦ by
    rw [hβ x, neg_one_mul]

/-- The difference of two cycles rationally equivalent to zero within a subset is rationally
equivalent to zero within it. -/
theorem isRationallyEquivalentToZeroWithin_sub (C : ChowSituation.{u}) {X : Scheme.{u}}
    (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ) {α β γ : CycleGroup C p k} {T : Set X}
    (hα : IsRationallyEquivalentToZeroWithin C p k α T)
    (hβ : IsRationallyEquivalentToZeroWithin C p k β T)
    (hγ : ∀ x : X, γ.1 x = α.1 x - β.1 x) :
    IsRationallyEquivalentToZeroWithin C p k γ T := by
  have hneg : IsRationallyEquivalentToZeroWithin C p k (-β) T :=
    isRationallyEquivalentToZeroWithin_of_eq_neg C p k hβ fun x ↦ rfl
  have hsum := isRationallyEquivalentToZeroWithin_add C p k hα hneg
  refine isRationallyEquivalentToZeroWithin_zsmul C p k hsum 1 fun x ↦ ?_
  rw [hγ x, one_mul]
  change _ = α.1 x + -β.1 x
  ring

/-! ### A generator prescribed by the zero scheme -/

section Generator

variable {X : Scheme.{u}} (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- An arbitrary generator of `L_x` where the integral component `Z_x` is contained in the zero
scheme `Z(s)`, and the germ of `s` at `x` where it is not. -/
def componentGeneratorAt (x : X) : L.presheaf.stalk x :=
  open Classical in
  haveI := isInvertible_presheaf L
  if _ : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x then
    (exists_isStalkBasis (isTrivializedNear_of_isInvertible L x)).choose
  else L.presheaf.germ ⊤ x trivial s

/-- On a component contained in the zero scheme the prescribed generator generates. -/
theorem isStalkBasis_componentGeneratorAt_of_le {x : X}
    (h : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) :
    IsStalkBasis L x (componentGeneratorAt L s x) := by
  classical
  have := isInvertible_presheaf L
  rw [componentGeneratorAt]
  split
  · exact (exists_isStalkBasis (isTrivializedNear_of_isInvertible L x)).choose_spec
  · exact absurd h ‹_›

/-- Off the zero scheme the prescribed generator is the germ of the section. -/
theorem componentGeneratorAt_of_not_le {x : X}
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt x) :
    componentGeneratorAt L s x = L.presheaf.germ ⊤ x trivial s := by
  classical
  have := isInvertible_presheaf L
  rw [componentGeneratorAt]
  split
  · exact absurd ‹_› h
  · rfl

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] in
/-- The restriction along `j : A ⟶ X` of the germ of a global section is the germ of the
restricted section. -/
theorem pullbackStalkAt_germ_top {A : Scheme.{u}} (j : A ⟶ X) (a : A) {y : X}
    (hy : j.base a = y) :
    Stacks.Divisors.pullbackStalkAt j L a hy (L.presheaf.germ ⊤ y trivial s) =
      ((Scheme.Modules.pullback j).obj L).presheaf.germ ⊤ a trivial
        (AlgebraicGeometry.pullbackGlobalSections j L s) := by
  rw [show AlgebraicGeometry.pullbackGlobalSections j L s =
      Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackUnitSections j L ⊤ s by
    rw [AlgebraicGeometry.pullbackGlobalSections_eq_unit]; rfl]
  exact Stacks.Divisors.pullbackStalkAt_germ j L a hy ⊤ trivial s

/-- The restriction of `componentGeneratorAt` to an integral closed subscheme generates the
stalk of the restricted module. -/
theorem isStalkBasis_pullbackStalkAt_componentGeneratorAt (W : X.IdealSheafData)
    [IsIntegral W.subscheme] [IsLocallyNoetherian W.subscheme] (w : W.subscheme) {y : X}
    (hy : W.subschemeι.base w = y) :
    IsStalkBasis ((Scheme.Modules.pullback W.subschemeι).obj L) w
      (Stacks.Divisors.pullbackStalkAt W.subschemeι L w hy (componentGeneratorAt L s y)) := by
  subst hy
  by_cases h : Stacks.Divisors.zeroScheme X L s ≤
      integralComponentAt (W.subschemeι.base w)
  · exact Stacks.Divisors.IsStalkBasis.pullbackStalkAt W.subschemeι L w rfl
      (isStalkBasis_componentGeneratorAt_of_le L s h)
  · have hmemW : W.subschemeι.base w ∈ (W.support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    have hW : ¬ Stacks.Divisors.zeroScheme X L s ≤ W := fun hle ↦
      h (hle.trans ((le_integralComponentAt_iff_mem_support W _).2 hmemW))
    have hne : (ConcreteCategory.hom
        (AlgebraicGeometry.pullbackGlobalSections W.subschemeι L)) s ≠ 0 :=
      pullbackGlobalSections_subschemeι_ne_zero L s W inferInstance hW
    rw [componentGeneratorAt_of_not_le L s h,
      pullbackStalkAt_germ_top L s W.subschemeι w rfl]
    refine isStalkBasis_germ_of_notMem_support_zeroScheme
      ((Scheme.Modules.pullback W.subschemeι).obj L) _ hne ?_
    rw [Stacks.Divisors.zeroScheme_pullback W.subschemeι L s,
      Scheme.IdealSheafData.support_comap]
    intro hmem
    exact h ((le_integralComponentAt_iff_mem_support _ _).2 (by simpa using hmem))

end Generator

/-! ### The component comparison -/

section Component

variable (C : ChowSituation.{u}) {Y : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q]
  (M : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]
  (t : Γ(M, ⊤)) (k : ℤ)

/-- Off the zero scheme, the divisor cycle of the germ of `t` on `Z_ξ` is the cycle of the closed
subscheme `Z(t) ∩ Z_ξ`. -/
private theorem chernCycleOfRestrictedStalk_germ_of_not_le (ξ : Y)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ q) =
      ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ) :
    chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
        (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ)
        (M.presheaf.germ ⊤ ξ trivial t) =
      cycleAssociatedToClosedSubscheme C ((integralComponentAt ξ).subschemeι ≫ q)
        ((Stacks.Divisors.zeroScheme Y M t).comap
          (integralComponentAt ξ).subschemeι).subschemeι k :=
  Subtype.ext ((val_chernCycleOfRestrictedStalk C q k M ξ hDim _).trans
    (weilDivisorAlgebraicCycle_restrictedWeilDivisorAt_germ_of_not_le C q M t ξ h k hDim))

include C q in
/-- Let `m ∈ M_ξ` generate the stalk if `Z_ξ ⊆ Z(t)`, and be the germ of `t` otherwise. Then
the Gysin component cycle of `Z_ξ` and the divisor cycle of `m` on `Z_ξ`, pushed forward to `Y`,
differ by a cycle rationally equivalent to zero with witnesses inside `Z_ξ ∩ Z(t)`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub_of_le (ξ : Y)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ q) =
      ((k + 1 : ℤ) : EInt)) {m : M.presheaf.stalk ξ}
    (hm : Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ → IsStalkBasis M ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ →
      m = M.presheaf.germ ⊤ ξ trivial t) :
    IsRationallyEquivalentToZeroWithin C q k
      (properPushforward C ((Stacks.Divisors.zeroScheme Y M t).subschemeι ≫ q) q
          (Stacks.Divisors.zeroScheme Y M t).subschemeι rfl k
          (gysinComponentCycle C q k M t (firstChernComponentClass C q k M)
            (integralComponentAt ξ) (isIntegral_integralComponentAt ξ) hDim) -
        properPushforward C ((integralComponentAt ξ).subschemeι ≫ q) q
          (integralComponentAt ξ).subschemeι rfl k
          (chernCycleOfRestrictedStalk C q k M (integralComponentAt ξ)
            (isIntegral_integralComponentAt ξ) hDim (genericPointOf_integralComponentAt ξ) m))
      (((integralComponentAt ξ).support : Set Y) ∩
        ((Stacks.Divisors.zeroScheme Y M t).support : Set Y)) := by
  by_cases h : Stacks.Divisors.zeroScheme Y M t ≤ integralComponentAt ξ
  · exact isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub C q M t k ξ
      hDim (hm h) fun hc ↦ absurd h hc
  · obtain rfl := hmt h
    rw [chernCycleOfRestrictedStalk_germ_of_not_le C q M t k ξ hDim h,
      properPushforward_gysinComponentCycle_eq_of_not_le C q M t k
      (integralComponentAt ξ) (isIntegral_integralComponentAt ξ) hDim h, sub_self]
    exact isRationallyEquivalentToZeroWithin_zero C q k _

end Component

/-! ### The comparison descended into the zero scheme -/

section GysinDescent

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- Let `m ∈ L_ξ` generate the stalk if `Z_ξ ⊆ Z(s)`, and be the germ of `s` otherwise. Inside
the zero scheme, the Gysin component cycle of `Z_ξ` is rationally equivalent to the inverse
image of the divisor cycle of `m`, with witnesses over `Z_ξ ∩ Z(s)`. -/
theorem isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback_of_le (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt)) {m : L.presheaf.stalk ξ}
    (hm : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      Stacks.Divisors.IsStalkBasis L ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s) :
    IsRationallyEquivalentToZeroWithin C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinComponentCycle C p k L s (firstChernComponentClass C p k L) (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim -
        cyclePullbackAlongClosedImmersion C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k
          (properPushforward C ((integralComponentAt ξ).subschemeι ≫ p) p
            (integralComponentAt ξ).subschemeι rfl k
            (chernCycleOfRestrictedStalk C p k L (integralComponentAt ξ)
              (isIntegral_integralComponentAt ξ) hDim
              (genericPointOf_integralComponentAt ξ) m)))
      ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
        (((integralComponentAt ξ).support : Set X) ∩
          ((Stacks.Divisors.zeroScheme X L s).support : Set X))) := by
  refine isRationallyEquivalentToZeroWithin_of_properPushforward C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _
    (by rw [Scheme.IdealSheafData.range_subschemeι]; exact Set.inter_subset_right) ?_
  rw [properPushforward_sub, properPushforward_cyclePullbackAlongClosedImmersion_eq C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k _
    (properPushforward_chernCycleOfRestrictedStalk_apply_eq_zero_of_notMem C p k L s ξ hDim hmt)]
  exact isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub_of_le C p L s
    k ξ hDim hm hmt

end GysinDescent

/-! ### The iterated comparison -/

section Comm

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L L' : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L']
  (s : Γ(L, ⊤)) (s' : Γ(L', ⊤))

/-- Let `m ∈ L_ξ` generate the stalk if `Z_ξ ⊆ Z(s)`, and be the germ of `s` otherwise. Inside
`D ∩ D'`, the iterated Gysin cycle of `Z_ξ` is rationally equivalent to the outer Gysin map
applied to the descended divisor cycle of `m`, with witnesses over `Z_ξ ∩ Z(s)`. -/
theorem isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_le (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    {m : L.presheaf.stalk ξ}
    (hm : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      Stacks.Divisors.IsStalkBasis L ξ m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      m = L.presheaf.germ ⊤ ξ trivial s) :
    IsRationallyEquivalentToZeroWithin C
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
      (gysinGysinComponentCycle C p k L L' s s' (integralComponentAt ξ)
          (isIntegral_integralComponentAt ξ) hDim -
        (gysinRuleInter C p k L L' s s').extendCycleGroup
          (descendedComponentDivisorCycle C p k L s ξ hDim m))
      ((zeroSchemeInter L L' s s').subschemeι.base ⁻¹'
        ((Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹'
          (((integralComponentAt ξ).support : Set X) ∩
            ((Stacks.Divisors.zeroScheme X L s).support : Set X)))) := by
  have h := isRationallyEquivalentToZeroWithin_gysinRule_extendCycleGroup C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k
    (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s')
    (isRationallyEquivalentToZeroWithin_gysinComponentCycle_sub_cyclePullback_of_le C p (k + 1) L
      s ξ hDim hm hmt)
  rwa [map_sub] at h

/-- The comparison `isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_le`,
pushed forward to `X`, with witnesses inside `Z_ξ ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinGysinComponentCycle_sub_of_le
    (ξ : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt ξ).subschemeι ≫ p) =
      ((k + 1 + 1 : ℤ) : EInt))
    {m : L.presheaf.stalk ξ}
    (hm : Stacks.Divisors.zeroScheme X L s ≤ integralComponentAt ξ →
      Stacks.Divisors.IsStalkBasis L ξ m)
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
  have hclosed : IsClosed ((((integralComponentAt ξ).support : Set X) ∩
      ((Stacks.Divisors.zeroScheme X L s).support : Set X))) :=
    (integralComponentAt ξ).support.isClosed.inter
      (Stacks.Divisors.zeroScheme X L s).support.isClosed
  have h := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι) (Category.assoc _ _ _) k
    (hclosed.preimage ((zeroSchemeInter L L' s s').subschemeι ≫
      (Stacks.Divisors.zeroScheme X L s).subschemeι).continuous)
    (isRationallyEquivalentToZeroWithin_gysinGysinComponentCycle_sub_of_le C p k L L' s s' ξ hDim
      hm hmt)
  rw [properPushforward_sub] at h
  exact h.mono (image_preimage_zeroSchemeInter_subset L L' s s' ξ)

/-- Let `z` be a point of `D = Z(s)` and `m'` an element of the stalk of `L'|_D` at `z` which
generates it if `Z_z ⊆ D ∩ D'`, and is the germ of the restriction of `s'` otherwise. Then the
outer Gysin cycle of `Z_z` and the divisor cycle of `m'` on `Z_z`, pushed forward to `X`, differ
by a cycle rationally equivalent to zero with witnesses inside `Z_z ∩ D ∩ D'`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_gysinRuleInter_cycle_sub_of_le
    (z : (Stacks.Divisors.zeroScheme X L s).subscheme)
    (hDim : schemeDeltaDimension C ((integralComponentAt z).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    {m' : (zeroSchemeRestrictModule L L' s).presheaf.stalk z}
    (hm' : zeroSchemeInter L L' s s' ≤ integralComponentAt z →
      Stacks.Divisors.IsStalkBasis (zeroSchemeRestrictModule L L' s) z m')
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
  have hclosed : IsClosed (((integralComponentAt z).support :
        Set (Stacks.Divisors.zeroScheme X L s).subscheme) ∩
      ((zeroSchemeInter L L' s s').support :
        Set (Stacks.Divisors.zeroScheme X L s).subscheme)) :=
    (integralComponentAt z).support.isClosed.inter (zeroSchemeInter L L' s s').support.isClosed
  have h := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion_of_within C
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
    (Stacks.Divisors.zeroScheme X L s).subschemeι rfl k hclosed
    (isRationallyEquivalentToZeroWithin_properPushforward_gysinComponentCycle_sub_of_le C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      (zeroSchemeRestrictModule L L' s) (restrictSectionToZeroScheme L L' s s') k z hDim hm'
      hmt')
  rw [properPushforward_sub, properPushforward_properPushforward C
      ((zeroSchemeInter L L' s s').subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (zeroSchemeInter L L' s s').subschemeι (Stacks.Divisors.zeroScheme X L s).subschemeι rfl
      rfl k,
    properPushforward_properPushforward C
      ((integralComponentAt z).subschemeι ≫
        (Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
      (integralComponentAt z).subschemeι (Stacks.Divisors.zeroScheme X L s).subschemeι rfl rfl
      k] at h
  exact h.mono (image_support_inter_zeroSchemeInter_subset L L' s s' z)

end Comm

/-! ### The divisor cycle of a prescribed generator does not depend on the ambient scheme -/

section Ambient

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (N : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (t : Γ(N, ⊤)) {A : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (j : A ⟶ X)
  [IsClosedImmersion j] (hj : j ≫ p = sA)

attribute [local instance] isIntegral_integralComponentAt

include hj in
/-- Let `j : A ⟶ X` be a closed immersion, let `a` be a point of `A` whose integral component
`Z_a` has delta-dimension `k + 1`, and let `m` be an element of `N` at the image point which
generates there whenever the component is contained in the zero scheme `Z(t)`, and is the germ of
`t` whenever it is not. The divisor `div_{N|_{Z_a}}(m|_{Z_a})` computed inside `A` and the
divisor `div_{N|_Z}(m|_Z)` computed inside `X` have, after being pushed forward to `X`, a
difference rationally equivalent to zero with witnesses inside `Z ∩ Z(t)`. -/
theorem isRationallyEquivalentToZeroWithin_properPushforward_chernCycleOfRestrictedStalk_ambient
    (a : A) {y : X} (hy : j.base a = y)
    (hDimA : schemeDeltaDimension C ((integralComponentAt a).subschemeι ≫ sA) =
      ((k + 1 : ℤ) : EInt))
    (hDimX : schemeDeltaDimension C ((integralComponentAt y).subschemeι ≫ p) =
      ((k + 1 : ℤ) : EInt))
    {m : N.presheaf.stalk y}
    (hm : Stacks.Divisors.zeroScheme X N t ≤ integralComponentAt y →
      IsStalkBasis N y m)
    (hmt : ¬ Stacks.Divisors.zeroScheme X N t ≤ integralComponentAt y →
      m = N.presheaf.germ ⊤ y trivial t) :
    IsRationallyEquivalentToZeroWithin C p k
      (properPushforward C ((integralComponentAt a).subschemeι ≫ sA) p
          ((integralComponentAt a).subschemeι ≫ j) (by rw [Category.assoc, hj]) k
          (chernCycleOfRestrictedStalk C sA k ((Scheme.Modules.pullback j).obj N)
            (integralComponentAt a) (isIntegral_integralComponentAt a) hDimA
            (genericPointOf_integralComponentAt a)
            (Stacks.Divisors.pullbackStalkAt j N a hy m)) -
        properPushforward C ((integralComponentAt y).subschemeι ≫ p) p
          (integralComponentAt y).subschemeι rfl k
          (chernCycleOfRestrictedStalk C p k N (integralComponentAt y)
            (isIntegral_integralComponentAt y) hDimX
            (genericPointOf_integralComponentAt y) m))
      (((integralComponentAt y).support : Set X) ∩
        ((Stacks.Divisors.zeroScheme X N t).support : Set X)) := by
  subst hy
  obtain ⟨ε, hε⟩ := exists_iso_integralComponentAt_comp j a
  have hcomp : ((integralComponentAt a).subschemeι ≫ j) ≫ p =
      (integralComponentAt a).subschemeι ≫ sA := by rw [Category.assoc, hj]
  have hrange : Set.range ((integralComponentAt a).subschemeι ≫ j).base =
      ((integralComponentAt (j.base a)).support : Set X) := by
    rw [← hε, ← Scheme.IdealSheafData.range_subschemeι]
    refine Set.ext fun y ↦ ⟨?_, ?_⟩
    · rintro ⟨w, rfl⟩
      exact ⟨ε.hom.base w, rfl⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨v, rfl⟩ := surjective_base_hom_of_iso ε w
      exact ⟨v, rfl⟩
  by_cases h : Stacks.Divisors.zeroScheme X N t ≤ integralComponentAt (j.base a)
  · have hsubT : ((integralComponentAt (j.base a)).support : Set X) ⊆
        ((Stacks.Divisors.zeroScheme X N t).support : Set X) := by
      rw [coe_support_integralComponentAt]
      exact ((Stacks.Divisors.zeroScheme X N t).support.isClosed.closure_subset_iff).mpr
        (Set.singleton_subset_iff.mpr ((le_integralComponentAt_iff_mem_support _ _).1 h))
    have : IsLocallyNoetherian (integralComponentAt (j.base a)).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian
        ((integralComponentAt (j.base a)).subschemeι ≫ p)
    have : IsLocallyNoetherian (integralComponentAt a).subscheme :=
      LocallyOfFiniteType.isLocallyNoetherian ((integralComponentAt a).subschemeι ≫ sA)
    have hεp : ε.hom ≫ ((integralComponentAt (j.base a)).subschemeι ≫ p) =
        (integralComponentAt a).subschemeι ≫ sA := by
      rw [← Category.assoc, hε, Category.assoc, hj]
    have hbasisA : IsStalkBasis ((Scheme.Modules.pullback j).obj N) a
        (Stacks.Divisors.pullbackStalkAt j N a rfl m) :=
      Stacks.Divisors.IsStalkBasis.pullbackStalkAt j N a rfl (hm h)
    have hσ : Stacks.Chow.restrictStalk (integralComponentAt a)
        ((Scheme.Modules.pullback j).obj N) (genericPointOf_integralComponentAt a)
        (Stacks.Divisors.pullbackStalkAt j N a rfl m) ≠ 0 :=
      restrictStalk_ne_zero _ (integralComponentAt a)
        (genericPointOf_integralComponentAt a) hbasisA
    have hmX : Stacks.Chow.restrictStalk (integralComponentAt (j.base a)) N
        (genericPointOf_integralComponentAt (j.base a)) m ≠ 0 :=
      restrictStalk_ne_zero N (integralComponentAt (j.base a))
        (genericPointOf_integralComponentAt (j.base a)) (hm h)
    have := isInvertible_presheaf_modulePullback N
      (integralComponentAt (j.base a)).subschemeι
    have := isInvertible_presheaf_modulePullback ((Scheme.Modules.pullback j).obj N)
      (integralComponentAt a).subschemeι
    have hre := rationallyEquivalentToZero_properPushforward_sub_chernComponentCycle C
      ((integralComponentAt a).subschemeι ≫ sA)
      ((integralComponentAt (j.base a)).subschemeι ≫ p) ε hεp k hDimA hDimX
      (Stacks.Chow.restrictModule (integralComponentAt (j.base a)) N)
      (Stacks.Chow.restrictModule (integralComponentAt a)
        ((Scheme.Modules.pullback j).obj N))
      (pullbackCompIso ε.hom (integralComponentAt (j.base a)).subschemeι
        (integralComponentAt a).subschemeι j hε N) hσ
      (chernCycleOfRestrictedStalk C p k N (integralComponentAt (j.base a))
        (isIntegral_integralComponentAt (j.base a)) hDimX
        (genericPointOf_integralComponentAt (j.base a)) m)
      (fun u hu ↦ mk_chernComponentCycle_eq C
        ((integralComponentAt (j.base a)).subschemeι ≫ p) hDimX _ hmX hu)
    have hpush := properPushforward_isRationallyEquivalentToZeroWithin_of_isClosedImmersion C
      ((integralComponentAt a).subschemeι ≫ sA) p
      ((integralComponentAt a).subschemeι ≫ j) hcomp k hre
    rw [properPushforward_sub, properPushforward_properPushforward C
        ((integralComponentAt (j.base a)).subschemeι ≫ p)
        ((integralComponentAt a).subschemeι ≫ sA) p ε.inv
        ((integralComponentAt a).subschemeι ≫ j)
        (by rw [← hεp, Iso.inv_hom_id_assoc]) hcomp k,
      congrFun (properPushforward_congr C
        ((integralComponentAt (j.base a)).subschemeι ≫ p) p
        (ε.inv ≫ (integralComponentAt a).subschemeι ≫ j)
        (integralComponentAt (j.base a)).subschemeι
        (by rw [← hε, Iso.inv_hom_id_assoc]) _ rfl k) _, hrange] at hpush
    have hpush2 : IsRationallyEquivalentToZeroWithin C p k
        (properPushforward C ((integralComponentAt (j.base a)).subschemeι ≫ p) p
            (integralComponentAt (j.base a)).subschemeι rfl k
            (chernCycleOfRestrictedStalk C p k N (integralComponentAt (j.base a))
              (isIntegral_integralComponentAt (j.base a)) hDimX
              (genericPointOf_integralComponentAt (j.base a)) m) -
          properPushforward C ((integralComponentAt a).subschemeι ≫ sA) p
            ((integralComponentAt a).subschemeι ≫ j) hcomp k
            (chernCycleOfRestrictedStalk C sA k ((Scheme.Modules.pullback j).obj N)
              (integralComponentAt a) (isIntegral_integralComponentAt a) hDimA
              (genericPointOf_integralComponentAt a)
              (Stacks.Divisors.pullbackStalkAt j N a rfl m)))
        ((integralComponentAt (j.base a)).support : Set X) := hpush
    refine (isRationallyEquivalentToZeroWithin_of_eq_neg C p k hpush2 fun x ↦ ?_).mono
      (Set.subset_inter subset_rfl hsubT)
    change (_ : ℤ) - _ = -(_ - _)
    ring
  · obtain rfl := hmt h
    have hzA : Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback j).obj N)
        (AlgebraicGeometry.pullbackGlobalSections j N t) =
          (Stacks.Divisors.zeroScheme X N t).comap j :=
      Stacks.Divisors.zeroScheme_pullback j N t
    have hA' : ¬ Stacks.Divisors.zeroScheme A ((Scheme.Modules.pullback j).obj N)
        (AlgebraicGeometry.pullbackGlobalSections j N t) ≤ integralComponentAt a := by
      rw [hzA, le_integralComponentAt_iff_mem_support,
        Scheme.IdealSheafData.support_comap]
      exact fun hmem ↦ h ((le_integralComponentAt_iff_mem_support _ _).2 hmem)
    have hcycA : chernCycleOfRestrictedStalk C sA k ((Scheme.Modules.pullback j).obj N)
          (integralComponentAt a) (isIntegral_integralComponentAt a) hDimA
          (genericPointOf_integralComponentAt a)
          (Stacks.Divisors.pullbackStalkAt j N a rfl
            (N.presheaf.germ ⊤ (j.base a) trivial t)) =
        cycleAssociatedToClosedSubscheme C ((integralComponentAt a).subschemeι ≫ sA)
          (((Stacks.Divisors.zeroScheme X N t).comap
            ((integralComponentAt a).subschemeι ≫ j)).subschemeι) k := by
      rw [pullbackStalkAt_germ_top N t j a rfl,
        chernCycleOfRestrictedStalk_germ_of_not_le C sA _ _ k a hDimA hA', hzA,
        Scheme.IdealSheafData.comap_comp]
    have hcycX := chernCycleOfRestrictedStalk_germ_of_not_le C p N t k (j.base a) hDimX h
    obtain ⟨e₁, he₁⟩ := Stacks.ChernCap42.exists_iso_comap_sup
      (integralComponentAt (j.base a)) (Stacks.Divisors.zeroScheme X N t)
      ((integralComponentAt a).subschemeι ≫ j) ε.symm hε
    obtain ⟨e₂, he₂⟩ := Stacks.ChernCap42.exists_iso_comap_sup
      (integralComponentAt (j.base a)) (Stacks.Divisors.zeroScheme X N t)
      (integralComponentAt (j.base a)).subschemeι (Iso.refl _) (by simp)
    rw [hcycA, hcycX,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
        ((integralComponentAt a).subschemeι ≫ sA) p
        ((integralComponentAt a).subschemeι ≫ j) hcomp _ k,
      properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
        ((integralComponentAt (j.base a)).subschemeι ≫ p) p
        (integralComponentAt (j.base a)).subschemeι rfl _ k,
      cycleAssociatedToClosedSubscheme_eq_of_iso C p
        (((Stacks.Divisors.zeroScheme X N t).comap
            ((integralComponentAt a).subschemeι ≫ j)).subschemeι ≫
          ((integralComponentAt a).subschemeι ≫ j))
        (integralComponentAt (j.base a) ⊔ Stacks.Divisors.zeroScheme X N t).subschemeι e₁ he₁ k,
      cycleAssociatedToClosedSubscheme_eq_of_iso C p
        (((Stacks.Divisors.zeroScheme X N t).comap
            (integralComponentAt (j.base a)).subschemeι).subschemeι ≫
          (integralComponentAt (j.base a)).subschemeι)
        (integralComponentAt (j.base a) ⊔ Stacks.Divisors.zeroScheme X N t).subschemeι e₂ he₂ k,
      sub_self]
    exact isRationallyEquivalentToZeroWithin_zero C p k _

end Ambient

end Stacks.Chow

end
