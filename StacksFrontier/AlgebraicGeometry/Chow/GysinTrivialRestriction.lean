module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction

/-!
# The Gysin map on cycles when the invertible module is trivial on the zero scheme

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module, let `s ∈ Γ(X, L)` and let `i : D → X` be the
closed immersion of the zero scheme `D = Z(s)`, as in Stacks 02T8. The Gysin map of Stacks 02T8
takes values in the Chow group `A_k(D)` rather than in cycles, because on an integral closed
subscheme `W ⊆ D` its value is the first Chern class `c₁(L|_W) ∩ [W]`, which is only a class.

Stacks 0B6Z observes that if the restriction `L|_D` is trivial then there is a *canonical*
map on cycles
```
  i^* : Z_{k+1}(X) ⟶ Z_k(D),
```
obtained by keeping the rule of Stacks 02T8 for an integral closed subscheme `W ⊆ X` not
contained in `D` — the fundamental cycle of the scheme-theoretic intersection `W ∩ D` — and
*requiring* that `i^*[W] = 0` whenever `W ⊆ D`. That requirement is legitimate exactly because
`L|_W` is then trivial, so that `c₁(L|_W) ∩ [W]` vanishes in `A_k(W)`.

The map is determined uniquely, among all additive maps `Z_{k+1}(X) ⟶ Z_k(D)`, by the locally
finite component formula.

## Main definitions

* `Stacks.Chow.gysinCycleMapComponent` — the cycle attached to an integral closed subscheme of
  delta-dimension `k + 1`: zero if it is contained in the zero scheme, and the fundamental cycle
  of its scheme-theoretic intersection with the zero scheme otherwise.
* `Stacks.Chow.gysinCycleMapRule` — those two rules packaged as an
  `Stacks.Chow.IntegralComponentRule`.
* `Stacks.Chow.gysinCycleMap` — the canonical map `Z_{k+1}(X) ⟶ Z_k(D)` of Stacks 0B6Z.
* `Stacks.Chow.IsGysinCycleMap` — the locally finite component formula that characterizes it.
* `Stacks.Chow.cycleSupportIndex` — the points at which a cycle has a nonzero coefficient.

## Main results

* `Stacks.Chow.gysinCycleMap_of_le` — the defining requirement of Stacks 0B6Z: an integral
  closed subscheme contained in the zero scheme has zero image.
* `Stacks.Chow.gysinCycleMap_of_not_le` — on an integral closed subscheme not contained in the
  zero scheme the map is the one of Stacks 02T8, read on cycles.
* `Stacks.Chow.isGysinCycleMap_gysinCycleMap` — the map satisfies the locally finite component
  formula.
* `Stacks.Chow.eq_gysinCycleMap_of_isGysinCycleMap` — canonicity: nothing else does.
* `Stacks.Chow.cycle_eq_finsum_primeCycles` — every cycle is the locally finite sum of the
  prime cycles of the points of its support, weighted by its coefficients.

## References

* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02QR](https://stacks.math.columbia.edu/tag/02QR)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 02SK](https://stacks.math.columbia.edu/tag/02SK)
* [Stacks Project, Tag 02RZ](https://stacks.math.columbia.edu/tag/02RZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Presenting a cycle by the prime cycles of its support

A `k`-cycle is a function on the points of `X` with locally finite support, nonzero only at
points of relative dimension `k`. Reading each such point as the integral closed subscheme it is
the generic point of turns a cycle into the locally finite sum of the fundamental cycles of
those subschemes, weighted by the coefficients of the cycle. -/

section Presentation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The delta-dimension of the integral closed subscheme attached to a point of `X` is the
relative dimension of that point. -/
theorem schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq {k : ℤ} (x : X)
    (hx : relativeDimension C.dimensionFunction p x = k) :
    schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = (k : EInt) := by
  let _ : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  rw [schemeDeltaDimension_eq_genericPoint C ((integralComponentAt x).subschemeι ≫ p),
    relativeDimension_comp_closedImmersion]
  have hgen : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x := by
    simpa [genericPointOf] using genericPointOf_integralComponentAt x
  rw [show ((integralComponentAt x).subschemeι
    (genericPoint (integralComponentAt x).subscheme)) = x from hgen, hx]

/-- The fundamental cycle of the integral closed subscheme attached to a point of
delta-dimension `k` has coefficient one at that point. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_self {k : ℤ} (x : X)
    (hDim : schemeDeltaDimension C ((integralComponentAt x).subschemeι ≫ p) = (k : EInt)) :
    (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k).1 x = 1 := by
  have h := cycleAssociatedToClosedSubscheme_integral_apply C p (integralComponentAt x)
    (isIntegral_integralComponentAt x) hDim
  rwa [genericPointOf_integralComponentAt] at h

/-- The fundamental cycle of the integral closed subscheme attached to a point `x` vanishes at
every point other than `x`. -/
theorem cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne (k : ℤ) (x : X) {y : X}
    (hy : y ≠ x) :
    (cycleAssociatedToClosedSubscheme C p (integralComponentAt x).subschemeι k).1 y = 0 :=
  cycleAssociatedToClosedSubscheme_integral_apply_of_ne C p (integralComponentAt x)
    (isIntegral_integralComponentAt x) k (by rwa [genericPointOf_integralComponentAt])

variable {C p}

/-- The points of `X` at which a cycle has a nonzero coefficient, as an index type. -/
abbrev cycleSupportIndex {k : ℤ} (α : CycleGroup C p k) : Type u := {x : X // α.1 x ≠ 0}

/-- Every integral closed subscheme occurring in the canonical presentation of a `k`-cycle has
delta-dimension `k`. -/
theorem schemeDeltaDimension_cycleSupportIndex {k : ℤ} (α : CycleGroup C p k)
    (x : cycleSupportIndex α) :
    schemeDeltaDimension C ((integralComponentAt x.1).subschemeι ≫ p) = (k : EInt) :=
  schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq C p x.1
    ((mem_cyclesOfDimension_iff_forall_point C p k α.1).1 α.2 x.1 x.2)

/-- The integral closed subschemes occurring in the canonical presentation of a cycle form a
locally finite family. -/
theorem locallyFinite_support_integralComponentAt {k : ℤ} (α : CycleGroup C p k) :
    LocallyFinite fun x : cycleSupportIndex α ↦ ((integralComponentAt x.1).support : Set X) := by
  intro y
  obtain ⟨t, ht, hfin⟩ := α.1.locallyFiniteSupport y
  obtain ⟨U, hUt, hU, hyU⟩ := mem_nhds_iff.mp ht
  refine ⟨U, hU.mem_nhds hyU, ?_⟩
  have hmem : ∀ x : cycleSupportIndex α,
      (((integralComponentAt x.1).support : Set X) ∩ U).Nonempty → x.1 ∈ U := by
    intro x hx
    obtain ⟨z, hz, hzU⟩ := hx
    rw [coe_support_integralComponentAt] at hz
    obtain ⟨w, hwU, hw⟩ := mem_closure_iff.mp hz U hU hzU
    rw [Set.mem_singleton_iff] at hw
    exact hw ▸ hwU
  refine Set.Finite.of_finite_image (hfin.subset ?_)
    (Set.injOn_of_injective Subtype.val_injective)
  rintro z ⟨x, hx, rfl⟩
  exact ⟨hUt (hmem x hx), Function.mem_support.2 x.2⟩

/-- **The canonical presentation of a cycle.** A `k`-cycle is the locally finite sum, over the
points `x` carrying a nonzero coefficient, of the fundamental cycle of the integral closed
subscheme attached to `x` — the reduced induced structure on the closure of `x` — weighted by
that coefficient. -/
theorem cycle_eq_finsum_primeCycles {k : ℤ} (α : CycleGroup C p k) (y : X) :
    α.1 y = ∑ᶠ x : cycleSupportIndex α, α.1 x.1 *
      (cycleAssociatedToClosedSubscheme C p (integralComponentAt x.1).subschemeι k).1 y := by
  by_cases hy : α.1 y = 0
  · rw [hy, eq_comm]
    refine finsum_eq_zero_of_forall_eq_zero fun x ↦ ?_
    have hne : y ≠ x.1 := fun h ↦ x.2 (h ▸ hy)
    rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x.1 hne, mul_zero]
  · rw [finsum_eq_single _ (⟨y, hy⟩ : cycleSupportIndex α) fun x hx ↦ ?_]
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C p y
        (schemeDeltaDimension_cycleSupportIndex α ⟨y, hy⟩), mul_one]
    · have hne : y ≠ x.1 := fun h ↦ hx (Subtype.ext h.symm)
      rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k x.1 hne, mul_zero]

/-- **The canonical presentation of a cycle with finitely many components, as a finite sum in
`Z_k(X)`.** A `k`-cycle with finitely many components is the finite sum, over the points carrying
a nonzero coefficient, of the fundamental cycles of the integral closed subschemes attached to
them, weighted by those coefficients. -/
theorem cycle_eq_sum_zsmul_primeCycles {k : ℤ} (α : CycleGroup C p k)
    (hα : (Function.support α.1).Finite) :
    α = ∑ v ∈ hα.toFinset, α.1 v •
      cycleAssociatedToClosedSubscheme C p (integralComponentAt v).subschemeι k := by
  classical
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  have hterm : ∀ v ∈ hα.toFinset, α.1 v *
      (cycleAssociatedToClosedSubscheme C p (integralComponentAt v).subschemeι k).1 y =
      if y = v then α.1 v else 0 := by
    intro v hv
    rcases eq_or_ne y v with rfl | hne
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_self C p y
        (schemeDeltaDimension_cycleSupportIndex α ⟨y, hα.mem_toFinset.1 hv⟩), mul_one, if_pos rfl]
    · rw [cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p k v hne, mul_zero,
        if_neg hne]
  have hcoe : (∑ v ∈ hα.toFinset, α.1 v •
        cycleAssociatedToClosedSubscheme C p (integralComponentAt v).subschemeι k).1 y =
      ∑ v ∈ hα.toFinset, α.1 v *
        (cycleAssociatedToClosedSubscheme C p (integralComponentAt v).subschemeι k).1 y := by
    simp [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  rw [hcoe, Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  by_cases hy : y ∈ hα.toFinset
  · rw [if_pos hy]
  · rw [if_neg hy]
    exact Function.notMem_support.1 fun h ↦ hy (hα.mem_toFinset.2 h)

end Presentation

section CarrierSupport

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] {m : ℤ}

/-- Each summand of the canonical presentation of a cycle is supported on the integral closed
subscheme it is attached to. -/
theorem support_zsmul_primeCycle_subset (β : CycleGroup C p m) (i : cycleSupportIndex β) :
    Function.support (β.1 i.1 • cycleAssociatedToClosedSubscheme C p
        (integralComponentAt i.1).subschemeι m).1 ⊆
      ((integralComponentAt i.1).support : Set X) := by
  intro y hy
  have hy' : (β.1 i.1 • cycleAssociatedToClosedSubscheme C p
      (integralComponentAt i.1).subschemeι m).1 y ≠ 0 := hy
  have hne : y = i.1 := by
    by_contra hne
    have hzero : (cycleAssociatedToClosedSubscheme C p
        (integralComponentAt i.1).subschemeι m).1 y = 0 :=
      cycleAssociatedToClosedSubscheme_integralComponentAt_of_ne C p m i.1 hne
    exact hy' (by simp [hzero])
  rw [hne, coe_support_integralComponentAt]
  exact subset_closure (Set.mem_singleton _)

end CarrierSupport

/-! ### The canonical map on cycles -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- The cycle attached to an integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`: zero
if `W` is contained in the zero scheme `D = Z(s)`, and the fundamental cycle of the
scheme-theoretic intersection `W ∩ D` otherwise.

Ideal sheaves are ordered oppositely to their closed subschemes, so `D ≤ W` is the assertion
that `W` lies inside `D`, and the intersection is `W.comap D.subschemeι`. -/
def gysinCycleMapComponent (W : X.IdealSheafData) (_hW : IsIntegral W.subscheme)
    (_hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  open Classical in
  if Stacks.Divisors.zeroScheme X L s ≤ W then 0
  else
    cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k

/-- The component cycle `Stacks.Chow.gysinCycleMapComponent` vanishes on an integral closed
subscheme contained in the zero scheme. -/
theorem gysinCycleMapComponent_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapComponent C p k L s W hW hDim = 0 := by
  classical
  rw [gysinCycleMapComponent]
  exact ite_eq_left h

/-- On an integral closed subscheme not contained in the zero scheme the component cycle
`Stacks.Chow.gysinCycleMapComponent` is the fundamental cycle of the scheme-theoretic
intersection. -/
theorem gysinCycleMapComponent_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMapComponent C p k L s W hW hDim =
      cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k := by
  classical
  rw [gysinCycleMapComponent]
  exact ite_eq_right h

/-- The component cycle `Stacks.Chow.gysinCycleMapComponent` attached to `W` is supported over
`W`. -/
theorem support_gysinCycleMapComponent_subset (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    Function.support (gysinCycleMapComponent C p k L s W hW hDim).1 ⊆
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X) := by
  classical
  set D := Stacks.Divisors.zeroScheme X L s with hD
  by_cases h : D ≤ W
  · rw [gysinCycleMapComponent_of_le C p k L s W hW hDim h]
    simp
  · rw [gysinCycleMapComponent_of_not_le C p k L s W hW hDim h]
    refine (support_cycleAssociatedToClosedSubscheme_subset C (D.subschemeι ≫ p)
      ((W.comap D.subschemeι).subschemeι) k).trans ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact subset_rfl

/-- The component cycles `Stacks.Chow.gysinCycleMapComponent` as an
`Stacks.Chow.IntegralComponentRule`. -/
def gysinCycleMapRule : IntegralComponentRule C p
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι k where
  cycle := gysinCycleMapComponent C p k L s
  support_subset := support_gysinCycleMapComponent_subset C p k L s

/-- The canonical Gysin map on cycles `i^* : Z_{k+1}(X) ⟶ Z_k(D)` attached to a section `s` of an
invertible module whose restriction to the zero scheme `D = Z(s)` is trivial: the extension of
the two rules of `Stacks.Chow.gysinCycleMapComponent` over locally finite presentations by
integral closed subschemes. It does not depend on a trivialization of `L|_D`. -/
@[stacks 0B6Z "the canonical map on cycles"]
def gysinCycleMap
    (_htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L)) :
    CycleGroup C p (k + 1) →+
      CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  (gysinCycleMapRule C p k L s).extendCycleGroup

variable (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
    (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
    (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
    ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))

/-- An integral closed subscheme contained in the zero scheme has zero image under the canonical
map on cycles. -/
@[stacks 0B6Z "vanishing on integral closed subschemes contained in the zero scheme"]
theorem gysinCycleMap_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMap C p k L s htriv
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) = 0 := by
  rw [show gysinCycleMap C p k L s htriv = (gysinCycleMapRule C p k L s).extendCycleGroup from
      rfl,
    (gysinCycleMapRule C p k L s).extendCycleGroup_cycleAssociatedToClosedSubscheme W hW hDim]
  exact gysinCycleMapComponent_of_le C p k L s W hW hDim h

/-- The canonical map on cycles sends an integral closed subscheme `W` not contained in `D` to the
fundamental cycle of the scheme-theoretic intersection `W ∩ D`. -/
@[stacks 0B6Z "agreement with Stacks 02T8 off the zero scheme"]
theorem gysinCycleMap_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinCycleMap C p k L s htriv
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k := by
  rw [show gysinCycleMap C p k L s htriv = (gysinCycleMapRule C p k L s).extendCycleGroup from
      rfl,
    (gysinCycleMapRule C p k L s).extendCycleGroup_cycleAssociatedToClosedSubscheme W hW hDim]
  exact gysinCycleMapComponent_of_not_le C p k L s W hW hDim h

/-- The locally finite component formula: on a presentation `α = ∑ n_j [W_j]` of a `(k+1)`-cycle
by integral closed subschemes of delta-dimension `k + 1`, the coefficient of the image cycle at a
point of `D` is the corresponding sum of the coefficients of the component cycles. -/
def IsGysinCycleMap
    (F : CycleGroup C p (k + 1) →+
      CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k) : Prop :=
  ∀ {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (_hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (n : J → ℤ) (α : CycleGroup C p (k + 1)),
    (∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) →
    ∀ y : (Stacks.Divisors.zeroScheme X L s).subscheme,
      (F α).1 y = ∑ᶠ j : J, n j *
        (gysinCycleMapComponent C p k L s (W j) (hW j) (hDim j)).1 y

/-- The canonical map on cycles satisfies the locally finite component formula. -/
@[stacks 0B6Z "the locally finite component formula"]
theorem isGysinCycleMap_gysinCycleMap :
    IsGysinCycleMap C p k L s (gysinCycleMap C p k L s htriv) := by
  intro J W hW hDim hLocal n α hα y
  exact (gysinCycleMapRule C p k L s).extendCycleGroup_apply_of_presentation W hW hDim hLocal n
    α hα y

/-- Any additive map `Z_{k+1}(X) ⟶ Z_k(D)` satisfying the locally finite component formula is the
canonical map on cycles. -/
@[stacks 0B6Z "canonicity"]
theorem eq_gysinCycleMap_of_isGysinCycleMap
    (F : CycleGroup C p (k + 1) →+
      CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k)
    (hF : IsGysinCycleMap C p k L s F) :
    F = gysinCycleMap C p k L s htriv := by
  refine AddMonoidHom.ext fun α ↦ Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [hF (fun x : cycleSupportIndex α ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex α x)
      (locallyFinite_support_integralComponentAt α) (fun x ↦ α.1 x.1) α
      (cycle_eq_finsum_primeCycles α) y,
    isGysinCycleMap_gysinCycleMap C p k L s htriv
      (fun x : cycleSupportIndex α ↦ integralComponentAt x.1)
      (fun x ↦ isIntegral_integralComponentAt x.1)
      (fun x ↦ schemeDeltaDimension_cycleSupportIndex α x)
      (locallyFinite_support_integralComponentAt α) (fun x ↦ α.1 x.1) α
      (cycle_eq_finsum_primeCycles α) y]

end Stacks.Chow

end
