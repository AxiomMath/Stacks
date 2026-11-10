module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ComponentRules
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.ZeroScheme

/-!
# The Gysin homomorphism of the zero scheme of a section

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible module on `X` and let `s ∈ Γ(X, L)` be a global section with
zero scheme `D = Z(s)`. Stacks 02T8 constructs an additive *Gysin map*

  `Z_{k+1}(X) ⟶ A_k(D)`

by prescribing it on integral components. For an integral closed subscheme `W ⊆ X` of
delta-dimension `k + 1` there are two cases. If `W` is *not* contained in `D`, the value is the
fundamental cycle of the scheme-theoretic intersection `W ∩ D` — in the language of ideal
sheaves, of `W.comap D.subschemeι`, since ideal sheaves are ordered oppositely to their closed
subschemes and `D ≤ W` is the assertion that `W` lies inside `D`. If `W` *is* contained in `D`,
the value is the first Chern class of `L|_W` pushed into `D`. The two rules are then extended
coefficientwise over an arbitrary locally finite presentation of a `(k+1)`-cycle, which is
exactly what `Stacks.Chow.IntegralComponentRule.extendChow` does.

## Main definitions

* `Stacks.Chow.gysinComponentCycle` — the cycle representative attached to an integral
  component, by the two rules above.
* `Stacks.Chow.gysinRule` — those two rules packaged as an
  `Stacks.Chow.IntegralComponentRule`.
* `Stacks.Chow.IsGysinHomomorphism` — the locally finite component formula characterizing the
  Gysin map.
* `Stacks.Chow.gysinHomomorphismConstruction` — the additive Gysin map together with a proof
  that it satisfies that formula.
* `Stacks.Chow.gysinHomomorphism` — the Gysin map itself.

## Main results

* `Stacks.Chow.gysinHomomorphism_of_not_le` — the value on an integral component not contained
  in the zero scheme.
* `Stacks.Chow.gysinHomomorphism_finsum` — the locally finite component formula.

## Implementation notes

The contained-component rule of Stacks 02T8 is the first Chern class of the restricted
invertible module (Stacks 02SO). Every declaration below takes that class as an explicit
argument `chern` of type `Stacks.Chow.FirstChernComponentClassRule`.

## References

* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Supports of the two basic cycle constructions -/

/-- The fundamental cycle of a closed subscheme is supported on that closed subscheme. -/
theorem support_cycleAssociatedToClosedSubscheme_subset (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    (k : ℤ) :
    Function.support (cycleAssociatedToClosedSubscheme C f i k).1 ⊆ Set.range i.base :=
  Function.support_subset_iff'.2 fun x hx ↦
    cycleAssociatedToClosedSubscheme_apply_eq_zero C f i k x fun ⟨ξ, hξ, _⟩ ↦ hx ⟨ξ.1, hξ⟩

/-- A proper pushforward of cycles is supported on the image of the morphism. -/
theorem support_properPushforward_subset (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) (k : ℤ) (c : CycleGroup C sX k) :
    Function.support (properPushforward C sX sY f hf k c).1 ⊆ Set.range f.base :=
  Function.support_subset_iff'.2 fun y hy ↦ by
    rw [properPushforward_apply, Set.preimage_singleton_eq_empty.2 hy, finsum_mem_empty]

/-! ### The contained-component input -/

/-- A choice, for every integral closed subscheme `W ⊆ X` of delta-dimension `k + 1`, of a class
in the Chow group `A_k(W)`. -/
abbrev FirstChernComponentClassRule (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S)
    [LocallyOfFiniteType p] (k : ℤ) : Type u :=
  ∀ W : X.IdealSheafData, IsIntegral W.subscheme →
    schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt) →
    chowGroup C (W.subschemeι ≫ p) k

/-! ### The Gysin rule on integral components -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (chern : FirstChernComponentClassRule C p k)

/-- **Stacks 02T8 (1).** A cycle representative of the Gysin image of an integral component
`W` of delta-dimension `k + 1`: the fundamental cycle of the scheme-theoretic intersection
`W ∩ D` when `W` is not contained in the zero scheme `D`, and the pushforward to `D` of a cycle
representing the first Chern class of `L|_W` when it is. -/
def gysinComponentCycle (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  open Classical in
  if h : Stacks.Divisors.zeroScheme X L s ≤ W then
    properPushforward C (W.subschemeι ≫ p)
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      (Scheme.IdealSheafData.inclusion h) (by simp) k (Quotient.out (chern W hW hDim))
  else
    cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
      ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k

/-- **Stacks 02T8 (1).** For an integral component not contained in the zero scheme the Gysin
component cycle is the fundamental cycle of the scheme-theoretic intersection. -/
theorem gysinComponentCycle_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinComponentCycle C p k L s chern W hW hDim =
      cycleAssociatedToClosedSubscheme C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k := by
  classical
  rw [gysinComponentCycle, dite_eq_right h]

/-- **Stacks 02T8 (1).** For an integral component contained in the zero scheme the Gysin
component cycle is the pushforward of a representative of the first Chern class. -/
theorem gysinComponentCycle_of_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinComponentCycle C p k L s chern W hW hDim =
      properPushforward C (W.subschemeι ≫ p)
        ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
        (Scheme.IdealSheafData.inclusion h) (by simp) k (Quotient.out (chern W hW hDim)) := by
  classical
  rw [gysinComponentCycle, dite_eq_left h]

/-- The Gysin component cycle of `W` is supported over `W`. -/
theorem support_gysinComponentCycle_subset (W : X.IdealSheafData)
    (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt)) :
    Function.support (gysinComponentCycle C p k L s chern W hW hDim).1 ⊆
      (Stacks.Divisors.zeroScheme X L s).subschemeι.base ⁻¹' (W.support : Set X) := by
  classical
  set D := Stacks.Divisors.zeroScheme X L s with hD
  by_cases h : D ≤ W
  · rw [gysinComponentCycle_of_le C p k L s chern W hW hDim h]
    refine (support_properPushforward_subset C (W.subschemeι ≫ p) (D.subschemeι ≫ p)
      (Scheme.IdealSheafData.inclusion h) (by simp) k _).trans ?_
    rintro y ⟨w, rfl⟩
    rw [Set.mem_preimage, ← W.range_subschemeι]
    exact ⟨w, congrArg (fun f : W.subscheme ⟶ X ↦ f.base w)
      (Scheme.IdealSheafData.inclusion_subschemeι h).symm⟩
  · rw [gysinComponentCycle_of_not_le C p k L s chern W hW hDim h]
    refine (support_cycleAssociatedToClosedSubscheme_subset C (D.subschemeι ≫ p)
      ((W.comap D.subschemeι).subschemeι) k).trans ?_
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact fun _ h ↦ h

/-- The two integral-component rules of Stacks 02T8, as a `Stacks.Chow.IntegralComponentRule`.
-/
def gysinRule : IntegralComponentRule C p
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
    (Stacks.Divisors.zeroScheme X L s).subschemeι k where
  cycle := gysinComponentCycle C p k L s chern
  support_subset := support_gysinComponentCycle_subset C p k L s chern

/-! ### The Gysin homomorphism -/

/-- **Stacks 02T8 (2).** The two integral-component rules extended coefficientwise to every
locally finite presentation of a `(k+1)`-cycle. -/
def IsGysinHomomorphism
    (F : CycleGroup C p (k + 1) →+
      chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k) : Prop :=
  ∀ {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (_hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X)))
    (n : J → ℤ) (α : CycleGroup C p (k + 1)),
    (∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) →
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      F α = QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycle C p k L s chern (W j) (hW j) (hDim j)).1 x

/-- **Stacks 02T8.** Construction of the additive Gysin map of the zero scheme of `s`, together
with its locally finite component rule. -/
def gysinHomomorphismConstruction :
    { F : CycleGroup C p (k + 1) →+
        chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k //
      IsGysinHomomorphism C p k L s chern F } :=
  ⟨(gysinRule C p k L s chern).extendChow, fun W hW hDim hLocal n α hα ↦
    ⟨(gysinRule C p k L s chern).extendCycleGroup α, rfl,
      (gysinRule C p k L s chern).extendCycleGroup_apply_of_presentation W hW hDim hLocal n α hα⟩⟩

/-- **Stacks 02T8.** The Gysin homomorphism associated to the zero scheme of a section of an
invertible module. -/
def gysinHomomorphism : CycleGroup C p (k + 1) →+
    chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k :=
  (gysinHomomorphismConstruction C p k L s chern).val

/-- **Stacks 02T8.** The Gysin image of an integral closed subscheme not contained in the zero
scheme is the class of its scheme-theoretic intersection with that zero scheme. -/
theorem gysinHomomorphism_of_not_le (W : X.IdealSheafData) (hW : IsIntegral W.subscheme)
    (hDim : schemeDeltaDimension C (W.subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (h : ¬ Stacks.Divisors.zeroScheme X L s ≤ W) :
    gysinHomomorphism C p k L s chern
        (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1)) =
      QuotientAddGroup.mk
        (cycleAssociatedToClosedSubscheme C
          ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p)
          ((W.comap (Stacks.Divisors.zeroScheme X L s).subschemeι).subschemeι) k) := by
  change QuotientAddGroup.mk
    ((gysinRule C p k L s chern).extendCycleGroup
      (cycleAssociatedToClosedSubscheme C p W.subschemeι (k + 1))) = _
  rw [(gysinRule C p k L s chern).extendCycleGroup_cycleAssociatedToClosedSubscheme W hW hDim]
  exact congrArg QuotientAddGroup.mk
    (gysinComponentCycle_of_not_le C p k L s chern W hW hDim h)

/-- **Stacks 02T8.** The locally finite component rule for the Gysin map. -/
theorem gysinHomomorphism_finsum {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite (fun j ↦ ((W j).support : Set X))) (n : J → ℤ)
    (α : CycleGroup C p (k + 1))
    (hα : ∀ x : X, α.1 x = ∑ᶠ j : J, n j *
      (cycleAssociatedToClosedSubscheme C p (W j).subschemeι (k + 1)).1 x) :
    ∃ β : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) k,
      gysinHomomorphism C p k L s chern α = QuotientAddGroup.mk β ∧
      ∀ x : (Stacks.Divisors.zeroScheme X L s).subscheme,
        β.1 x = ∑ᶠ j : J, n j *
          (gysinComponentCycle C p k L s chern (W j) (hW j) (hDim j)).1 x :=
  (gysinHomomorphismConstruction C p k L s chern).2 W hW hDim hLocal n α hα

end Stacks.Chow

end
