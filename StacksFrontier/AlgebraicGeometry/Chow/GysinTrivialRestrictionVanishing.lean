module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinSystemOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VeryWeakBivariantCriterion
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCapInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.SelfIntersectionFormula
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.GysinComponentDischarge

/-!
# The Gysin map kills classes supported on the zero scheme when the normal bundle is trivial

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project, let `L` be an invertible `𝒪_X`-module, let `s ∈ Γ(X, L)` and let `i : D = Z(s) ⟶ X` be
the closed immersion of its zero scheme. Remark 0B6Z of the source observes that when the
restriction `L|_D` is trivial, the Gysin map `i^*` can be computed on cycles by declaring
`i^*[W] = 0` for every integral closed subscheme `W ⊆ D`. Read on Chow groups this says that
`i^*` kills every class pushed forward from `D`:

  `i^* i_* γ = 0`  in  `A_k(D)`,  for `γ ∈ A_{k+1}(D)`.

This is how Remark 0B6Z is used in the proof of Stacks 0F9J, where `D` is the fibre at infinity
of a modification of `𝐏¹_X` and the triviality of `L|_D` is that of the normal bundle of the
divisor at infinity.

The proof is the self-intersection formula `i^* i_* γ = c₁(L|_D) ∩ γ`
(`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι`) followed by the
vanishing of the first Chern class of the structure sheaf (Stacks 02SP,
`Stacks.Chow.firstChernClassCapOfInvertible_unit`), transported along the trivialization of
`L|_D` (`Stacks.Chow.firstChernClassCapOfInvertible_congr`).

## Main results

* `Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero` — the
  vanishing on cycles pushed forward from the zero scheme.
* `Stacks.Chow.gysinChowOfInvertible_chowPushforwardOfIsClosedImmersion_eq_zero` — the vanishing
  on Chow groups, for any closed immersion identified with the zero scheme.
* `Stacks.Chow.gysinSystemOfInvertible_onChowEqGysinCycleMap` — **Remark 0B6Z on Chow groups**:
  when `L|_D` is trivial, the Gysin map of Stacks 02TO is the class of the canonical Gysin map on
  cycles of Remark 0B6Z.

## References

* [Stacks Project, Tag 0B6Z](https://stacks.math.columbia.edu/tag/0B6Z)
* [Stacks Project, Tag 0F95](https://stacks.math.columbia.edu/tag/0F95)
* [Stacks Project, Tag 02SP](https://stacks.math.columbia.edu/tag/02SP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (k : ℤ)
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))

/-- **Remark 0B6Z, on cycles pushed forward from the zero scheme.** If the restriction of `L` to
the zero scheme `D = Z(s)` is trivial, the Gysin map of `s` kills the pushforward of every cycle
on `D`: by the self-intersection formula the value is `c₁(L|_D) ∩ γ`, and the first Chern class
of a trivial module is zero. -/
theorem gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    (γ : CycleGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) (k + 1)) :
    gysinHomomorphismOfInvertible C p k L s
        (properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1) γ) = 0 := by
  let e : (Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L ≅
      SheafOfModules.unit (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf :=
    htriv.some
  rw [gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι,
    firstChernClassCapOfInvertible_congr C _ k _ _ e, firstChernClassCapOfInvertible_unit]

/-- **Remark 0B6Z, on Chow groups.** Let `i : Y ⟶ X` be a closed immersion identified, by an
isomorphism `e` over `X`, with the zero scheme `D = Z(s)`. If the restriction of `L` to `D` is
trivial, the descended Gysin map of `s` (Stacks 02TO) kills every class pushed forward along `i`:

  `i^* i_* γ = 0`  in  `A_k(D)`,  for `γ ∈ A_{k+1}(Y)`. -/
theorem gysinChowOfInvertible_chowPushforwardOfIsClosedImmersion_eq_zero
    (htriv : AlgebraicGeometry.SheafOfModules.IsTrivial
      (Stacks.Divisors.zeroScheme X L s).subscheme.sheaf.obj
      (Stacks.Divisors.zeroScheme X L s).subscheme.ringCatSheaf.property
      ((Scheme.Modules.pullback (Stacks.Divisors.zeroScheme X L s).subschemeι).obj L))
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = sY) (e : Y ≅ (Stacks.Divisors.zeroScheme X L s).subscheme)
    (he : e.hom ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι = i)
    (γ : chowGroup C sY (k + 1)) :
    gysinChowOfInvertible C p k L s (chowPushforwardOfIsClosedImmersion C sY p i hi (k + 1) γ) =
      0 := by
  induction γ using QuotientAddGroup.induction_on with
  | H c =>
    have hb : e.hom ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) = sY := by
      rw [← Category.assoc, he, hi]
    have hpush : properPushforward C sY p i hi (k + 1) c =
        properPushforward C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) p
          (Stacks.Divisors.zeroScheme X L s).subschemeι rfl (k + 1)
          (properPushforward C sY ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) e.hom hb
            (k + 1) c) := by
      rw [properPushforward_properPushforward]
      exact congrFun (properPushforward_congr C sY p i
        (e.hom ≫ (Stacks.Divisors.zeroScheme X L s).subschemeι) he.symm hi _ (k + 1)) c
    change gysinChowOfInvertible C p k L s
      (QuotientAddGroup.mk' _ (properPushforward C sY p i hi (k + 1) c)) = 0
    rw [hpush, gysinChowOfInvertible_mk]
    exact gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero C p k L s htriv _

/-! ### The Gysin map on Chow groups is the canonical map on cycles -/

omit [LocallyOfFiniteType p] in
/-- The pushforward along a closed immersion of the inverse image of a cycle has, at a point of
the image, the coefficient of the cycle. -/
theorem properPushforward_cycleComap_apply_of_isClosedImmersion [LocallyOfFiniteType p]
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = sY) {m : ℤ} (c : CycleGroup C p m) (y : Y) :
    (properPushforward C sY p i hi m
        ⟨cycleComap i i.isClosedEmbedding.injective c.1,
          cycleComap_mem_cyclesOfDimension_of_isClosedImmersion C p sY i hi m c.2⟩).1
        (i.base y) = c.1 (i.base y) := by
  have hfibre : i.base ⁻¹' {i.base y} = {y} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hw ↦ i.isClosedEmbedding.injective hw, fun hw ↦ hw ▸ rfl⟩
  have hdim : relativeDimension C.dimensionFunction sY y =
      relativeDimension C.dimensionFunction p (i.base y) := by
    subst hi
    exact relativeDimension_comp_closedImmersion C.dimensionFunction i p y
  rw [properPushforward_apply, hfibre, finsum_mem_singleton, cycleComap_apply, hdim,
    residueDegree_eq_one_of_isClosedImmersion]
  simp

/-- An integral closed subscheme through a point of a closed subscheme `D` lies inside `D`. -/
theorem le_integralComponentAt_of_mem {D : X.IdealSheafData} {x : X}
    (hx : x ∈ Set.range D.subschemeι.base) : D ≤ integralComponentAt x := by
  refine Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.1 ?_
  rw [D.range_subschemeι] at hx
  exact (TopologicalSpace.Closeds.closure_le).2 (Set.singleton_subset_iff.2 hx)

/-- An integral closed subscheme through a point off a closed subscheme `D` does not lie inside
`D`. -/
theorem not_le_integralComponentAt_of_not_mem {D : X.IdealSheafData} {x : X}
    (hx : x ∉ Set.range D.subschemeι.base) : ¬ D ≤ integralComponentAt x := by
  intro h
  refine hx ?_
  rw [D.range_subschemeι]
  have hsupp := Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.2 h
  exact hsupp (subset_closure (Set.mem_singleton x))

/-- **Remark 0B6Z on Chow groups.** For the Gysin system of the first Chern class rule, if the
restriction of `L` to the zero scheme `D = Z(s)` is trivial, the Gysin map of Stacks 02TO sends the
class of a cycle to the class of the canonical Gysin map on cycles of Remark 0B6Z.

The cycle splits into its part supported on `D`, which is pushed forward from `D`, and the rest.
On the first part both maps vanish: the Gysin map by
`Stacks.Chow.gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero`, the map on
cycles because it is zero on every integral component inside `D`. On the second part every
component meets `D` properly, where the two rules coincide. -/
theorem gysinSystemOfInvertible_onChowEqGysinCycleMap (C : ChowSituation.{u}) :
    (gysinSystemOfInvertible C).OnChowEqGysinCycleMap := by
  intro T q _ L _ s htriv k δ
  classical
  set D := Stacks.Divisors.zeroScheme T L s with hD
  -- the part of `δ` supported on `D`, pushed forward from `D`
  set δin : CycleGroup C q (k + 1) := properPushforward C (D.subschemeι ≫ q) q D.subschemeι rfl
    (k + 1) ⟨cycleComap D.subschemeι D.subschemeι.isClosedEmbedding.injective δ.1,
      cycleComap_mem_cyclesOfDimension_of_isClosedImmersion C q _ D.subschemeι rfl (k + 1) δ.2⟩
    with hδin
  have hin_supp : Function.support δin.1 ⊆ Set.range D.subschemeι.base :=
    support_properPushforward_subset C _ q D.subschemeι rfl (k + 1) _
  have hout_supp : Function.support (δ - δin).1 ⊆ (Set.range D.subschemeι.base)ᶜ := by
    rintro x hx ⟨y, rfl⟩
    refine hx ?_
    change δ.1 (D.subschemeι.base y) - δin.1 (D.subschemeι.base y) = 0
    rw [hδin, properPushforward_cycleComap_apply_of_isClosedImmersion, sub_self]
  -- the map on cycles kills the part supported on `D`
  have hcyc_in : gysinCycleMap C q k L s htriv δin = 0 := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    change ((gysinCycleMapRule C q k L s).extendCycleGroup δin).1 y = 0
    rw [GysinChernCap.extendCycleGroup_eq_finsum_cycle]
    refine finsum_eq_zero_of_forall_eq_zero fun i ↦ ?_
    rw [show (gysinCycleMapRule C q k L s).cycle = gysinCycleMapComponent C q k L s from rfl,
      gysinCycleMapComponent_of_le C q k L s _ _ _
        (le_integralComponentAt_of_mem (hin_supp i.2)), smul_zero]
    rfl
  -- on the rest the two rules agree
  have hrule_out : (gysinRule C q k L s (firstChernComponentClass C q k L)).extendCycleGroup
      (δ - δin) = gysinCycleMap C q k L s htriv (δ - δin) := by
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
    change _ = ((gysinCycleMapRule C q k L s).extendCycleGroup (δ - δin)).1 y
    rw [GysinChernCap.extendCycleGroup_eq_finsum_cycle,
      GysinChernCap.extendCycleGroup_eq_finsum_cycle]
    refine finsum_congr fun i ↦ ?_
    have hnot := not_le_integralComponentAt_of_not_mem (hout_supp i.2)
    rw [show (gysinCycleMapRule C q k L s).cycle = gysinCycleMapComponent C q k L s from rfl,
      show (gysinRule C q k L s (firstChernComponentClass C q k L)).cycle =
        gysinComponentCycle C q k L s (firstChernComponentClass C q k L) from rfl,
      gysinComponentCycle_of_not_le C q k L s _ _ _ _ hnot,
      gysinCycleMapComponent_of_not_le C q k L s _ _ _ hnot]
  -- the Gysin map kills the part supported on `D`
  have hgys_in : (gysinSystemOfInvertible C).onChow q L s k
      (QuotientAddGroup.mk' (rationalEquivalences C q (k + 1)) δin) = 0 :=
    gysinHomomorphismOfInvertible_properPushforward_zeroSchemeι_eq_zero C q k L s htriv _
  have hsplit : δ = δin + (δ - δin) := by abel
  rw [hsplit, map_add, map_add, hgys_in, map_add, hcyc_in, zero_add, zero_add]
  exact congrArg QuotientAddGroup.mk hrule_out

end Stacks.Chow

end
