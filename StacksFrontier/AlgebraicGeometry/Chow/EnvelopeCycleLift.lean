module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow

/-!
# Lifting cycles along a completely decomposed morphism

Let `X` be a scheme locally of finite type over the base scheme `S` of chapter 42 of the Stacks
Project and let `f : Y ⟶ X` be completely decomposed (Stacks 0GTI), that is, every point of `X`
has a preimage with the same residue field. Choosing such a preimage `y` for each `x` gives a
section of `f` on points, and transporting the coefficients of a cycle along it lifts every
`k`-cycle on `X` to a `k`-cycle on `Y` whose proper pushforward is the cycle one started from.

For an envelope `f` (Stacks 0GU5) this is exactly the surjectivity half of Stacks 0GU8: proper
pushforward `A_k(Y) → A_k(X)` along an envelope is surjective.

## Main definitions

* `Stacks.Chow.envelopePointLift` — the chosen preimage of a point under a completely
  decomposed morphism.
* `Stacks.Chow.envelopeLiftCycleCoeff`, `Stacks.Chow.envelopeLiftCycle` — the lifted
  coefficient function and the cycle it defines.
* `Stacks.Chow.envelopeCycleLift` — the lift of a `k`-cycle, as a map
  `Z_k(X) → Z_k(Y)`.

## Main results

* `Stacks.Chow.relativeDimension_eq_of_residueFieldMap_isIso` — a point at which a morphism
  induces an isomorphism of residue fields has the same relative dimension over the base as its
  image.
* `Stacks.Chow.residueDegree_eq_one_of_residueFieldMap_isIso` — such a point has residue
  degree one.
* `Stacks.Chow.envelopeCycleLift_pushforward` — proper pushforward of the lift is the original
  cycle.
* `Stacks.Chow.envelope_chow_surjective` — proper pushforward on Chow groups along an envelope is
  surjective.

## Implementation notes

### Stacks 02S2 is an explicit hypothesis

Proper pushforward on Chow groups, `Stacks.Chow.properChowPushforward`, carries the vanishing of
Stacks 02S2 as an explicit hypothesis
`Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence`, and
`Stacks.Chow.envelope_chow_surjective` assumes it for the envelope itself.

### The lift is a map of cycle groups, not a homomorphism

`Stacks.Chow.envelopeCycleLift` is additive in the cycle, since the chosen preimage does not
depend on it, but the additive structure is not recorded.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0GU5](https://stacks.math.columbia.edu/tag/0GU5)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Points with an isomorphism of residue fields -/

/-- A point at which a morphism induces an isomorphism on residue fields has the same relative
dimension over the base as its image. -/
theorem relativeDimension_eq_of_residueFieldMap_isIso (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) (f : Y ⟶ X) (y : Y)
    (hy : IsIso (f.residueFieldMap y)) :
    relativeDimension C.dimensionFunction (f ≫ sX) y =
      relativeDimension C.dimensionFunction sX (f.base y) := by
  let _ : Algebra (C.S.residueField (sX.base (f.base y))) (X.residueField (f.base y)) :=
    (sX.residueFieldMap (f.base y)).hom.toAlgebra
  let _ : Algebra (C.S.residueField (sX.base (f.base y))) (Y.residueField y) :=
    ((f ≫ sX).residueFieldMap y).hom.toAlgebra
  let e : X.residueField (f.base y) ≃+* Y.residueField y :=
    (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  have he : ∀ a : C.S.residueField (sX.base (f.base y)),
      e (algebraMap _ _ a) = algebraMap _ _ a := by
    intro a
    change (f.residueFieldMap y).hom ((sX.residueFieldMap (f.base y)).hom a) =
      ((f ≫ sX).residueFieldMap y).hom a
    rw [Scheme.residueFieldMap_comp]
    rfl
  let eA : X.residueField (f.base y) ≃ₐ[C.S.residueField (sX.base (f.base y))]
      Y.residueField y := AlgEquiv.ofRingEquiv (f := e) he
  change C.dimensionFunction (sX.base (f.base y)) +
      (Cardinal.toNat (Algebra.trdeg (C.S.residueField (sX.base (f.base y)))
        (Y.residueField y)) : ℤ) =
    C.dimensionFunction (sX.base (f.base y)) +
      (Cardinal.toNat (Algebra.trdeg (C.S.residueField (sX.base (f.base y)))
        (X.residueField (f.base y))) : ℤ)
  rw [eA.trdeg_eq]

/-- A point at which a morphism induces an isomorphism on residue fields has residue degree
one. -/
theorem residueDegree_eq_one_of_residueFieldMap_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y)
    (hy : IsIso (f.residueFieldMap y)) : f.residueDegree y = 1 := by
  have hb : Function.Bijective (f.residueFieldMap y) :=
    ConcreteCategory.bijective_of_isIso (C := CommRingCat) (f.residueFieldMap y)
  let _ := (f.residueFieldMap y).hom.toAlgebra
  change Module.finrank (X.residueField (f.base y)) (Y.residueField y) = 1
  exact Module.finrank_of_bijective_algebraMap hb

/-! ### The chosen preimage of a point -/

/-- The preimage of `x` chosen by the complete decomposition of `f`: a point of `Y` above `x` at
which `f` induces an isomorphism of residue fields. -/
def envelopePointLift {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f) (x : X) :
    Y := Classical.choose (hcd x)

/-- The chosen preimage lies above the point it was chosen for. -/
@[simp]
theorem envelopePointLift_map {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f)
    (x : X) : f.base (envelopePointLift f hcd x) = x := (Classical.choose_spec (hcd x)).1

/-- At the chosen preimage the morphism induces an isomorphism of residue fields. -/
theorem envelopePointLift_residueFieldMap_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (x : X) :
    IsIso (f.residueFieldMap (envelopePointLift f hcd x)) := (Classical.choose_spec (hcd x)).2

/-! ### Lifting a cycle -/

open scoped Classical in
/-- The coefficient function of the lifted cycle: it carries the coefficient of `c` at `f y` to
the chosen preimage of `f y`, and vanishes at every other point. -/
def envelopeLiftCycleCoeff {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f)
    (c : AlgebraicCycle X ℤ) (y : Y) : ℤ :=
  if envelopePointLift f hcd (f.base y) = y then c (f.base y) else 0

/-- At a point which is the chosen preimage of its own image, the lifted coefficient is the
coefficient of `c` at that image. -/
theorem envelopeLiftCycleCoeff_of_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle X ℤ) {y : Y}
    (hy : envelopePointLift f hcd (f.base y) = y) :
    envelopeLiftCycleCoeff f hcd c y = c (f.base y) := ite_eq_left hy

/-- At every other point the lifted coefficient vanishes. -/
theorem envelopeLiftCycleCoeff_of_ne {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle X ℤ) {y : Y}
    (hy : envelopePointLift f hcd (f.base y) ≠ y) :
    envelopeLiftCycleCoeff f hcd c y = 0 := ite_eq_right hy

/-- A point where the lifted coefficient is nonzero is the chosen preimage of its image. -/
private theorem envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero {X Y : Scheme.{u}}
    (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle X ℤ) {y : Y}
    (hy : envelopeLiftCycleCoeff f hcd c y ≠ 0) : envelopePointLift f hcd (f.base y) = y :=
  of_not_not fun h ↦ hy (envelopeLiftCycleCoeff_of_ne f hcd c h)

/-- The lifted coefficient function has locally finite support. -/
theorem envelopeLiftCycleCoeff_locallyFiniteSupport {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle X ℤ) :
    LocallyFiniteSupport (envelopeLiftCycleCoeff f hcd c) := by
  classical
  intro y
  obtain ⟨U, hU, hfin⟩ := c.supportLocallyFiniteWithinDomain (f.base y) (by trivial)
  refine ⟨f.base ⁻¹' U, f.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
  apply Set.Finite.of_injOn
    (s := f.base ⁻¹' U ∩ (envelopeLiftCycleCoeff f hcd c).support) (t := U ∩ c.support)
  · intro z ⟨hzU, hz⟩
    have hne := Function.mem_support.mp hz
    have hlift := envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero f hcd c hne
    rw [envelopeLiftCycleCoeff_of_eq f hcd c hlift] at hne
    exact ⟨hzU, Function.mem_support.mpr hne⟩
  · intro a ha b hb hab
    have ha' := envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero f hcd c ha.2
    have hb' := envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero f hcd c hb.2
    rw [← ha', hab, hb']
  · exact hfin

/-- The lift of a cycle along a completely decomposed morphism: the cycle on `Y` with the
coefficients of `Stacks.Chow.envelopeLiftCycleCoeff`. -/
def envelopeLiftCycle {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f)
    (c : AlgebraicCycle X ℤ) : AlgebraicCycle Y ℤ where
  toFun := envelopeLiftCycleCoeff f hcd c
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' _ _ :=
    envelopeLiftCycleCoeff_locallyFiniteSupport f hcd c _

/-- The coefficient of `Stacks.Chow.envelopeLiftCycle f hcd c` at `y` is
`Stacks.Chow.envelopeLiftCycleCoeff f hcd c y`. -/
@[simp]
theorem envelopeLiftCycle_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle X ℤ) (y : Y) :
    envelopeLiftCycle f hcd c y = envelopeLiftCycleCoeff f hcd c y := rfl

/-- The lift of a `k`-cycle is a `k`-cycle. -/
theorem envelopeLiftCycle_mem_cyclesOfDimension (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C sX k) :
    envelopeLiftCycle f hcd c.1 ∈ cyclesOfDimension C (f ≫ sX) k := by
  classical
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y hy
  have hy' : envelopeLiftCycleCoeff f hcd c.1 y ≠ 0 := hy
  have hlift := envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero f hcd c.1 hy'
  have hc : c.1 (f.base y) ≠ 0 := by
    rwa [envelopeLiftCycleCoeff_of_eq f hcd c.1 hlift] at hy'
  have hres : IsIso (f.residueFieldMap y) := by
    rw [← hlift]
    exact envelopePointLift_residueFieldMap_isIso f hcd (f.base y)
  rw [relativeDimension_eq_of_residueFieldMap_isIso C sX f y hres]
  exact (mem_cyclesOfDimension_iff_forall_point C sX k c.1).mp c.2 (f.base y) hc

/-- The lift of a `k`-cycle along a completely decomposed morphism, as a map
`Z_k(X) → Z_k(Y)`. -/
def envelopeCycleLift (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C sX k) :
    CycleGroup C (f ≫ sX) k :=
  ⟨envelopeLiftCycle f hcd c.1, envelopeLiftCycle_mem_cyclesOfDimension C sX f hcd k c⟩

/-- Proper pushforward of the lift of a cycle is the cycle itself. -/
theorem envelopeCycleLift_pushforward (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C sX k) :
    properPushforward C (f ≫ sX) sX f rfl k (envelopeCycleLift C sX f hcd k c) = c := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [properPushforward_apply]
  set y₀ := envelopePointLift f hcd x with hy₀def
  have hy₀ : f.base y₀ = x := envelopePointLift_map f hcd x
  set φ : Y → ℤ := fun y ↦ (envelopeCycleLift C sX f hcd k c).1 y *
    (if relativeDimension C.dimensionFunction (f ≫ sX) y =
        relativeDimension C.dimensionFunction sX (f.base y)
      then (f.residueDegree y : ℤ) else 0) with hφdef
  have hsupport : f.base ⁻¹' ({x} : Set X) ∩ Function.support φ =
      (({y₀} : Finset Y) : Set Y) ∩ Function.support φ := by
    ext y
    refine ⟨fun ⟨hyx, hyφ⟩ ↦ ⟨?_, hyφ⟩, fun ⟨hy, hyφ⟩ ↦ ⟨?_, hyφ⟩⟩
    · have hcoeff : envelopeLiftCycleCoeff f hcd c.1 y ≠ 0 :=
        left_ne_zero_of_mul (Function.mem_support.mp hyφ)
      have hchosen := envelopePointLift_eq_of_envelopeLiftCycleCoeff_ne_zero f hcd c.1 hcoeff
      rw [(hyx : f.base y = x)] at hchosen
      simp [hy₀def, hchosen]
    · obtain rfl : y = y₀ := by simpa using hy
      simpa using hy₀
  rw [finsum_mem_eq_sum_of_inter_support_eq φ hsupport]
  have hres₀ : IsIso (f.residueFieldMap y₀) := envelopePointLift_residueFieldMap_isIso f hcd x
  have hdim₀ := relativeDimension_eq_of_residueFieldMap_isIso C sX f y₀ hres₀
  have hdeg₀ := residueDegree_eq_one_of_residueFieldMap_isIso f y₀ hres₀
  have hcoeff₀ : (envelopeCycleLift C sX f hcd k c).1 y₀ = c.1 x := by
    change envelopeLiftCycleCoeff f hcd c.1 y₀ = c.1 x
    rw [envelopeLiftCycleCoeff_of_eq f hcd c.1 (by rw [hy₀, hy₀def]), hy₀]
  have hφ₀ : φ y₀ = c.1 x := by
    rw [hφdef]
    change (envelopeCycleLift C sX f hcd k c).1 y₀ * _ = c.1 x
    rw [ite_eq_left hdim₀, hdeg₀, hcoeff₀, Nat.cast_one, mul_one]
  rw [Finset.sum_singleton, hφ₀]

/-! ### Surjectivity of pushforward along an envelope -/

/-- Proper pushforward on Chow groups along an envelope `f : Y ⟶ X` is surjective. -/
theorem envelope_chow_surjective (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : Y ⟶ X) (hf : IsEnvelope f) (k : ℤ)
    (hfac : letI : IsProper f := hf.isProper
      ProperPushforwardFactorsThroughRationalEquivalence C (f ≫ sX) sX f rfl k) :
    letI : IsProper f := hf.isProper
    Function.Surjective (properChowPushforward C (f ≫ sX) sX f rfl k hfac) := by
  let _ : IsProper f := hf.isProper
  intro β
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX k) β
  refine ⟨QuotientAddGroup.mk' (rationalEquivalences C (f ≫ sX) k)
    (envelopeCycleLift C sX f hf.isCompletelyDecomposed k c), ?_⟩
  rw [properChowPushforward_mk,
    envelopeCycleLift_pushforward C sX f hf.isCompletelyDecomposed k c]
  exact hc

end Stacks.Chow

end
