module

public import StacksFrontier.AlgebraicGeometry.Chow.ChowGroupsEnvelopes.SubschemeLift
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentProduct

/-!
# Cycles on the fibre square of a completely decomposed morphism

Let `f : Y ⟶ X` be proper and completely decomposed and let `p, q : Y ×_X Y ⟶ Y` be the two
projections. A `k`-cycle `β` on `Y` whose pushforward to `X` vanishes is the difference
`p_* γ - q_* γ` of the pushforwards of a single `k`-cycle `γ` on `Y ×_X Y`: take for `γ` the
cycle supported on the points `(y, y')` with `y'` the chosen preimage of the image of `y`, with
the coefficient of `β` at `y`. Then `p_* γ = β`, while `q_* γ` is supported on chosen preimages
only and pushes forward to zero on `X`, hence vanishes.

## Main definitions

* `Stacks.Chow.envelopeFibreCycleCoeff`, `Stacks.Chow.envelopeFibreCycle` — the lifted cycle on
  the fibre square.

## Main results

* `Stacks.Chow.pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso` and
  `Stacks.Chow.pullbackPoint_eq_of_proj_eq_of_snd_residueFieldMap_isIso` — a point of a fibre
  product is determined by its two projections as soon as one of the two structure morphisms is
  an isomorphism on residue fields there.
* `Stacks.Chow.envelopeFibreCycle_fst_pushforward` — the first projection pushes the lifted
  cycle forward to the cycle it was built from.
* `Stacks.Chow.cycle_eq_zero_of_forall_envelopePointLift` — a cycle supported on chosen
  preimages and pushing forward to zero is zero.
* `Stacks.Chow.exists_fibre_difference_of_properPushforward_eq_zero` — a `k`-cycle on `Y` whose
  pushforward to `X` vanishes is `p_* γ - q_* γ`.

## References

* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0GTI](https://stacks.math.columbia.edu/tag/0GTI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Points of a fibre product -/

/-- A point of a fibre product is determined by its two projections as soon as the first
structure morphism induces an isomorphism of residue fields at its first projection. -/
theorem pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (a b : (pullback f g : Scheme))
    (hfst : (pullback.fst f g).base a = (pullback.fst f g).base b)
    (hsnd : (pullback.snd f g).base a = (pullback.snd f g).base b)
    (hres : IsIso (f.residueFieldMap ((pullback.fst f g).base a))) : a = b := by
  apply Scheme.Pullback.carrierEquiv.injective
  refine Scheme.Pullback.carrierEquiv_eq_iff.mpr ⟨Scheme.Pullback.Triplet.ext hfst hsnd, ?_⟩
  set T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint b
  have : IsIso (f.residueFieldMap T.x) := by
    show IsIso (f.residueFieldMap ((pullback.fst f g).base b))
    rwa [← hfst]
  have : IsIso T.tensorInr := pushout_inr_iso_of_left_iso _ _
  have : Subsingleton (Spec (CommRingCat.of (Y.residueField T.y))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (Y.residueField T.y)))
  have e : Spec T.tensor ≅ Spec (CommRingCat.of (Y.residueField T.y)) :=
    Scheme.Spec.mapIso (asIso T.tensorInr).op
  exact e.hom.homeomorph.subsingleton.elim _ _

/-- A point of a fibre product is determined by its two projections as soon as the second
structure morphism induces an isomorphism of residue fields at its second projection. -/
theorem pullbackPoint_eq_of_proj_eq_of_snd_residueFieldMap_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Z)
    (g : Y ⟶ Z) (a b : (pullback f g : Scheme))
    (hfst : (pullback.fst f g).base a = (pullback.fst f g).base b)
    (hsnd : (pullback.snd f g).base a = (pullback.snd f g).base b)
    (hres : IsIso (g.residueFieldMap ((pullback.snd f g).base a))) : a = b := by
  set e : pullback f g ≅ pullback g f := pullbackSymmetry f g
  have hfstPoint (z : (pullback f g : Scheme)) :
      (pullback.fst g f).base (e.hom.base z) = (pullback.snd f g).base z :=
    congrArg (fun h : pullback f g ⟶ Y ↦ h.base z) (pullbackSymmetry_hom_comp_fst f g)
  have hsndPoint (z : (pullback f g : Scheme)) :
      (pullback.snd g f).base (e.hom.base z) = (pullback.fst f g).base z :=
    congrArg (fun h : pullback f g ⟶ X ↦ h.base z) (pullbackSymmetry_hom_comp_snd f g)
  exact e.hom.homeomorph.injective <|
    pullbackPoint_eq_of_proj_eq_of_residueFieldMap_isIso g f (e.hom.base a) (e.hom.base b)
      ((hfstPoint a).trans (hsnd.trans (hfstPoint b).symm))
      ((hsndPoint a).trans (hfst.trans (hsndPoint b).symm)) (by rwa [hfstPoint a])

/-! ### The fibre square of a morphism -/

/-- The two structure morphisms of the fibre square `Y ×_X Y` over the base obtained from the two
projections agree. -/
theorem pullback_snd_comp_eq_pullback_fst_comp {X Y S : Scheme.{u}} (f : Y ⟶ X) (sX : X ⟶ S) :
    pullback.snd f f ≫ f ≫ sX = pullback.fst f f ≫ f ≫ sX := by
  rw [pullback.condition_assoc]

/-- Above every point `y` of `Y` the fibre square has a point whose first projection is `y` and
whose second projection is the chosen preimage of the image of `y`. -/
theorem exists_fibrePoint_envelopePointLift {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (y : Y) :
    ∃ z : (pullback f f : Scheme), (pullback.fst f f).base z = y ∧
      (pullback.snd f f).base z = envelopePointLift f hcd (f.base y) :=
  Scheme.Pullback.exists_preimage_pullback y (envelopePointLift f hcd (f.base y))
    (by rw [envelopePointLift_map])

/-! ### The lifted cycle on the fibre square -/

open scoped Classical in
/-- The coefficient function of the lifted cycle on the fibre square: at a point whose second
projection is the chosen preimage of the image of its first projection it is the coefficient of
`c` at that first projection, and it vanishes elsewhere. -/
def envelopeFibreCycleCoeff {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f)
    (c : AlgebraicCycle Y ℤ) (z : (pullback f f : Scheme)) : ℤ :=
  if (pullback.snd f f).base z =
      envelopePointLift f hcd (f.base ((pullback.fst f f).base z))
    then c ((pullback.fst f f).base z) else 0

/-- At a point whose second projection is the chosen preimage of the image of its first
projection the lifted coefficient is the coefficient of `c`. -/
theorem envelopeFibreCycleCoeff_of_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) {z : (pullback f f : Scheme)}
    (hz : (pullback.snd f f).base z =
      envelopePointLift f hcd (f.base ((pullback.fst f f).base z))) :
    envelopeFibreCycleCoeff f hcd c z = c ((pullback.fst f f).base z) := ite_eq_left hz

/-- At every other point the lifted coefficient vanishes. -/
theorem envelopeFibreCycleCoeff_of_ne {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) {z : (pullback f f : Scheme)}
    (hz : (pullback.snd f f).base z ≠
      envelopePointLift f hcd (f.base ((pullback.fst f f).base z))) :
    envelopeFibreCycleCoeff f hcd c z = 0 := ite_eq_right hz

/-- A point carrying a nonzero lifted coefficient has its second projection equal to the chosen
preimage of the image of its first projection. -/
theorem envelopeFibreCycleCoeff_snd_eq {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) {z : (pullback f f : Scheme)}
    (hz : envelopeFibreCycleCoeff f hcd c z ≠ 0) :
    (pullback.snd f f).base z =
      envelopePointLift f hcd (f.base ((pullback.fst f f).base z)) :=
  of_not_not fun h ↦ hz (envelopeFibreCycleCoeff_of_ne f hcd c h)

/-- A point carrying a nonzero lifted coefficient has its second projection a point at which `f`
induces an isomorphism of residue fields. -/
theorem envelopeFibreCycleCoeff_residueFieldMap_isIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) {z : (pullback f f : Scheme)}
    (hz : envelopeFibreCycleCoeff f hcd c z ≠ 0) :
    IsIso (f.residueFieldMap ((pullback.snd f f).base z)) := by
  rw [envelopeFibreCycleCoeff_snd_eq f hcd c hz]
  exact envelopePointLift_residueFieldMap_isIso f hcd _

/-- The lifted coefficient function has locally finite support. -/
theorem envelopeFibreCycleCoeff_locallyFiniteSupport {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) :
    LocallyFiniteSupport (envelopeFibreCycleCoeff f hcd c) := by
  classical
  intro z
  obtain ⟨U, hU, hfin⟩ := c.supportLocallyFiniteWithinDomain
    ((pullback.fst f f).base z) (by trivial)
  refine ⟨(pullback.fst f f).base ⁻¹' U,
    (pullback.fst f f).continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
  apply Set.Finite.of_injOn
    (s := (pullback.fst f f).base ⁻¹' U ∩ (envelopeFibreCycleCoeff f hcd c).support)
    (t := U ∩ c.support)
  · rintro w ⟨hwU, hw : envelopeFibreCycleCoeff f hcd c w ≠ 0⟩
    refine ⟨hwU, Function.mem_support.mpr ?_⟩
    rwa [envelopeFibreCycleCoeff_of_eq f hcd c (envelopeFibreCycleCoeff_snd_eq f hcd c hw)] at hw
  · rintro a ⟨-, ha⟩ b ⟨-, hb⟩ hab
    refine pullbackPoint_eq_of_proj_eq_of_snd_residueFieldMap_isIso f f a b hab ?_
      (envelopeFibreCycleCoeff_residueFieldMap_isIso f hcd c ha)
    rw [envelopeFibreCycleCoeff_snd_eq f hcd c ha, envelopeFibreCycleCoeff_snd_eq f hcd c hb, hab]
  · exact hfin

/-- The lifted cycle on the fibre square, as an algebraic cycle. -/
def envelopeFibreAlgebraicCycle {X Y : Scheme.{u}} (f : Y ⟶ X) (hcd : IsCompletelyDecomposed f)
    (c : AlgebraicCycle Y ℤ) : AlgebraicCycle (pullback f f) ℤ where
  toFun := envelopeFibreCycleCoeff f hcd c
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' _ _ :=
    envelopeFibreCycleCoeff_locallyFiniteSupport f hcd c _

/-- The lifted cycle on the fibre square has the lifted coefficient at every point. -/
@[simp]
theorem envelopeFibreAlgebraicCycle_apply {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hcd : IsCompletelyDecomposed f) (c : AlgebraicCycle Y ℤ) (z : (pullback f f : Scheme)) :
    envelopeFibreAlgebraicCycle f hcd c z = envelopeFibreCycleCoeff f hcd c z := rfl

/-- The lift of a `k`-cycle on `Y` is a `k`-cycle on the fibre square. -/
theorem envelopeFibreAlgebraicCycle_mem_cyclesOfDimension (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X)
    [LocallyOfFiniteType f] (hcd : IsCompletelyDecomposed f) (k : ℤ)
    (c : CycleGroup C (f ≫ sX) k) :
    envelopeFibreAlgebraicCycle f hcd c.1 ∈
      cyclesOfDimension C (pullback.fst f f ≫ f ≫ sX) k := by
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro z hz
  have hz' : envelopeFibreCycleCoeff f hcd c.1 z ≠ 0 := hz
  have hcoeff : c.1 ((pullback.fst f f).base z) ≠ 0 := by
    rwa [envelopeFibreCycleCoeff_of_eq f hcd c.1
      (envelopeFibreCycleCoeff_snd_eq f hcd c.1 hz')] at hz'
  have hres : IsIso ((pullback.fst f f).residueFieldMap z) :=
    fst_residueFieldMap_isIso_of_snd f f z
      (envelopeFibreCycleCoeff_residueFieldMap_isIso f hcd c.1 hz')
  rw [relativeDimension_eq_of_residueFieldMap_isIso C (f ≫ sX) (pullback.fst f f) z hres]
  exact (mem_cyclesOfDimension_iff_forall_point C (f ≫ sX) k c.1).mp c.2 _ hcoeff

/-- The lift of a `k`-cycle on `Y` to the fibre square `Y ×_X Y`. -/
def envelopeFibreCycle (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (f : Y ⟶ X) [LocallyOfFiniteType f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C (f ≫ sX) k) :
    CycleGroup C (pullback.fst f f ≫ f ≫ sX) k :=
  ⟨envelopeFibreAlgebraicCycle f hcd c.1,
    envelopeFibreAlgebraicCycle_mem_cyclesOfDimension C sX f hcd k c⟩

/-! ### Pushing the lifted cycle forward along the two projections -/

/-- The first projection pushes the lifted cycle forward to the cycle it was built from. -/
theorem envelopeFibreCycle_fst_pushforward (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C (f ≫ sX) k) :
    properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k
      (envelopeFibreCycle C sX f hcd k c) = c := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  rw [properPushforward_apply]
  obtain ⟨z₀, hz₀fst, hz₀snd⟩ := exists_fibrePoint_envelopePointLift f hcd y
  set φ : ↥(pullback f f) → ℤ := fun z ↦
    (envelopeFibreCycle C sX f hcd k c).1 z *
      (if relativeDimension C.dimensionFunction (pullback.fst f f ≫ f ≫ sX) z =
          relativeDimension C.dimensionFunction (f ≫ sX) ((pullback.fst f f).base z)
        then ((pullback.fst f f).residueDegree z : ℤ) else 0) with hφ
  have hsupport : (pullback.fst f f).base ⁻¹' ({y} : Set Y) ∩ Function.support φ =
      (({z₀} : Finset (pullback f f : Scheme)) : Set (pullback f f : Scheme)) ∩
        Function.support φ := by
    ext z
    constructor
    · rintro ⟨hzy : (pullback.fst f f).base z = y, hzφ⟩
      have hcz : envelopeFibreCycleCoeff f hcd c.1 z ≠ 0 := left_ne_zero_of_mul hzφ
      refine ⟨?_, hzφ⟩
      rw [Finset.coe_singleton, Set.mem_singleton_iff]
      refine pullbackPoint_eq_of_proj_eq_of_snd_residueFieldMap_isIso f f z z₀
        (by rw [hzy, hz₀fst]) ?_ (envelopeFibreCycleCoeff_residueFieldMap_isIso f hcd c.1 hcz)
      rw [envelopeFibreCycleCoeff_snd_eq f hcd c.1 hcz, hzy, hz₀snd]
    · rintro ⟨hz, hzφ⟩
      obtain rfl : z = z₀ := by simpa using hz
      exact ⟨hz₀fst, hzφ⟩
  rw [finsum_mem_eq_sum_of_inter_support_eq φ hsupport]
  have hsndres : IsIso (f.residueFieldMap ((pullback.snd f f).base z₀)) := by
    rw [hz₀snd]
    exact envelopePointLift_residueFieldMap_isIso f hcd _
  have hfstres : IsIso ((pullback.fst f f).residueFieldMap z₀) :=
    fst_residueFieldMap_isIso_of_snd f f z₀ hsndres
  have hdim := relativeDimension_eq_of_residueFieldMap_isIso C (f ≫ sX) (pullback.fst f f)
    z₀ hfstres
  have hdeg := residueDegree_eq_one_of_residueFieldMap_isIso (pullback.fst f f) z₀ hfstres
  have hcoeff : (envelopeFibreCycle C sX f hcd k c).1 z₀ = c.1 y := by
    show envelopeFibreCycleCoeff f hcd c.1 z₀ = c.1 y
    rw [envelopeFibreCycleCoeff_of_eq f hcd c.1 (by rw [hz₀snd, hz₀fst]), hz₀fst]
  rw [Finset.sum_singleton, hφ]
  show (envelopeFibreCycle C sX f hcd k c).1 z₀ * _ = c.1 y
  rw [ite_eq_left hdim, hdeg, hcoeff, Nat.cast_one, mul_one]

/-- A `k`-cycle on `Y` supported on chosen preimages whose pushforward to `X` vanishes is zero. -/
theorem cycle_eq_zero_of_forall_envelopePointLift (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C (f ≫ sX) k)
    (hsel : ∀ y : Y, c.1 y ≠ 0 → envelopePointLift f hcd (f.base y) = y)
    (hpush : properPushforward C (f ≫ sX) sX f rfl k c = 0) : c = 0 := by
  classical
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  show c.1 y = 0
  by_contra hcy
  have hy := hsel y hcy
  have hcoeff := congrArg (fun d : CycleGroup C sX k ↦ d.1 (f.base y)) hpush
  rw [properPushforward_apply] at hcoeff
  set φ : Y → ℤ := fun w ↦ c.1 w *
    (if relativeDimension C.dimensionFunction (f ≫ sX) w =
        relativeDimension C.dimensionFunction sX (f.base w)
      then (f.residueDegree w : ℤ) else 0) with hφ
  have hsupp : f.base ⁻¹' ({f.base y} : Set X) ∩ Function.support φ =
      (({envelopePointLift f hcd (f.base y)} : Finset Y) : Set Y) ∩ Function.support φ := by
    ext w
    constructor
    · rintro ⟨hw : f.base w = f.base y, hwφ⟩
      refine ⟨?_, hwφ⟩
      rw [Finset.coe_singleton, Set.mem_singleton_iff, ← hw, hsel w (left_ne_zero_of_mul hwφ)]
    · rintro ⟨hw, hwφ⟩
      obtain rfl : w = envelopePointLift f hcd (f.base y) := by simpa using hw
      exact ⟨by simp [envelopePointLift_map], hwφ⟩
  have hres := envelopePointLift_residueFieldMap_isIso f hcd (f.base y)
  have hdim := relativeDimension_eq_of_residueFieldMap_isIso C sX f
    (envelopePointLift f hcd (f.base y)) hres
  have hdeg := residueDegree_eq_one_of_residueFieldMap_isIso f
    (envelopePointLift f hcd (f.base y)) hres
  rw [hy] at hdim hdeg
  have hvalue : φ (envelopePointLift f hcd (f.base y)) = c.1 y := by
    rw [hφ, hy]
    show c.1 y * _ = c.1 y
    rw [ite_eq_left hdim, hdeg, Nat.cast_one, mul_one]
  rw [finsum_mem_eq_sum_of_inter_support_eq φ hsupp, Finset.sum_singleton, hvalue] at hcoeff
  exact hcy hcoeff

/-- The second projection pushes the lifted cycle forward to a cycle supported on chosen
preimages only. -/
theorem envelopeFibreCycle_snd_pushforward_selected (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C (f ≫ sX) k) (y : Y)
    (hy : (properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
      (pullback_snd_comp_eq_pullback_fst_comp f sX) k
      (envelopeFibreCycle C sX f hcd k c)).1 y ≠ 0) :
    envelopePointLift f hcd (f.base y) = y := by
  classical
  by_contra hnot
  apply hy
  rw [properPushforward_apply]
  apply finsum_eq_zero_of_forall_eq_zero
  intro z
  rw [finsum_eq_if]
  refine ite_eq_right_iff.mpr fun hzy : (pullback.snd f f).base z = y ↦ ?_
  have hdz : (envelopeFibreCycle C sX f hcd k c).1 z = 0 := by
    by_contra hdz
    apply hnot
    have hfst : f.base ((pullback.snd f f).base z) = f.base ((pullback.fst f f).base z) :=
      congrArg (fun g : pullback f f ⟶ X ↦ g.base z) pullback.condition.symm
    rw [← hzy, hfst, ← envelopeFibreCycleCoeff_snd_eq f hcd c.1 hdz, hzy]
  simp [hdz]

/-- **The kernel of pushforward along a completely decomposed proper morphism.** A `k`-cycle on
`Y` whose pushforward to `X` vanishes is the difference of the pushforwards of a single
`k`-cycle on `Y ×_X Y` along the two projections. -/
theorem exists_fibre_difference_of_properPushforward_eq_zero (C : ChowSituation.{u})
    {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (f : Y ⟶ X) [IsProper f]
    (hcd : IsCompletelyDecomposed f) (k : ℤ) (c : CycleGroup C (f ≫ sX) k)
    (hpush : properPushforward C (f ≫ sX) sX f rfl k c = 0) :
    ∃ γ : CycleGroup C (pullback.fst f f ≫ f ≫ sX) k,
      c = properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f) rfl k γ -
        properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
          (pullback_snd_comp_eq_pullback_fst_comp f sX) k γ := by
  set γ := envelopeFibreCycle C sX f hcd k c
  have hfst : properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.fst f f)
      rfl k γ = c := envelopeFibreCycle_fst_pushforward C sX f hcd k c
  set d := properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) (pullback.snd f f)
    (pullback_snd_comp_eq_pullback_fst_comp f sX) k γ with hd
  have hsel : ∀ y : Y, d.1 y ≠ 0 → envelopePointLift f hcd (f.base y) = y := fun y hy ↦
    envelopeFibreCycle_snd_pushforward_selected C sX f hcd k c y hy
  have hpushd : properPushforward C (f ≫ sX) sX f rfl k d = 0 := by
    rw [hd, properPushforward_properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) sX
      (pullback.snd f f) f (pullback_snd_comp_eq_pullback_fst_comp f sX) rfl k γ,
      properPushforward_apply_congr C (pullback.fst f f ≫ f ≫ sX) sX
        (show pullback.snd f f ≫ f = pullback.fst f f ≫ f from pullback.condition.symm)
        (by rw [Category.assoc, pullback_snd_comp_eq_pullback_fst_comp]) (by rw [Category.assoc])
        k γ,
      ← properPushforward_properPushforward C (pullback.fst f f ≫ f ≫ sX) (f ≫ sX) sX
        (pullback.fst f f) f rfl rfl k γ, hfst]
    exact hpush
  have hdzero : d = 0 := cycle_eq_zero_of_forall_envelopePointLift C sX f hcd k d hsel hpushd
  exact ⟨γ, by rw [hfst, ← hd, hdzero, sub_zero]⟩

end Stacks.Chow

end
