module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.QuasiCoherentDirectImage

/-!
# Lifting quasi-coherent derived objects along a quasi-compact open immersion

Let `X` be a scheme and `j : U ⟶ X` a quasi-compact open immersion. Restriction from `X` to `U`
is essentially surjective on the derived categories with quasi-coherent cohomology: every object
of `D_QCoh(𝒪_U)` is the restriction of an object of `D_QCoh(𝒪_X)`. The same holds on
bounded-below objects, and — when `X` is quasi-compact — on bounded-above and on bounded
objects.

The lift is always the derived direct image `Rj_* E`. It has quasi-coherent cohomology because
`j` is quasi-compact and quasi-separated, and restricting it along `j` recovers `E`. What the
four statements differ in is the boundedness that has to be transported: `Rj_*` preserves a
lower cohomological bound unconditionally, while an upper bound is preserved only up to the
cohomological dimension of `j`, which is finite when `X` is quasi-compact.

## Main results

* `AlgebraicGeometry.exists_quasicoherentDerived_lift`: the unbounded lift.
* `AlgebraicGeometry.exists_quasicoherentDerived_plus_lift`: the bounded-below lift.
* `AlgebraicGeometry.exists_quasicoherentDerived_minus_lift`: the bounded-above lift, for `X`
  quasi-compact.
* `AlgebraicGeometry.exists_quasicoherentDerived_bounded_lift`: the bounded lift, for `X`
  quasi-compact.

## Implementation notes

Essential surjectivity of a functor at an object is the existence of a preimage together with an
isomorphism, which is what the four statements assert; the restriction is written as the derived
pullback `Lj^*` along the open immersion, which is the canonical form of restriction on derived
categories.

Quasi-compactness of `X` enters the last two statements and only those: it is the hypothesis of
the bound on the cohomological dimension of `j`, and the first two statements hold for an
arbitrary scheme `X`.

## References

* [Stacks Project, Tag 08ED](https://stacks.math.columbia.edu/tag/08ED)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedPushforwardUnit)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- Cohomology of a shift: `H^i(K⟦n⟧) ≅ H^{i+n}(K)`, from the shift sequence on the cohomology
functors of the derived category. -/
private def derivedHomologyShiftObjIso {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (K : DerivedCategory C) (i n : ℤ) :
    (DerivedCategory.homologyFunctor C i).obj (K⟦n⟧) ≅
      (DerivedCategory.homologyFunctor C (i + n)).obj K := by
  rw [← DerivedCategory.shift_homologyFunctor C i,
    ← DerivedCategory.shift_homologyFunctor C (i + n)]
  exact ((DerivedCategory.homologyFunctor C 0).shiftIso n i (i + n) (by omega)).app K

section

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]

/-- **The derived direct image along a quasi-compact open immersion into a quasi-compact scheme
raises an upper cohomological bound by a fixed amount.** If `E` has quasi-coherent cohomology
and lies in degrees `≤ b`, then `Rj_* E` lies in degrees `≤ b + N - 1` for an `N` depending only
on `j`.

The bound is [Stacks, Tag 08D5] part (2), which is stated for objects in degrees `≤ 0`; the
general case is obtained from it by shifting, `Rj_*` commuting with the shift. -/
theorem exists_isZero_homology_derivedPushforward_openImmersion_of_isLE [CompactSpace X]
    (E : QuasicoherentDerivedCategory U) (b : ℤ) (hE : E.obj.IsLE b) :
    ∃ N : ℤ, ∀ m : ℤ, b + N - 1 < m →
      IsZero ((DerivedCategory.homologyFunctor X.Modules m).obj
        ((derivedPushforward j.toLRSHom.toShHom).obj E.obj)) := by
  obtain ⟨N, hN⟩ := exists_isZero_homology_derivedPushforward_of_isLE_zero j
  let R := derivedPushforward j.toLRSHom.toShHom
  let T := E.obj⟦b⟧
  have hTqc : ∀ i : ℤ,
      ((DerivedCategory.homologyFunctor U.Modules i).obj T).IsQuasicoherent := fun i =>
    (SheafOfModules.isQuasicoherent U.ringCatSheaf).prop_of_iso
      (derivedHomologyShiftObjIso E.obj i b).symm (E.property (i + b))
  have hTle : T.IsLE 0 := DerivedCategory.TStructure.t.isLE_shift E.obj b b 0 (by omega)
  have hR : (R.obj T).IsLE (N - 1) :=
    (DerivedCategory.isLE_iff _ _).2 fun m hm => hN T hTqc hTle m (by omega)
  let C := SheafOfModules.{u} (structureSheafRing U.toRingedSpace)
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let _ : R.IsRightDerivedFunctor (derivedPushforwardUnit j.toLRSHom.toShHom) W := by
    dsimp [R, W, C]
    infer_instance
  let _ : R.CommShift ℤ :=
    Functor.IsRightDerivedFunctor.commShift R (derivedPushforwardUnit j.toLRSHom.toShHom) W ℤ
  have eComm : R.obj T ≅ (R.obj E.obj)⟦b⟧ := (R.commShiftIso b).app E.obj
  have _ : ((R.obj E.obj)⟦b⟧).IsLE (N - 1) := DerivedCategory.TStructure.t.isLE_of_iso eComm (N - 1)
  exact ⟨N, (DerivedCategory.isLE_iff _ _).1
    (DerivedCategory.TStructure.t.isLE_of_shift (R.obj E.obj) (b + N - 1) b (N - 1) (by omega))⟩

/-- The derived direct image of an object of `D_QCoh(𝒪_U)` along a quasi-compact open immersion,
as an object of `D_QCoh(𝒪_X)`. -/
private def pushforwardLift (E : QuasicoherentDerivedCategory U) :
    QuasicoherentDerivedCategory X :=
  ⟨(derivedPushforward j.toLRSHom.toShHom).obj E.obj,
    isQuasicoherent_derivedPushforward j E⟩

/-- The cohomology of `Rj_* E` vanishes below `a` if the cohomology of `E` does. -/
private theorem isZero_homology_pushforwardLift_of_lt (E : QuasicoherentDerivedCategory U) (a : ℤ)
    (ha : ∀ n < a, IsZero ((DerivedCategory.homologyFunctor U.Modules n).obj E.obj)) :
    ∀ n < a, IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj
      (pushforwardLift j E).obj) :=
  (DerivedCategory.isGE_iff _ a).1
    (isGE_derivedPushforward_obj j E.obj a ((DerivedCategory.isGE_iff E.obj a).2 ha))

/-- **Stacks Project, Tag 08ED.** Every quasi-coherent derived object on a quasi-compact open
subscheme extends to a quasi-coherent derived object on the ambient scheme: the functor
`D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_U)` given by restriction is essentially surjective. -/
@[stacks 08ED "unbounded derived category"]
theorem exists_quasicoherentDerived_lift (E : QuasicoherentDerivedCategory U) :
    ∃ F : QuasicoherentDerivedCategory X,
      Nonempty ((derivedPullback j.toLRSHom.toShHom).obj F.obj ≅ E.obj) :=
  ⟨pushforwardLift j E, ⟨openDerivedPushforwardRestrictionIso j E.obj⟩⟩

/-- **Stacks Project, Tag 08ED.** A bounded-below quasi-coherent derived object on a
quasi-compact open subscheme has a bounded-below quasi-coherent lift: the functor
`D⁺_QCoh(𝒪_X) ⟶ D⁺_QCoh(𝒪_U)` given by restriction is essentially surjective.

No quasi-compactness of the ambient scheme is needed, the derived direct image preserving a
lower cohomological bound for an arbitrary morphism of schemes. -/
@[stacks 08ED "bounded-below derived category"]
theorem exists_quasicoherentDerived_plus_lift (E : QuasicoherentDerivedCategory U)
    (hE : DerivedCategory.TStructure.t.plus E.obj) :
    ∃ F : QuasicoherentDerivedCategory X,
      DerivedCategory.TStructure.t.plus F.obj ∧
      Nonempty ((derivedPullback j.toLRSHom.toShHom).obj F.obj ≅ E.obj) := by
  obtain ⟨a, ha⟩ := (DerivedCategory.plus_iff E.obj).1 hE
  refine ⟨pushforwardLift j E, (DerivedCategory.plus_iff _).2
    ⟨a, fun n hn => isZero_homology_pushforwardLift_of_lt j E (a + 1)
      (fun m hm => ha m (by omega)) n (by omega)⟩,
    ⟨openDerivedPushforwardRestrictionIso j E.obj⟩⟩

/-- **Stacks Project, Tag 08ED.** A bounded-above quasi-coherent derived object on a
quasi-compact open subscheme of a quasi-compact scheme has a bounded-above quasi-coherent lift:
the functor `D⁻_QCoh(𝒪_X) ⟶ D⁻_QCoh(𝒪_U)` given by restriction is essentially surjective.

Quasi-compactness of the ambient scheme is what bounds the cohomological dimension of `j`, and
so bounds the shift by which the derived direct image can raise an upper bound. -/
@[stacks 08ED "bounded-above derived category"]
theorem exists_quasicoherentDerived_minus_lift [CompactSpace X]
    (E : QuasicoherentDerivedCategory U) (hE : DerivedCategory.TStructure.t.minus E.obj) :
    ∃ F : QuasicoherentDerivedCategory X,
      DerivedCategory.TStructure.t.minus F.obj ∧
      Nonempty ((derivedPullback j.toLRSHom.toShHom).obj F.obj ≅ E.obj) := by
  obtain ⟨N, hN⟩ := (DerivedCategory.minus_iff E.obj).1 hE
  have hELE : E.obj.IsLE (N - 1) :=
    (DerivedCategory.isLE_iff E.obj (N - 1)).2 fun n hn => hN n (by omega)
  obtain ⟨M, hRM⟩ :=
    exists_isZero_homology_derivedPushforward_openImmersion_of_isLE j E (N - 1) hELE
  refine ⟨pushforwardLift j E, (DerivedCategory.minus_iff _).2
    ⟨N - 1 + M - 1 + 1, fun n hn => hRM n (by omega)⟩,
    ⟨openDerivedPushforwardRestrictionIso j E.obj⟩⟩

/-- **Stacks Project, Tag 08ED.** A bounded quasi-coherent derived object on a quasi-compact
open subscheme of a quasi-compact scheme has a bounded quasi-coherent lift: the functor
`D^b_QCoh(𝒪_X) ⟶ D^b_QCoh(𝒪_U)` given by restriction is essentially surjective. -/
@[stacks 08ED "bounded derived category"]
theorem exists_quasicoherentDerived_bounded_lift [CompactSpace X]
    (E : QuasicoherentDerivedCategory U) (hE : DerivedCategory.TStructure.t.bounded E.obj) :
    ∃ F : QuasicoherentDerivedCategory X,
      DerivedCategory.TStructure.t.bounded F.obj ∧
      Nonempty ((derivedPullback j.toLRSHom.toShHom).obj F.obj ≅ E.obj) := by
  obtain ⟨N, hN⟩ := (DerivedCategory.bounded_iff E.obj).1 hE
  have habs : (0 : ℤ) ≤ |N| := abs_nonneg N
  have hNabs : N ≤ |N| := le_abs_self N
  have hGE := isZero_homology_pushforwardLift_of_lt j E (-|N| + 1) fun n hn => hN n (by
    rcases le_or_gt 0 n with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_neg h]
      omega)
  have hELE : E.obj.IsLE |N| :=
    (DerivedCategory.isLE_iff E.obj |N|).2 fun n hn => hN n (by
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ n)]
      omega)
  obtain ⟨M, hRM⟩ := exists_isZero_homology_derivedPushforward_openImmersion_of_isLE j E |N| hELE
  refine ⟨pushforwardLift j E, (DerivedCategory.bounded_iff _).2
    ⟨max |N| (|N| + M - 1 + 1), fun n hn => ?_⟩,
    ⟨openDerivedPushforwardRestrictionIso j E.obj⟩⟩
  rcases le_or_gt 0 n with h | h
  · rw [abs_of_nonneg h] at hn
    have := le_trans (le_max_right |N| (|N| + M - 1 + 1)) hn
    exact hRM n (by omega)
  · rw [abs_of_neg h] at hn
    have := le_trans (le_max_left |N| (|N| + M - 1 + 1)) hn
    exact hGE n (by omega)

end

end AlgebraicGeometry

end
