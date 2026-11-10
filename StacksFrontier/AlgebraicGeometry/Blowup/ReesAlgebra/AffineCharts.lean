module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowUp
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.RingTheory.Blowup.Basic
public import StacksFrontier.RingTheory.Blowup.Defs

/-!
# Affine charts of a blowup

Over an affine open `U` of the base, the blowup of `X` in a quasi-coherent ideal `I` is the
projective spectrum of the graded ring `⨁_{n ≥ 0} (I.ideal U)ⁿ` of local sections of the Rees
algebra. This file identifies the standard open of that spectrum attached to a section
`a ∈ I.ideal U` with the spectrum of the affine blowup algebra `Γ(X, U)[I/a]`, as a scheme over
`U`, and shows that those standard opens cover the part of the blowup lying over `U`.

## Main definitions

* `AlgebraicGeometry.reesDegreeOne` is a section of the ideal, viewed as a homogeneous element
  of degree one in the graded ring of local sections.
* `AlgebraicGeometry.reesToBase` is the ring map from that graded ring to the sections of the
  structure sheaf, given on each homogeneous piece by the affine identification with a power of
  the ideal.
* `AlgebraicGeometry.reesToAffineBlowupEquiv` identifies the degree-zero homogeneous
  localization away from `reesDegreeOne I U a` with the affine blowup algebra at `a`.
* `AlgebraicGeometry.affineBlowupStandardOpenIso` is the resulting affine chart isomorphism.

## Main results

* `Stacks.RelativeProj.Situation.relativeProjChart_isPullback` identifies the inverse image of
  an affine open of the base with the projective spectrum of the graded ring of sections there.
* `AlgebraicGeometry.affineBlowupStandardOpenIso_over`: the chart's structure morphism to the
  base is `Spec` of the canonical map from `Γ(X, U)` into its blowup algebra.
* `AlgebraicGeometry.affineBlowupStandardOpenIso_fraction`: on the chart at `a`, the
  degree-one section coming from `b` divided by the one coming from `a` is the generating
  fraction `b / a` of the blowup algebra.
* `AlgebraicGeometry.blownUpAffine_chart_cover`: these charts cover the inverse image of the
  affine open.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace DirectSum

universe u

add_to_stacks 0804 "canonical local projective-spectrum identification"
  Stacks.RelativeProj.Situation.relativeProjChart_isPullback

/-- An element of the ideal, viewed as a homogeneous element of degree one in
the local Rees algebra. -/
public noncomputable def reesDegreeOne {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : I.ideal U) :
    {f : (reesSituation I).sectionRing U.1 //
      f ∈ (reesSituation I).sectionRingGrading U.1 1} :=
  ⟨DirectSum.of ((reesSituation I).sectionPieces U.1) 1
      (((reesAlgebraData I).pieceEquiv 1 (by omega) U).symm
        ⟨(a : X.presheaf.obj (.op U.1)), by simp⟩),
    ⟨_, rfl⟩⟩

/-- The degree `n` part of the map from the graded ring of local sections of the Rees algebra to
the sections of the structure sheaf: the affine identification of the degree `n` piece with
`Iⁿ`, followed by the inclusion of `Iⁿ` into `Γ(X, U)`. -/
public noncomputable def reesToBaseComponent {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    (n : ℕ) → (reesSituation I).sectionPieces U.1 n →+
      X.presheaf.obj (.op U.1) := fun n => by
    change ((reesAlgebraData I).algebra.piece (n : ℤ)).val.obj
        (Opposite.op U.1) →+ X.presheaf.obj (.op U.1)
    exact {
      toFun := fun z => (reesAlgebraData I).pieceEquiv n (by omega) U z
      map_zero' := by simp
      map_add' := by
        intro x y
        have h := ((reesAlgebraData I).pieceEquiv n (by omega) U).map_add x y
        exact congrArg (fun z : ↥((I.ideal U) ^ n) =>
          (z : X.presheaf.obj (.op U.1))) h }

/-- The ring map from the graded ring of local sections of the Rees algebra over an affine open to
the sections of the structure sheaf there, given on each homogeneous piece by the affine
identification with a power of the ideal. -/
public noncomputable def reesToBase {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    (reesSituation I).sectionRing U.1 →+*
      X.presheaf.obj (.op U.1) := by
  let data := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I)
  let _ : DirectSum.GCommRing ((reesSituation I).sectionPieces U.1) :=
    data.gradedRing U.1
  let f : ∀ {n : ℕ}, (reesSituation I).sectionPieces U.1 n →+
      X.presheaf.obj (.op U.1) := fun {n} => reesToBaseComponent I U n
  refine DirectSum.liftRingHom ⟨f, ?_, ?_⟩
  · change f (n := 0)
      (GradedMonoid.GOne.one : (reesSituation I).sectionPieces U.1 0) = 1
    rw [data.one_homogeneous U.1]
    change ((reesAlgebraData I).pieceEquiv 0 (le_refl 0) U
      ((reesSituation I).algebra.one.eval (Opposite.op U.1)) :
        X.presheaf.obj (Opposite.op U.1)) = 1
    exact (reesAlgebraData I).pieceEquiv_one U
  · intro n m a b
    change f (GradedMonoid.GMul.mul a b) = f a * f b
    have hm := eq_of_heq (data.mul_homogeneous U.1 n m a b)
    rw [hm]
    change ((reesAlgebraData I).pieceEquiv (n + m) (by omega) U
        (((reesAlgebraData I).algebra.mul (n : ℤ) (m : ℤ)).app
          (Opposite.op U.1) a b) : X.presheaf.obj (Opposite.op U.1)) =
      ((reesAlgebraData I).pieceEquiv n (by omega) U a :
        X.presheaf.obj (Opposite.op U.1)) *
      ((reesAlgebraData I).pieceEquiv m (by omega) U b :
        X.presheaf.obj (Opposite.op U.1))
    exact (reesAlgebraData I).pieceEquiv_mul (n : ℤ) (m : ℤ)
      (by omega) (by omega) U a b

/-- The affine blowup algebra of `J` at `a`, computed inside the localization away from `a`, is the
affine blowup subalgebra generated by the fractions `x / a` for `x ∈ J`. -/
public lemma affineBlowupAlgebra_eq_basicBlowup {R : Type*} [CommRing R]
    (J : Ideal R) (a : R) :
    affineBlowupAlgebra J a (Localization.Away a) =
      affineBlowup J a := by
  unfold affineBlowupAlgebra affineBlowup
  congr 1
  ext z
  simp only [affineBlowupGenSet, Set.mem_image]
  rw [Localization.mk_eq_mk']
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, hxz.symm⟩

/-- The map to the base sends the degree-one element coming from `a` to `a`. -/
public lemma reesToBase_degreeOne {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (a : I.ideal U) :
    reesToBase I U (reesDegreeOne I U a).1 =
      (a : X.presheaf.obj (.op U.1)) := by
  let data := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I)
  let := data.gradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  rw [reesToBase, DirectSum.liftRingHom_apply]
  dsimp only [reesDegreeOne]
  simp only [DirectSum.toSemiring_of]
  change ((reesAlgebraData I).pieceEquiv 1 (by omega) U
    (((reesAlgebraData I).pieceEquiv 1 (by omega) U).symm
      ⟨(a : X.presheaf.obj (.op U.1)), by simp⟩) :
        X.presheaf.obj (.op U.1)) = (a : X.presheaf.obj (.op U.1))
  exact congrArg Subtype.val <|
    (reesAlgebraData I).pieceEquiv 1 (by omega) U |>.apply_symm_apply _

/-- The map to the base on a homogeneous element in the image of the degree `n` inclusion is the
affine identification of the degree `n` piece with `Iⁿ`. -/
public lemma reesToBase_of {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ)
    (x : (reesSituation I).sectionPieces U.1 n) :
    reesToBase I U (DirectSum.of ((reesSituation I).sectionPieces U.1)
      n x) =
      ((reesAlgebraData I).pieceEquiv n (by omega) U x :
        X.presheaf.obj (.op U.1)) := by
  let data := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I)
  let := data.gradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  rw [reesToBase, DirectSum.liftRingHom_apply, DirectSum.toSemiring_of]
  rfl

/-- Every element of the `n`-th power of the ideal is the image of a homogeneous element of degree
`n`. -/
private lemma exists_mem_sectionRingGrading_reesToBase_eq {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ)
    (x : X.presheaf.obj (.op U.1)) (hx : x ∈ I.ideal U ^ n) :
    ∃ y ∈ (reesSituation I).sectionRingGrading U.1 n,
      reesToBase I U y = x := by
  let e := (reesAlgebraData I).pieceEquiv n (by omega) U
  refine ⟨DirectSum.of ((reesSituation I).sectionPieces U.1) n
    (e.symm ⟨x, hx⟩), ⟨_, rfl⟩, ?_⟩
  rw [reesToBase_of]
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)

/-- The map to the base sends a homogeneous element of degree `n` into the `n`-th power of the
ideal. -/
public lemma reesToBase_mem_pow {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) (n : ℕ) (x : (reesSituation I).sectionRing U.1)
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 n) :
    reesToBase I U x ∈ (I.ideal U) ^ n := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  change x ∈ Set.range (DirectSum.of (s.sectionPieces U.1) n) at hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy, reesToBase_of]
  exact ((reesAlgebraData I).pieceEquiv n (by omega) U y).property

/-- The map to the base is injective on each homogeneous piece. -/
public lemma reesToBase_injective_on_grade {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ)
    (x : (reesSituation I).sectionRing U.1)
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 n)
    (h0 : reesToBase I U x = 0) : x = 0 := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  change x ∈ Set.range (DirectSum.of (s.sectionPieces U.1) n) at hx
  obtain ⟨y, rfl⟩ := hx
  rw [reesToBase_of] at h0
  have hy0 : y = 0 := ((reesAlgebraData I).pieceEquiv n (by omega) U).injective
    ((Subtype.ext h0).trans (map_zero _).symm)
  simp [hy0]

/-- The ring map from the degree-zero homogeneous localization of the local Rees algebra away
from the degree-one element of `a` to the localization of `Γ(X, U)` away from `a`. -/
@[irreducible] public noncomputable def reesToLocalization {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    HomogeneousLocalization.Away
      ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1 →+*
      Localization.Away (a : X.presheaf.obj (.op U.1)) := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  let f := (reesDegreeOne I U a).1
  let φ := (algebraMap (X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1)))).comp (reesToBase I U)
  have hφ : φ f = algebraMap (X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1))) a := by
    change algebraMap _ _ (reesToBase I U (reesDegreeOne I U a).1) = _
    rw [reesToBase_degreeOne]
  have hmul : algebraMap (X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1))) a *
      IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)) = 1 :=
    IsLocalization.Away.mul_invSelf (R := X.presheaf.obj (.op U.1))
      (S := Localization.Away (a : X.presheaf.obj (.op U.1))) a
  have hunit : IsUnit (φ f) := isUnit_iff_exists_inv.mpr
    ⟨IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)), by rw [hφ]; exact hmul⟩
  let lift : Localization.Away f →+*
      Localization.Away (a : X.presheaf.obj (.op U.1)) :=
    IsLocalization.Away.lift (R := (reesSituation I).sectionRing U.1)
      (S := Localization.Away f) (P := Localization.Away (a : X.presheaf.obj (.op U.1)))
      f (g := φ) hunit
  exact lift.comp (algebraMap
    (HomogeneousLocalization.Away (s.sectionRingGrading U.1) f)
    (Localization.Away f))

/-- That map sends the homogeneous fraction `x / fⁿ` to `reesToBase x / aⁿ`. -/
public lemma reesToLocalization_mk {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)
    (n : ℕ) (x : (reesSituation I).sectionRing U.1)
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 (n • 1)) :
    reesToLocalization I U a
      (HomogeneousLocalization.Away.mk
        ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).2 n x hx) =
      Localization.mk (reesToBase I U x)
        (⟨(a : X.presheaf.obj (.op U.1)) ^ n, n, rfl⟩ :
          Submonoid.powers (a : X.presheaf.obj (.op U.1))) := by
  let data := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I)
  let := data.gradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  let φ := (algebraMap (X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1)))).comp (reesToBase I U)
  have hφ : φ (reesDegreeOne I U a).1 =
      algebraMap (X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1))) a := by
    change algebraMap _ _ (reesToBase I U (reesDegreeOne I U a).1) = _
    rw [reesToBase_degreeOne]
  have hmul : algebraMap (X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1))) a *
      IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)) = 1 :=
    IsLocalization.Away.mul_invSelf (R := X.presheaf.obj (.op U.1))
      (S := Localization.Away (a : X.presheaf.obj (.op U.1))) a
  have hunit : IsUnit (φ (reesDegreeOne I U a).1) := isUnit_iff_exists_inv.mpr
    ⟨IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)), by rw [hφ]; exact hmul⟩
  unfold reesToLocalization
  change Localization.awayLift φ (reesDegreeOne I U a).1 hunit
      (Localization.mk x ⟨(reesDegreeOne I U a).1 ^ n, n, rfl⟩) = _
  rw [Localization.awayLift_mk φ (reesDegreeOne I U a).1 x
    (IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)))
    (by rw [hφ]; exact hmul) n]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  have hpow : IsLocalization.Away.invSelf (a : X.presheaf.obj (.op U.1)) ^ n =
      IsLocalization.mk' (Localization.Away (a : X.presheaf.obj (.op U.1))) 1
        (⟨(a : X.presheaf.obj (.op U.1)) ^ n,
          ⟨n, rfl⟩⟩ : Submonoid.powers (a : X.presheaf.obj (.op U.1))) := by
    rw [IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow]
    (congr 1; simp)
  rw [← hpow]
  rfl

/-- The ring map from the degree-zero homogeneous localization of the local Rees algebra away from
the degree-one element of `a` to the affine blowup algebra of `I.ideal U` at `a`: the map to the
localization lands in the blowup subalgebra. -/
public noncomputable def reesToAffineBlowup {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    HomogeneousLocalization.Away
      ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1 →+*
      affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1))) := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  let φ := reesToLocalization I U a
  refine φ.codRestrict _ ?_
  intro z
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (s.sectionRingGrading U.1) (reesDegreeOne I U a).2 z
  have hx' : x ∈ s.sectionRingGrading U.1 (n • 1) := hx
  rw [reesToLocalization_mk I U a n x hx']
  rw [affineBlowupAlgebra_eq_basicBlowup]
  rw [affineBlowup_mem_iff (I.ideal U) (a : X.presheaf.obj (.op U.1)) a.property]
  exact ⟨n, reesToBase I U x, reesToBase_mem_pow I U n x (by simpa using hx'), rfl⟩

/-- The map to the affine blowup algebra is the map to the localization, followed by the inclusion
of the blowup subalgebra. -/
private lemma reesToAffineBlowup_val {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)
    : letI := (reesSituation I).sectionRingGradedRing U.1
      letI := (reesSituation I).sectionRingGradingGradedRing U.1
      ∀ z : HomogeneousLocalization.Away
      ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1,
      ((reesToAffineBlowup I U a z : affineBlowupAlgebra (I.ideal U)
      (a : X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1)))) :
      Localization.Away (a : X.presheaf.obj (.op U.1))) =
      reesToLocalization I U a z := by
  intro z
  rfl

/-- That map is injective. -/
public lemma reesToAffineBlowup_injective {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    Function.Injective (reesToAffineBlowup I U a) := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  let f := (reesDegreeOne I U a).1
  intro z w h
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (s.sectionRingGrading U.1) (reesDegreeOne I U a).2 z
  obtain ⟨m, y, hy, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (s.sectionRingGrading U.1) (reesDegreeOne I U a).2 w
  have hloc : reesToLocalization I U a
      (HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1)
        (reesDegreeOne I U a).2 n x hx) =
      reesToLocalization I U a
      (HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1)
        (reesDegreeOne I U a).2 m y hy) :=
    congrArg Subtype.val h
  rw [reesToLocalization_mk I U a n x hx,
    reesToLocalization_mk I U a m y hy] at hloc
  have hfrac : (Localization.mk (reesToBase I U x)
        (⟨(a : X.presheaf.obj (.op U.1)) ^ n,
          ⟨n, rfl⟩⟩ : Submonoid.powers (a : X.presheaf.obj (.op U.1))) :
          Localization.Away (a : X.presheaf.obj (.op U.1))) =
      Localization.mk (reesToBase I U y)
        (⟨(a : X.presheaf.obj (.op U.1)) ^ m,
          ⟨m, rfl⟩⟩ : Submonoid.powers (a : X.presheaf.obj (.op U.1))) := hloc
  obtain ⟨k, hk⟩ := (affineBlowup_repr_eq_iff
    (a : X.presheaf.obj (.op U.1)) n m
    (reesToBase I U x) (reesToBase I U y)).mp hfrac
  have hxg : x ∈ s.sectionRingGrading U.1 n := by simpa using hx
  have hyg : y ∈ s.sectionRingGrading U.1 m := by simpa using hy
  have hfpow : ∀ j, f ^ j ∈ s.sectionRingGrading U.1 j := fun j => by
    simpa using SetLike.pow_mem_graded j (reesDegreeOne I U a).2
  have h1 : f ^ m * x ∈ s.sectionRingGrading U.1 (m + n) :=
    SetLike.mul_mem_graded (hfpow m) hxg
  have h2 : f ^ n * y ∈ s.sectionRingGrading U.1 (m + n) := by
    simpa [Nat.add_comm] using SetLike.mul_mem_graded (hfpow n) hyg
  have hsub : f ^ m * x - f ^ n * y ∈ s.sectionRingGrading U.1 (m + n) :=
    (s.sectionRingGrading U.1 (m + n)).sub_mem h1 h2
  have ht : f ^ k * (f ^ m * x - f ^ n * y) ∈
      s.sectionRingGrading U.1 (k + (m + n)) := by
    simpa using SetLike.mul_mem_graded (hfpow k) hsub
  have hzero : reesToBase I U (f ^ k * (f ^ m * x - f ^ n * y)) = 0 := by
    simp only [map_mul, map_pow, map_sub]
    have hfbase : reesToBase I U f = (a : X.presheaf.obj (.op U.1)) :=
      reesToBase_degreeOne I U a
    simpa [hfbase] using hk
  have hprod : f ^ k * (f ^ m * x - f ^ n * y) = 0 :=
    reesToBase_injective_on_grade I U (k + (m + n)) _ ht hzero
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  change (Localization.mk x (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f) :
      Localization.Away f) =
    Localization.mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f)
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨(⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f), ?_⟩
  linear_combination hprod

/-- That map is surjective. -/
public lemma reesToAffineBlowup_surjective {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    Function.Surjective (reesToAffineBlowup I U a) := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  intro z
  have hz : z.1 ∈ affineBlowup (I.ideal U) (a : X.presheaf.obj (.op U.1)) := by
    rw [← affineBlowupAlgebra_eq_basicBlowup]
    exact z.2
  obtain ⟨n, x, hx, hval⟩ := (affineBlowup_mem_iff (I.ideal U)
    (a : X.presheaf.obj (.op U.1)) a.property z.1).mp hz
  obtain ⟨r, hr, hrx⟩ := exists_mem_sectionRingGrading_reesToBase_eq I U n x hx
  have hr' : r ∈ s.sectionRingGrading U.1 (n • 1) := by simpa using hr
  refine ⟨HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1)
    (reesDegreeOne I U a).2 n r hr', ?_⟩
  apply Subtype.ext
  change reesToLocalization I U a
    (HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1)
      (reesDegreeOne I U a).2 n r hr') = _
  rw [reesToLocalization_mk, hrx]
  exact hval.symm

/-- The standard affine chart of the Rees projective spectrum at `a` has coordinate ring the affine
blowup algebra of `I.ideal U` at `a`. -/
public noncomputable def reesToAffineBlowupEquiv {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    HomogeneousLocalization.Away
      ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1 ≃+*
      affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1))) := by
  let := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I) |>.gradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  exact RingEquiv.ofBijective (reesToAffineBlowup I U a)
    ⟨reesToAffineBlowup_injective I U a, reesToAffineBlowup_surjective I U a⟩

/-- The canonical map from the sections of the structure sheaf to the graded ring of homogeneous
local sections multiplies the unit section by the given function. -/
public lemma relativeProj_sectionRingBaseMap_apply
    (s : Stacks.RelativeProj.Situation.{u}) (U : s.base.Opens)
    (r : s.base.ringCatSheaf.obj.obj (Opposite.op U)) :
    s.sectionRingBaseMap U r = DirectSum.of (s.sectionPieces U) 0
      (r • s.algebra.one.eval (Opposite.op U)) := by
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U
  change data.baseMap U r = _
  exact data.baseMap_apply U r

/-- The map to the affine blowup algebra carries the degree-zero part of the structure-sheaf map to
the structure map of the blowup algebra. -/
private lemma reesToAffineBlowup_baseMap {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U)
    (r : X.presheaf.obj (.op U.1)) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    reesToAffineBlowup I U a
      (HomogeneousLocalization.fromZeroRingHom
        ((reesSituation I).sectionRingGrading U.1)
        (Submonoid.powers (reesDegreeOne I U a).1)
        (GradedRing.projZeroRingHom'
          ((reesSituation I).sectionRingGrading U.1)
          ((reesSituation I).sectionRingBaseMap U.1 r))) =
      algebraMap (X.presheaf.obj (.op U.1))
        (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
          (Localization.Away (a : X.presheaf.obj (.op U.1)))) r := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  let e := s.sectionRingBaseMap U.1 r
  have he : e ∈ s.sectionRingGrading U.1 0 := by
    change (reesSituation I).sectionRingBaseMap U.1 r ∈
      Set.range (DirectSum.of ((reesSituation I).sectionPieces U.1) 0)
    rw [relativeProj_sectionRingBaseMap_apply
      (reesSituation I) U.1 r]
    exact ⟨_, rfl⟩
  let e0 : s.sectionRingGrading U.1 0 := ⟨e, he⟩
  have he0' : e ∈ s.sectionRingGrading U.1 (0 • (1 : ℕ)) := by
    simpa only [zero_smul] using he
  have hp : GradedRing.projZeroRingHom' (s.sectionRingGrading U.1) e = e0 := by
    simpa [e0] using
      (GradedRing.projZeroRingHom'_apply_coe (s.sectionRingGrading U.1) e0)
  apply Subtype.ext
  rw [reesToAffineBlowup_val]
  change reesToLocalization I U a
      (HomogeneousLocalization.fromZeroRingHom
        (s.sectionRingGrading U.1)
        (Submonoid.powers (reesDegreeOne I U a).1)
        (GradedRing.projZeroRingHom' (s.sectionRingGrading U.1) e)) = _
  rw [hp]
  have hfrom : HomogeneousLocalization.fromZeroRingHom
      (s.sectionRingGrading U.1) (Submonoid.powers (reesDegreeOne I U a).1) e0 =
      HomogeneousLocalization.Away.mk (s.sectionRingGrading U.1)
        (reesDegreeOne I U a).2 0 e he0' :=
    rfl
  rw [hfrom, reesToLocalization_mk I U a 0 e he0']
  let r' : X.ringCatSheaf.obj.obj (Opposite.op U.1) := r
  have hbase : reesToBase I U e = r := by
    change reesToBase I U
      ((reesSituation I).sectionRingBaseMap U.1 r') = r
    let P := (reesAlgebraData I).algebra.piece 0
    let M := P.val.obj (Opposite.op U.1)
    let : Module (X.ringCatSheaf.obj.obj
      (Opposite.op U.1)) M := M.isModule
    rw [relativeProj_sectionRingBaseMap_apply
      (reesSituation I) U.1 r', reesToBase_of]
    change ((reesAlgebraData I).pieceEquiv (0 : ℤ) (by omega) U
      (r' • (reesAlgebraData I).algebra.one.eval (Opposite.op U.1)) :
      X.presheaf.obj (.op U.1)) = r
    rw [(reesAlgebraData I).pieceEquiv_smul,
      (reesAlgebraData I).pieceEquiv_one]
    simp [r']
  rw [hbase]
  simp only [pow_zero, Subalgebra.coe_algebraMap]
  rfl

/-- The standard affine chart of the Rees projective spectrum is canonically the
spectrum of the affine blowup algebra. -/
@[stacks 0804 "affine blowup algebra chart"]
public noncomputable def affineBlowupStandardOpenIso {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    Spec (.of <| affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
      (Localization.Away (a : X.presheaf.obj (.op U.1)))) ≅
      (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1).toScheme := by
  let s := reesSituation I
  let data := Stacks.RelativeProj.Situation.sectionRingStructure s
  let := data.gradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  exact Scheme.Spec.mapIso (reesToAffineBlowupEquiv I U a).toCommRingCatIso.op ≪≫
    (Proj.basicOpenIsoSpec (s.sectionRingGrading U.1) (reesDegreeOne I U a).1
      (reesDegreeOne I U a).2 Nat.zero_lt_one).symm

/-- The affine blowup chart is an isomorphism over the affine base: its structure
map is induced by the canonical inclusion of the ring into its blowup algebra. -/
@[stacks 0804 "affine blowup chart over the base"]
public theorem affineBlowupStandardOpenIso_over {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    (affineBlowupStandardOpenIso I U a).hom ≫
        (Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
          (reesDegreeOne I U a).1).ι ≫
        Stacks.RelativeProj.Situation.projInclusionToOpen (reesSituation I) U.1 U.2 =
    Spec.map (CommRingCat.ofHom
        (algebraMap (X.presheaf.obj (.op U.1))
          (affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
            (Localization.Away (a : X.presheaf.obj (.op U.1)))))) ≫
        U.2.isoSpec.inv := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  simp only [affineBlowupStandardOpenIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, Iso.symm_hom, Scheme.Spec_map, Category.assoc,
    Stacks.RelativeProj.Situation.projInclusionToOpen]
  rw [← Category.assoc (Proj.basicOpenIsoSpec _ _ _ _).inv,
    Proj.basicOpenIsoSpec_inv_ι, Proj.awayι_toSpecZero_assoc]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 1
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (reesToAffineBlowup_baseMap I U a)))

/-- On the standard chart at `a`, a degree-one section `b` divided by `a`
corresponds to the generating fraction `b/a` in the affine blowup algebra. -/
@[stacks 0804 "canonical affine blowup fractions"]
public theorem affineBlowupStandardOpenIso_fraction {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (a b : I.ideal U) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    (((Spec.preimage
      ((affineBlowupStandardOpenIso I U a).hom ≫
        (Proj.basicOpenIsoSpec
          ((reesSituation I).sectionRingGrading U.1)
          (reesDegreeOne I U a).1 (reesDegreeOne I U a).2 (by omega)).hom)).hom
      (HomogeneousLocalization.Away.mk
        ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).2 1 (reesDegreeOne I U b).1
        (by simp)) :
      affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1)))) :
      Localization.Away (a : X.presheaf.obj (.op U.1))) =
      IsLocalization.mk' (Localization.Away (a : X.presheaf.obj (.op U.1)))
        (b : X.presheaf.obj (.op U.1))
        ⟨(a : X.presheaf.obj (.op U.1)), Submonoid.mem_powers _⟩ := by
  let := Stacks.RelativeProj.Situation.sectionRingStructure
    (reesSituation I) |>.gradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  simp only [affineBlowupStandardOpenIso, Iso.trans_hom, Category.assoc,
    Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
  change (((Spec.preimage (Spec.map
      (reesToAffineBlowupEquiv I U a).toCommRingCatIso.hom)).hom
        (HomogeneousLocalization.Away.mk
          ((reesSituation I).sectionRingGrading U.1)
          (reesDegreeOne I U a).2 1 (reesDegreeOne I U b).1
          (by simp)) :
      affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1)))) :
      Localization.Away (a : X.presheaf.obj (.op U.1))) = _
  simp only [Spec.preimage_map, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom]
  delta reesToAffineBlowupEquiv
  change ((reesToAffineBlowup I U a
      (HomogeneousLocalization.Away.mk
        ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).2 1 (reesDegreeOne I U b).1
        (by simp)) :
      affineBlowupAlgebra (I.ideal U) (a : X.presheaf.obj (.op U.1))
        (Localization.Away (a : X.presheaf.obj (.op U.1)))) :
      Localization.Away (a : X.presheaf.obj (.op U.1))) = _
  delta reesToAffineBlowup
  simp only [RingHom.codRestrict_apply]
  change reesToLocalization I U a
      (HomogeneousLocalization.Away.mk
        ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).2 1 (reesDegreeOne I U b).1
        (by simp)) = _
  rw [reesToLocalization_mk, reesToBase_degreeOne, ← Localization.mk_eq_mk'_apply]
  congr 1
  apply Subtype.ext
  simp

/-- Every element of the `n`-th power of the ideal is the image of a homogeneous element of degree
`n`. -/
public lemma reesToBase_surjective_on_grade {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ)
    (x : X.presheaf.obj (.op U.1)) (hx : x ∈ I.ideal U ^ n) :
    ∃ y ∈ (reesSituation I).sectionRingGrading U.1 n,
      reesToBase I U y = x := by
  exact exists_mem_sectionRingGrading_reesToBase_eq I U n x hx

/-- An ideal of the local Rees algebra containing every degree-one element contains every
homogeneous element of positive degree. -/
public lemma rees_homogeneous_mem_ideal {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens)
    (J : Ideal ((reesSituation I).sectionRing U.1))
    (hJ : ∀ a : I.ideal U, (reesDegreeOne I U a).1 ∈ J)
    (n : ℕ) (hn : 0 < n)
    (x : (reesSituation I).sectionRing U.1)
    (hx : x ∈ (reesSituation I).sectionRingGrading U.1 n) : x ∈ J := by
  let s := reesSituation I
  let := s.sectionRingGradedRing U.1
  let := s.sectionRingGradingGradedRing U.1
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hpow := reesToBase_mem_pow I U (n + 1) x hx
  rw [pow_succ'] at hpow
  have hlift : ∀ z ∈ I.ideal U * I.ideal U ^ n,
      ∃ y ∈ s.sectionRingGrading U.1 (n + 1), reesToBase I U y = z ∧ y ∈ J := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro a ha b hb
      obtain ⟨v, hv, he⟩ := reesToBase_surjective_on_grade I U n b hb
      refine ⟨(reesDegreeOne I U ⟨a, ha⟩).1 * v, ?_, ?_, ?_⟩
      · simpa [Nat.add_comm] using SetLike.mul_mem_graded (reesDegreeOne I U ⟨a, ha⟩).2 hv
      · rw [map_mul, reesToBase_degreeOne, he]
      · exact J.mul_mem_right v (hJ ⟨a, ha⟩)
    · intro a b ha hb
      obtain ⟨v, hv, he, hj⟩ := ha
      obtain ⟨w, hw, hf, hk⟩ := hb
      exact ⟨v + w, (s.sectionRingGrading U.1 (n + 1)).add_mem hv hw,
        by rw [map_add, he, hf], J.add_mem hj hk⟩
  obtain ⟨y, hy, he, hj⟩ := hlift _ hpow
  have hxy : x - y = 0 := reesToBase_injective_on_grade I U (n + 1) _
    ((s.sectionRingGrading U.1 (n + 1)).sub_mem hx hy) (by rw [map_sub, he, sub_self])
  exact sub_eq_zero.mp hxy ▸ hj

/-- Every point of the Rees projective spectrum lies on the standard chart of some element of the
ideal: its homogeneous prime cannot contain all the degree-one elements, since it does not
contain the irrelevant ideal. -/
private lemma exists_reesDegreeOne_not_mem {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens)
    (x : AlgebraicGeometry.Proj ((reesSituation I).sectionRingGrading U.1)) :
    ∃ a : I.ideal U, (reesDegreeOne I U a).1 ∉ x.asHomogeneousIdeal := by
  classical
  by_contra! h
  exact x.not_irrelevant_le <| (HomogeneousIdeal.irrelevant_le _).mpr
    (rees_homogeneous_mem_ideal I U x.asHomogeneousIdeal.toIdeal h)

/-- Degree-one Rees elements give an affine open cover of the inverse image of
an affine open under the blowup morphism. -/
@[stacks 0804 "affine chart covering"]
public theorem blownUpAffine_chart_cover {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.affineOpens) :
    letI := (reesSituation I).sectionRingGradedRing U.1
    letI := (reesSituation I).sectionRingGradingGradedRing U.1
    (⋃ a : I.ideal U,
      Set.range ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
        (reesDegreeOne I U a).1).ι ≫
        Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U)) =
      (blowUpToBase I ⁻¹ᵁ U.1).1 := by
  let := (reesSituation I).sectionRingGradedRing U.1
  let := (reesSituation I).sectionRingGradingGradedRing U.1
  have hp := Stacks.RelativeProj.Situation.relativeProjChart_isPullback (reesSituation I) U
  ext x
  constructor
  · intro hx
    obtain ⟨a, y, rfl⟩ := Set.mem_iUnion.mp hx
    have he := congrArg (fun f => f ((Proj.basicOpen
      ((reesSituation I).sectionRingGrading U.1)
      (reesDegreeOne I U a).1).ι y)) hp.w
    change blowUpToBase I
      (Stacks.RelativeProj.Situation.relativeProjChart (reesSituation I) U
        ((Proj.basicOpen ((reesSituation I).sectionRingGrading U.1)
          (reesDegreeOne I U a).1).ι y)) ∈ U.1
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at he
    rw [he]
    exact (Stacks.RelativeProj.Situation.projInclusionToOpen (reesSituation I) U.1 U.2 _).property
  · intro hx
    obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback hp x
      ⟨blowUpToBase I x, hx⟩ rfl
    obtain ⟨a, ha⟩ := exists_reesDegreeOne_not_mem I U y
    exact Set.mem_iUnion.mpr ⟨a, ⟨y, (Proj.mem_basicOpen _ _ _).mpr ha⟩, hy⟩

end AlgebraicGeometry

end
