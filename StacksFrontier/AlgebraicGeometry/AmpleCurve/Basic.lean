module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.AlgebraicGeometry.Ample.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree

/-!
# Ampleness and degree on a proper curve

Let `X` be a proper curve over a field. Then `X` is not affine, so every affine open subset of
`X` is a proper subset; in particular a global section of an invertible sheaf on `X` whose
nonvanishing locus is affine vanishes somewhere. Given that the degree is additive in the tensor
product of invertible sheaves (Tag 0AYX) and that an invertible sheaf with a global section
vanishing somewhere but not everywhere has positive degree (Tag 0B40), it follows that an ample
invertible sheaf on `X` has positive degree: the "only if" direction of Tag 0B5X.

## Main results

* `AlgebraicGeometry.isAffine_of_isAffineOpen_top`: a scheme whose top open is an affine open is
  affine.
* `AlgebraicGeometry.IsAffineOpen.ne_top_of_not_isAffine`: on a scheme that is not affine, an
  affine open is a proper subset.
* `AlgebraicGeometry.topologicalKrullDim_eq_zero_of_isAffine`: an affine variety that is proper
  over a field has Krull dimension zero.
* `AlgebraicGeometry.not_isAffine_of_isCurve`: a proper curve over a field is not affine.
* `AlgebraicGeometry.IsAffineOpen.ne_top_of_isCurve`: on a proper curve over a field, an affine
  open is a proper subset.
* `AlgebraicGeometry.invertibleCurveDegree_unit_eq_zero`: the structure sheaf has degree zero.
* `AlgebraicGeometry.invertibleCurveDegree_tensorPower_eq_mul`: `deg 𝓛^{⊗ n} = n · deg 𝓛` for
  every integer `n`, given additivity of the degree in the tensor product of invertible sheaves.
* `AlgebraicGeometry.invertibleCurveDegree_pos_of_isAmple`: an ample invertible sheaf on a
  proper curve has positive degree, given the degree of its tensor powers and positivity of the
  degree of an invertible sheaf with a section vanishing somewhere but not everywhere.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules (nonvanishingLocus)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible tensorPowerSuccIso
  tensorPowerReindex tensorProduct_isInvertible)

universe u

namespace AlgebraicGeometry

/-- A scheme is affine as soon as its top open subset is an affine open. -/
public theorem isAffine_of_isAffineOpen_top (X : Scheme.{u})
    (h : IsAffineOpen (⊤ : X.Opens)) : IsAffine X :=
  have : IsAffine ↑(⊤ : X.Opens) := h
  IsAffine.of_isIso X.topIso.inv

/-- On a scheme that is not affine, an affine open subset is a proper subset. -/
public theorem IsAffineOpen.ne_top_of_not_isAffine {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (hX : ¬ IsAffine X) : U ≠ ⊤ :=
  fun h => hX (isAffine_of_isAffineOpen_top X (h ▸ hU))

/-- An affine variety that is proper over a field has topological Krull dimension zero. -/
public theorem topologicalKrullDim_eq_zero_of_isAffine (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsVariety k f] [IsAffine X] :
    topologicalKrullDim X = 0 := by
  have hfield : IsField Γ(X, ⊤) := isField_of_universallyClosed k f
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso X.isoSpec).isHomeomorph,
    show topologicalKrullDim ↥(Spec Γ(X, ⊤)) = topologicalKrullDim (PrimeSpectrum Γ(X, ⊤)) from
      rfl,
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact ringKrullDim_eq_zero_of_isField hfield

/-- A proper curve over a field is not affine. -/
public theorem not_isAffine_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] : ¬ IsAffine X := by
  intro hX
  simpa [IsCurve.topologicalKrullDim_eq_one f] using topologicalKrullDim_eq_zero_of_isAffine k f

/-- On a proper curve over a field, an affine open subset is a proper subset. -/
public theorem IsAffineOpen.ne_top_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] {U : X.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ :=
  hU.ne_top_of_not_isAffine (not_isAffine_of_isCurve k f)

/-- The structure sheaf of a proper scheme of dimension at most one over a field has degree
zero. -/
public theorem invertibleCurveDegree_unit_eq_zero (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) :
    @invertibleCurveDegree k _ X f _ hdim (SheafOfModules.unit X.ringCatSheaf)
      (Scheme.Modules.isInvertible_unit X) = 0 :=
  sub_self _

/-- **The degree of a tensor power**: `deg 𝓛^{⊗ n} = n · deg 𝓛` for every integer `n`, given
as the hypothesis `hadd` that `deg(𝓜 ⊗ 𝓝) = deg 𝓜 + deg 𝓝` for all invertible `𝓜` and `𝓝`
(the invertible case of Tag 0AYX). -/
public theorem invertibleCurveDegree_tensorPower_eq_mul (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hadd : ∀ (M N : X.Modules)
        (hM : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property M)
        (hN : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property N)
        (hMN : SheafOfModules.IsInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
            Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf
              (forget₂ CommRingCat RingCat) (structureSheafRing X.toRingedSpace).property⟩).obj
            M).obj N)),
        @invertibleCurveDegree k _ X f _ hdim
            (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.toRingedSpace.presheaf,
              Presheaf.isSheaf_of_isSheaf_comp _ X.toRingedSpace.presheaf
                (forget₂ CommRingCat RingCat) (structureSheafRing X.toRingedSpace).property⟩).obj
              M).obj N) hMN =
          @invertibleCurveDegree k _ X f _ hdim M hM +
            @invertibleCurveDegree k _ X f _ hdim N hN)
    (n : ℤ) :
    @invertibleCurveDegree k _ X f _ hdim
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n)
        (tensorPower_isInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n) =
      n * invertibleCurveDegree k f hdim L := by
  have step : ∀ a b : ℤ, a + 1 = b →
      @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L b)
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L b) =
        @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L a)
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L a) +
        invertibleCurveDegree k f hdim L := by
    intro a b hab
    have hM := tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L a
    have hMN := @tensorProduct_isInvertible _ _ _ X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property _ _ _ L hM ‹_›
    have key := @invertibleCurveDegree_eq_of_iso k _ X f _ hdim _ _ hMN
      (tensorPower_isInvertible X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L b)
      (tensorPowerSuccIso X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L a ≪≫
        tensorPowerReindex X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L hab)
    rw [← key, hadd _ _ hM ‹_› hMN]
  induction n using Int.induction_on with
  | zero => exact (invertibleCurveDegree_unit_eq_zero k f hdim).trans (zero_mul _).symm
  | succ m ih =>
      rw [step m _ rfl, ih]
      ring
  | pred m ih =>
      have h1 := step (-(m : ℤ) - 1) (-(m : ℤ)) (by ring)
      rw [ih] at h1
      linarith

/-- An ample invertible sheaf `𝓛` on a proper curve over a field has positive degree (the "only
if" direction of Tag 0B5X), given as hypotheses that `deg 𝓛^{⊗ n} = n · deg 𝓛` for every natural
number `n` (`hmul`, the invertible case of Tag 0AYX), and that for `n ≥ 1` the sheaf `𝓛^{⊗ n}`
has positive degree whenever it has a global section vanishing somewhere but not everywhere
(`hpos`, which follows from Tag 0B40). -/
public theorem invertibleCurveDegree_pos_of_isAmple (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L]
    (hmul : ∀ n : ℕ, @invertibleCurveDegree k _ X f _ hdim
        (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ))
        (tensorPower_isInvertible X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ))
        = (n : ℤ) * invertibleCurveDegree k f hdim L)
    (hpos : ∀ n : ℕ, 1 ≤ n → ∀ s : (tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L (n : ℤ)).sections,
        (∃ x : X, x ∈ nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s) →
        nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ →
        0 < @invertibleCurveDegree k _ X f _ hdim
          (tensorPower X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ))
          (tensorPower_isInvertible X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L (n : ℤ)))
    (hL : Scheme.Modules.IsAmple X L) :
    0 < invertibleCurveDegree k f hdim L := by
  obtain ⟨-, hpt⟩ := hL
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨n, hn, s, hxs, haff⟩ := hpt x
  have hne := haff.ne_top_of_isCurve k f
  have hloc : nonvanishingLocus (X := X.toLocallyRingedSpace.toRingedSpace)
      (tensorPower X.toRingedSpace.presheaf
        (structureSheafRing X.toRingedSpace).property L (n : ℤ)) s ≠ Set.univ := fun h =>
    hne (TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_top.symm))
  have h1 := hpos n hn s ⟨x, hxs⟩ hloc
  rw [hmul n] at h1
  rcases mul_pos_iff.mp h1 with ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · lia

end AlgebraicGeometry

end
