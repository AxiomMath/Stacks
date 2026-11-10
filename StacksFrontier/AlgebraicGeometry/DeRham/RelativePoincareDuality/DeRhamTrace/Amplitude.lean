module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionStalkVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.StalkVanishingCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceVanishing
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationBounds
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated

/-!
# Amplitude of the derived direct images of relative differential forms

For `f : X ⟶ S` proper with fibres of dimension `n`, `R^qf_*Ω^p_{X/S} = 0` for `q > n`
([Stacks, Tag 0E7D]); hence `Rf_*Ω^n_{X/S}[n]` and, by the stupid filtration,
`Rf_*(Ω^•_{X/S}[2n])` live in degrees `≤ 0`.

## Main results

* `AlgebraicGeometry.RelativeDualitySituation.isLE_derivedPushforward_formsInDegreeZero`:
  `Rf_*Ω^p_{X/S}` lies in degrees `≤ n`.
* `AlgebraicGeometry.RelativeDualitySituation.isLE_derivedPushforward_formsTop`:
  `Rf_*(Ω^n_{X/S}[n])` lies in degrees `≤ 0`.
* `AlgebraicGeometry.RelativeDualitySituation.isLE_deRhamDirectImageTop`:
  `Rf_*(Ω^•_{X/S}[2n])` lies in degrees `≤ 0`.

## Implementation notes

The vanishing of `R^qf_*Ω^p_{X/S}` is checked on stalks, where it is part (1) of
[Stacks, Tag 0E7D] for the fibres, all of dimension `n`. For the de Rham complex, whose terms
`Ω^p_{X/S}` sit in degrees `0 ≤ p ≤ n`, the bound `Rf_*Ω^p_{X/S}[-p] ∈ D^{≤ n + p} ⊆ D^{≤ 2n}`
on each term gives the bound on the complex by induction along its stupid filtration
(`StacksDraft.ExtremalDegrees.isLE_map_Q_of_terms`); `Ω^p_{X/S}` read as an `f⁻¹𝒪_S`-module has
the same derived direct image (`AlgebraicGeometry.Scheme.Hom.formsDirectImageIso`).

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Stacks.StandardDerivedModel
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)
open Stacks.DerivedTensor.RingedSite (DerivedModules derivedTensorProductFunctor
  canonicalDerivedTensorProduct)
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection)

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- `R^qf_*Ω^p_{X/S} = 0` for `q > n` ([Stacks, Tag 0E7D]), in the form of the right derived
functors of `f_*`. -/
theorem isZero_rightDerivedPlus_relativeDifferentialForms (p i : ℤ) (hi : (D.n : ℤ) < i) :
    IsZero (((Scheme.Modules.pushforward D.f).rightDerivedPlus i).obj
      (Scheme.Hom.relativeDifferentialForms D.f p)) := by
  have : (Scheme.Hom.relativeDifferentialForms D.f p).IsQuasicoherent := by
    rcases lt_or_ge p 0 with hp | hp
    · exact (SheafOfModules.isQuasicoherent _).prop_of_isZero
        (Stacks.DeRhamSmooth.isZero_relativeDifferentialForms_of_neg D.f p hp)
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hp
      exact Scheme.Hom.isQuasicoherent_relativeDifferentialForms D.f m
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
  exact isZero_stalk_rightDerivedPlus_of_topologicalKrullDim_fiber_le
    D.f y D.n (D.relativeDimension y (D.fiber_nonempty y)).2.le _ i hi

/-- `R^qf_*Ω^p_{X/S} = 0` for `q > n`: `Rf_*Ω^p_{X/S}` lies in degrees `≤ n`
([Stacks, Tag 0E7D]). -/
theorem isLE_derivedPushforward_formsInDegreeZero (p : ℤ) :
    ((Stacks.Duality.derivedPushforward D.f).obj (D.f.formsInDegreeZero p)).IsLE D.n := by
  have h := Stacks.AlgebraicGeometry.TopDegreeBaseChange.isLE_derivedPushforward_singleFunctor
    D.f.toLRSHom.toShHom (Scheme.Hom.relativeDifferentialForms D.f p) D.n
    (D.isZero_rightDerivedPlus_relativeDifferentialForms p)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    ((derivedPushforward D.f.toLRSHom.toShHom).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _)) _

/-- `Ω^p_{X/S} = 0` for `p > n`, as a term of the de Rham complex. -/
theorem isZero_deRhamCx_X_of_lt (p : ℕ) (hp : D.n < p) : IsZero (D.deRhamCx.X p) :=
  (SheafOfModules.restrictScalars _).map_isZero
    (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension D.f D.n p hp)

/-- The de Rham complex `Ω^•_{X/S}`, extended by zero to a `ℤ`-indexed complex, has its nonzero
terms in degrees `0, …, n`. -/
theorem exists_eq_of_not_isZero_deRhamCx_extend_X (i : ℤ)
    (h : ¬ IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X i)) :
    ∃ p : ℕ, p ≤ D.n ∧ (p : ℤ) = i := by
  by_cases hi : 0 ≤ i
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    refine ⟨p, ?_, rfl⟩
    by_contra hp
    exact h ((D.isZero_deRhamCx_X_of_lt p (by omega)).of_iso
      (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (by simp)))
  · exact absurd (D.deRhamCx.isZero_extend_X ComplexShape.embeddingUpNat i
      (fun p hp => by simp at hp; omega)) h

/-- A functor commuting with shifts sends `K⟦n⟧` to degrees `≤ 0` when `F K` lies in degrees
`≤ n`. -/
private theorem isLE_obj_shift_of_isLE {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
    (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ] (K : DerivedCategory A) (n : ℤ)
    (h : (F.obj K).IsLE n) : (F.obj (K⟦n⟧)).IsLE 0 :=
  have : ((F ⋙ shiftFunctor _ n).obj K).IsLE 0 :=
    DerivedCategory.TStructure.t.isLE_shift (F.obj K) n n 0 (by omega)
  DerivedCategory.TStructure.t.isLE_of_iso ((F.commShiftIso n).app K).symm 0

/-- `Rf_*(Ω^•_{X/S}[2n])` lies in degrees `≤ 0`. -/
theorem isLE_deRhamDirectImageTop : D.deRhamDirectImageTop.IsLE 0 := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    (inverseImageBaseProjection D.f)
  have := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    (inverseImageBaseProjection D.f)
  have hK : {i : ℤ | ¬ IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X i)}.Finite :=
    (Set.finite_Icc (0 : ℤ) D.n).subset fun i hi => by
      obtain ⟨p, hp, rfl⟩ := D.exists_eq_of_not_isZero_deRhamCx_extend_X i hi
      exact ⟨by omega, by omega⟩
  have hterm : ∀ i : ℤ, ¬ IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X i) →
      ((derivedPushforward (inverseImageBaseProjection D.f)).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X i))).IsLE (2 * D.n - i) := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := D.exists_eq_of_not_isZero_deRhamCx_extend_X i hi
    have h := D.isLE_derivedPushforward_formsInDegreeZero p
    have h' : DerivedCategory.TStructure.t.IsLE
        ((derivedPushforward D.f.toLRSHom.toShHom).obj (D.f.formsInDegreeZero p)) (2 * D.n - p) :=
      DerivedCategory.TStructure.t.isLE_of_le
        ((Stacks.Duality.derivedPushforward D.f).obj (D.f.formsInDegreeZero p)) D.n (2 * D.n - p)
        (by omega)
    exact DerivedCategory.TStructure.t.isLE_of_iso
      (D.f.formsDirectImageIso p ≪≫ (derivedPushforward (inverseImageBaseProjection D.f)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (by simp)).symm)) _
  have h := StacksDraft.ExtremalDegrees.isLE_map_Q_of_terms
    (derivedPushforward (inverseImageBaseProjection D.f))
    (D.deRhamCx.extend ComplexShape.embeddingUpNat) hK (2 * D.n) hterm
  exact isLE_obj_shift_of_isLE _ _ _ h

/-- `Rf_*(Ω^n_{X/S}[n])` lies in degrees `≤ 0`. -/
theorem isLE_derivedPushforward_formsTop :
    ((Stacks.Duality.derivedPushforward D.f).obj
      ((D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧)).IsLE 0 := by
  let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    D.f.toLRSHom.toShHom
  exact isLE_obj_shift_of_isLE _ _ _ (D.isLE_derivedPushforward_formsInDegreeZero D.n)

end AlgebraicGeometry.RelativeDualitySituation

end
