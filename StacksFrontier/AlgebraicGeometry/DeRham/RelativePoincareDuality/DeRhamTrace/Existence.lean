module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.ExistenceGraded
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamPerfect
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TruncationPairingInduction
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceExistence

/-!
# Existence of the trace of relative Poincaré duality for de Rham cohomology

The induction over the stupid truncations of the proof of [Stacks, Tag 0G8K], starting from the
perfect pairings of [Stacks, Tag 0G8I] on the graded pieces.

## References

* [Stacks Project, Tag 0G8K](https://stacks.math.columbia.edu/tag/0G8K)
* [Stacks Project, Tag 0G8I](https://stacks.math.columbia.edu/tag/0G8I)
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

/-- The derived tensor product over `𝒪_S` is additive in its first variable. -/
instance additive_derivedTensorProductFunctor_flip_obj_base
    (Y : DerivedModules.{u + 1, u} D.S.toRingedSpace.sheaf) :
    ((derivedTensorProductFunctor D.S.toRingedSpace.sheaf).flip.obj Y).Additive := by
  let := (canonicalDerivedTensorProduct D.S.toRingedSpace.sheaf).commShift_left Y
  have := (canonicalDerivedTensorProduct D.S.toRingedSpace.sheaf).exact_left Y
  infer_instance

/-- **Existence in [Stacks, Tag 0G8K]**: if `t : Rf_*(Ω^•[2n]) ⟶ 𝒪_S` restricts on the top piece
to the trace `Rf_*Ω^n[n] ≅ Rf_*ω^•_{X/S} ⟶ 𝒪_S` of [Stacks, Tag 0G8I], then the pairing
`Rf_*Ω^• ⊗^L Rf_*(Ω^•[2n]) ⟶ 𝒪_S`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, is a perfect pairing of perfect
complexes. -/
theorem isDeRhamPoincareTrace_of_topInclusion_comp
    (ψ : (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj)
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : D.topInclusion ≫ s = (Stacks.Duality.derivedPushforward D.f).map ψ.hom ≫
      (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0))) :
    D.IsDeRhamPoincareTrace s := by
  have hP :=
    AlgebraicGeometry.ProperSmoothDeRham.isPerfect_derivedPushforward_deRhamComplex D.f
  refine (D.isDeRhamPoincareTrace_iff s).2 ⟨hP, ?_, ?_⟩
  · let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
      (inverseImageBaseProjection D.f)
    exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (((derivedPushforward (inverseImageBaseProjection D.f)).commShiftIso (2 * D.n : ℤ)).app
        (Scheme.deRhamDerived D.f)).symm
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift hP _)
  · let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    let := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
      (inverseImageBaseProjection D.f)
    have := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
      (inverseImageBaseProjection D.f)
    have : (derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).Additive :=
      inferInstance
    have : (shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf) (2 * D.n : ℤ) ⋙
        derivedPushforward.{u, u + 1, u + 1} (inverseImageBaseProjection D.f)).Additive :=
      ⟨fun {_ _ a b} => (congrArg (derivedPushforward (inverseImageBaseProjection D.f)).map
        ((shiftFunctor (DerivedModules.{u + 1, u} (inverseImageBase D.f).sheaf)
          (2 * D.n : ℤ)).map_add (f := a) (g := b))).trans
        ((derivedPushforward (inverseImageBaseProjection D.f)).map_add)⟩
    exact (@StacksDraft.StupidTruncation.allPerf_toTensor_of_graded (inverseImageBase D.f) _ _ _ _ _
      (SheafOfModules.multiplicationInt
        (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
          (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
      _ (D.isZero_deRhamCx_extend_X) _ _ _ _ _ _ _ ‹_› (D.f.deRhamPushData (2 * D.n)) _ s
      (by omega) (fun k hk => HomologicalComplex.isZero_extend_X _ _ k (fun i => by simp; omega))
      (D.isZero_deRhamCx_extend_X)
      (fun k hk => HomologicalComplex.isZero_extend_X _ _ k (fun i => by simp; omega))
      (D.isZero_deRhamCx_extend_X)
      (fun p q hpq hp hq => D.allPerf_gradedMul ψ s hs p q hpq hp hq)).perf



end AlgebraicGeometry.RelativeDualitySituation

end
