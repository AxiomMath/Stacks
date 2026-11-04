module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TruncationPairingInduction
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceExistence
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedShiftClass
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedToTensorShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedPushforwardCompShift
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTopPiece
public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.DeRhamTrace.GradedTargetIdentification

/-!
# The graded pieces of the de Rham pairing are perfect at every shift

In the proof of [Stacks, Tag 0G8K] the induction over the stupid truncations starts from the
pairings `Ω^p[-p] ⊗^L Ω^q[-q] ⟶ Ω^•` (`p + q = n`) of the graded pieces of the de Rham complex,
pushed down to `S`. Through the trace they are the pairings of [Stacks, Tag 0G8I], read in the
derived category of `f⁻¹𝒪_S`-modules, and they are perfect at every shift by
[Stacks, Tag 0G81].

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
open Stacks.DeRhamDirectImage (inverseImageBase inverseImageBaseProjection toInverseImageBase)
open Stacks.Cohomology.NaiveCupProductOnRingedSpaces (pushforwardComplex)
open Stacks.Cohomology.DerivedPullbackTensor (tensorComplexBifunctorOn)
open AlgebraicGeometry.RingedSpace.KFlatDerivedPullback renaming Modules → ModulesOn

universe u

namespace AlgebraicGeometry.RelativeDualitySituation

variable (D : RelativeDualitySituation.{u})

/-- The derived tensor product over `𝒪_S` is additive in its second variable. -/
instance additive_derivedTensorProductFunctor_obj_base
    (Z : DerivedModules.{u + 1, u} D.S.toRingedSpace.sheaf) :
    ((derivedTensorProductFunctor D.S.toRingedSpace.sheaf).obj Z).Additive := by
  let := (canonicalDerivedTensorProduct D.S.toRingedSpace.sheaf).commShift_right Z
  have := (canonicalDerivedTensorProduct D.S.toRingedSpace.sheaf).exact_right Z
  infer_instance

/-- `Ω^•_{X/S}` vanishes above degree `n`. -/
theorem isZero_deRhamCx_extend_X (k : ℤ) (hk : (D.n : ℤ) < k) :
    IsZero ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X k) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ k by omega)
  refine IsZero.of_iso ((SheafOfModules.restrictScalars _).map_isZero
    (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension D.f D.n m
      (by omega))) (D.deRhamCx.extendXIso ComplexShape.embeddingUpNat (i := m) rfl)

/-- **The pairings of the graded pieces are perfect at every shift.** For `p + q = n`, the pairing
`Q(Ω^p[-p]) ⊗^L Q(Ω^q[-q]) ⟶ Q(Ω^•)` given by the wedge product, pushed down along
`deRhamPushData f (2n)` with a trace `t` restricting on the top piece to the trace of
[Stacks, Tag 0G8I], is perfect at every shift. -/
theorem allPerf_gradedMul
    (ψ : (D.f.formsInDegreeZero D.n)⟦(D.n : ℤ)⟧ ≅ (Stacks.Duality.relativeDualizingComplex D.f
      (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
      (Stacks.Duality.derivedStructureSheafInDegree D.S 0)).obj)
    (s : D.deRhamDirectImageTop ⟶ (Stacks.Duality.derivedStructureSheafInDegree D.S 0).obj)
    (hs : D.topInclusion ≫ s = (Stacks.Duality.derivedPushforward D.f).map ψ.hom ≫
      (ObjectProperty.ι _).map (Stacks.Duality.relativeDualizingComplexTrace D.f
        (Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward D.f)
        (Stacks.Duality.derivedStructureSheafInDegree D.S 0)))
    (p q : ℤ) (hpq : p + q = D.n) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    letI := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
    (D.f.deRhamPushData (2 * D.n)).AllPerf s
      ((canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).toTensor
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj
            ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X p))
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
            ((D.deRhamCx.extend ComplexShape.embeddingUpNat).X q)) ≫
        DerivedCategory.Q.map (StacksDraft.StupidTruncation.gradedMul
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageBase D.f).sheaf)
          (SheafOfModules.multiplicationInt
            (SheafOfModules.wedgeProduct (Scheme.Hom.deRhamAlgebras D.f)
              (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras D.f))))
          D.isZero_deRhamCx_extend_X p q hpq)) := by
  let := (canonicalDerivedTensorProduct (inverseImageBase D.f).sheaf).commShift₂
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
  refine Functor.PairingPushData.allPerf_of_shiftStable (D.f.deRhamPushData (2 * D.n)) s
    (fun {K L} β => ∃ (A B : CochainComplex (ModulesOn D.X.toRingedSpace) ℤ)
      (h : ((tensorComplexBifunctorOn D.X.toRingedSpace).obj A).obj B ⟶ D.topComplexX)
      (_ : D.IsPerfectFormsPairing h)
      (e : K ⟶ DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj A))
      (e' : DerivedCategory.Q.obj ((pushforwardComplex (toInverseImageBase D.f)).obj B) ⟶ L)
      (_ : IsIso e) (_ : IsIso e'),
      (derivedTensorProductFunctor (inverseImageBase D.f).sheaf).PairingCompatible β
        (D.inducedDeRhamPairing h) e e') ?_ ?_ _ ?_
  · rintro K L β ⟨A, B, h, hh, e, e', he, he', hc⟩ a b hab
    obtain ⟨e₂, e₂', he₂, he₂', hc₂⟩ :=
      D.pairingCompatible_shiftedPairing_inducedDeRhamPairing h a b hab
    exact ⟨_, _, _, IsPerfectFormsPairing.shiftedPairing D hh a b hab, e⟦a⟧' ≫ e₂,
      e₂' ≫ e'⟦b⟧', inferInstance, inferInstance, (hc.shiftedPairing a b hab).trans hc₂⟩
  · rintro K L β ⟨A, B, h, hh, e, e', he, he', hc⟩
    refine ((D.f.deRhamPushData (2 * D.n)).perf_iff_of_pairingCompatible s e e' hc).2 ?_
    obtain ⟨e₃, he₃, hc₃⟩ := D.pairingCompatible_commShift_inducedDeRhamPairing h
    obtain ⟨u, v, θ, hθ, heq⟩ := D.exists_pushedPairing_eq_relativeCupProduct ψ s hs h
    have hθψ : IsIso (θ ≫ ψ.hom) := @IsIso.comp_isIso _ _ _ _ _ θ ψ.hom hθ (Iso.isIso_hom ψ)
    have hb : (Scheme.Hom.deRhamPushDataBase D.f).Perf s (D.inducedShiftedDeRhamPairing h) := by
      intro Z
      rw [heq]
      exact (Functor.bijective_pairingPrecomp_iff_of_pairingCompatible_iso u v
        (Functor.pairingCompatible_of_eq_iso u.hom v.symm rfl) Z).2
          (@IsPerfectFormsPairing.bijective_relativeCupProduct D _ _ _ hh (θ ≫ ψ.hom) hθψ Z)
    have hb' := ((Scheme.Hom.deRhamPushDataBase D.f).perf_iff_of_pairingCompatible s (𝟙 _) e₃
      hc₃).1 hb
    exact (Functor.PairingPushData.perf_shiftTarget_iff (Scheme.Hom.deRhamPushDataBase D.f)
      (2 * D.n) s (D.inducedDeRhamPairing h)).2 hb'
  · obtain ⟨e, e', he, he', hc⟩ :=
      D.pairingCompatible_gradedMul_inducedDeRhamPairing D.isZero_deRhamCx_extend_X p q hpq
    exact ⟨_, _, _, D.isPerfectFormsPairing_gradedWedgeX p q hpq, e, e', he, he', hc⟩

end AlgebraicGeometry.RelativeDualitySituation

end
