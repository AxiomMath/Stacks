module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.DerivedTildePerfect
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDerivedHom
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology

/-!
# The derived internal Hom out of a perfect object on an affine scheme

Let `R` be a commutative ring and `X = Spec R`.  For a perfect object `E` of `D(𝒪_X)` and an
object `E'` of `D(𝒪_X)` with quasi-coherent cohomology sheaves, the derived internal Hom
`R𝓗om_{𝒪_X}(E, E')` again has quasi-coherent cohomology sheaves, with no boundedness hypothesis
on `E'`.

## Main results

* `Stacks.DerivedQCoh.OpenLift.isQuasicoherent_homology_derivedSheafHom_of_isPerfect`: the
  cohomology sheaves of `R𝓗om_{𝒪_X}(E, E')` are quasi-coherent.

## References

* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08EB](https://stacks.math.columbia.edu/tag/08EB)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.DerivedQCoh.OpenLift

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u})

/-- On `X = Spec R`, for `E` perfect and `E'` with quasi-coherent cohomology sheaves, every
cohomology sheaf of `R𝓗om_{𝒪_X}(E, E')` is quasi-coherent. -/
theorem isQuasicoherent_homology_derivedSheafHom_of_isPerfect
    (E E' : DerivedCategory ((Spec R).Modules))
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec R).toRingedSpace) E)
    (hE' : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E'))
    (n : ℤ) :
    SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op E)).obj E')) := by
  have hEqc : ∀ n : ℤ, SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E) :=
    AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent (Spec R) E
      (Stacks.Cohomology.TorAmplitude.isPseudoCoherent_of_isPerfect E hE)
  obtain ⟨K, ⟨eK⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R E hEqc
  obtain ⟨L, ⟨eL⟩⟩ := AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory R E' hE'
  have hK : StacksDraft.Perfect.IsPerfect K :=
    (AlgebraicGeometry.isPerfect_tilde_iff K).mp
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := (Spec R).toRingedSpace)
        eK.symm hE)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      ((((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso eK.op).app E' ≪≫
        ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj
            (op ((tilde.functor R).mapDerivedCategory.obj K))).mapIso eL.symm) ≪≫
        AlgebraicGeometry.affinePerfectDerivedSheafHomIso R K L hK)).symm
    (AlgebraicGeometry.isQuasicoherent_homology_mapDerivedCategory_obj R _ n)

end Stacks.DerivedQCoh.OpenLift

end
