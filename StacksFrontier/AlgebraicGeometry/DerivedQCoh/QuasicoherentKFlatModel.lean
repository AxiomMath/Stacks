module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalenceStandard
public import StacksFrontier.AlgebraicGeometry.Modules.TildeKFlat
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TildeStalkKFlat
import StacksCore.Tactic.StacksAttribute

/-!
# A K-flat representative with quasi-coherent terms, on an affine scheme

Every object of `D_QCoh(𝒪_{Spec R})` is the class of a K-flat cochain complex of quasi-coherent
`𝒪_{Spec R}`-modules, and that complex may be taken to be the degreewise sheafification `P̃^•` of
a K-flat complex `P` of `R`-modules.

## Main results

* `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model_tilde`: every object of
  `D_QCoh(𝒪_{Spec R})` is isomorphic to `Q(P̃^•)` for a K-flat complex `P` of `R`-modules.
* `AlgebraicGeometry.StandardModel.exists_kFlat_isQuasicoherent_model`: every object of
  `D_QCoh(𝒪_{Spec R})` is isomorphic to `Q(C)` for a complex `C` of quasi-coherent modules that is
  K-flat both as `Stacks.SheafOfModules.IsKFlat` and as
  `Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex`.

## Implementation notes

The derived categories are those of `HasDerivedCategory.standard`, installed as a local instance
at priority `10000`.

## References

* [Stacks Project, Tag 06Y5](https://stacks.math.columbia.edu/tag/06Y5)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 08DV](https://stacks.math.columbia.edu/tag/08DV)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : CommRingCat.{u})

/-- **Every object of `D_QCoh(𝒪_{Spec R})` is the class of a degreewise sheafified K-flat
complex.** For every object `E` of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves there is
a K-flat complex `P` of `R`-modules with `Q(P̃^•) ≅ E`. -/
theorem exists_kFlat_isQuasicoherent_model_tilde (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ, CochainComplex.KFlat.{u, u} P ∧
      Nonempty (DerivedCategory.Q.obj
        (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≅ E) := by
  obtain ⟨M, ⟨eM⟩⟩ := exists_iso_mapDerivedCategory R E hE
  obtain ⟨P, hP, ⟨eP⟩⟩ := CochainComplex.KFlat.exists_kFlat_representative.{u, u, u + 1} M
  exact ⟨P, hP, ⟨((tilde.functor R).mapDerivedCategoryFactors.app P).symm ≪≫
    (tilde.functor R).mapDerivedCategory.mapIso eP ≪≫ eM⟩⟩

/-- **A K-flat representative with quasi-coherent terms, on an affine scheme.** Every object of
`D_QCoh(𝒪_{Spec R})` is the class of a cochain complex of `𝒪_{Spec R}`-modules whose terms are all
quasi-coherent and which is K-flat, both stalkwise (`Stacks.SheafOfModules.IsKFlat`) and as
`Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex`. -/
theorem exists_kFlat_isQuasicoherent_model (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    ∃ C : CochainComplex (Spec R).Modules ℤ,
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      Stacks.SheafOfModules.IsKFlat (specCommRingSheaf R) C ∧
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace C ∧
      Nonempty (DerivedCategory.Q.obj C ≅ E) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlat_isQuasicoherent_model_tilde R E hE
  refine ⟨((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj P, fun n => ?_,
    kFlat_tilde P hP, Stacks.TildeStalk.kFlatComplex_tilde R P hP, ⟨e⟩⟩
  exact inferInstanceAs ((tilde.functor R).obj (P.X n)).IsQuasicoherent

end AlgebraicGeometry.StandardModel

end
