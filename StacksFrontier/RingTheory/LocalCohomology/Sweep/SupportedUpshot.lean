module

public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedCohomologyColimit
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.SupportedDerivedAdjunction
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.TensorFormula

/-!
# The upshot: `RΓ_T` is the right adjoint to the inclusion, and computes local cohomology

Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset stable under specialization. Stacks
Remark 0EF4 collects the discussion of Tags 0EF0–0EF3 into three assertions: `RΓ_T` is the
right adjoint to the inclusion `D_T^+(A) ⥤ D^+(A)`; when `dim(A) < ∞` it is the right adjoint
to the inclusion `D_T(A) ⥤ D(A)`; and in both cases
$$
H^i_T(K) \;=\; H^i(R\Gamma_T(K)) \;=\; R^iH^0_T(K) \;=\;
\operatorname*{colim}_{Z \subseteq T\text{ closed}} H^i_Z(K).
$$
This file states the remark as one theorem.

## Main results

* `Stacks.LocalCohomology.nonempty_rightDerivedFunctorPlus_supportedSections_comp_iso` — on
  `D^+(A)`, the derived functor of `H^0_T` into `Mod_{A,T}`, followed by the inclusion, is the
  derived functor of `H^0_T` into `Mod_A`.
* `Stacks.LocalCohomology.nonempty_inclusion_adj_and_localCohomologyWithSupportIn_colimit` —
  Tag 0EF4, all three assertions together.

## Implementation notes

The adjoint `RΓ_T` of the remark derives `H^0_T` as a functor into `Mod_{A,T}`, while the
library's `H^i_T` (`localCohomologyWithSupportIn`, `localCohomologyWithSupportInPlus`) is the
cohomology of the derived functor of `H^0_T` as a functor into `Mod_A`. The two are identified
by uniqueness of right derived functors: on `D(A)` by
`Stacks.LocalCohomology.nonempty_derivedSupportedSections_comp_iso`, on `D^+(A)` by the
comparison proved here. Through these the remark's chain of equalities is stated literally:
`H^i(RΓ_T(K))` is the cohomology of the adjoint, `R^iH^0_T(K)` the cohomology in `Mod_{A,T}` of
`RH^0_T(K)`, and both are isomorphic to `H^i_T(K)`, as is the filtered colimit over the closed
subsets `Z ⊆ T`. The second adjunction is stated under the finite-dimensionality hypothesis of
the source, which nothing else needs, so it appears as an implication rather than as a
hypothesis of the whole theorem.

## References

* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

section PlusComparison

variable (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A))

/-- The unit exhibiting `D^+(A) ⥤ D^+(Mod_{A,T}) ⥤ D^+(A)`, the bounded-below derived functor of
supported sections followed by the inclusion, as a right derived functor of sections with support
in `T` on bounded-below complexes. -/
private def supportedPlusUnit :
    (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙
        ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
          (supportModuleProperty A T :
            ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlus) :=
  Functor.whiskerRight (Functor.mapHomotopyCategoryPlusCompIso
      ((supportModuleProperty A T).liftCompιIso (sectionsWithSupportInFunctor.{u, v} A T)
        (sectionsWithSupportIn_supported.{u, v} A T))).inv DerivedCategory.Plus.Qh ≫
    Functor.whiskerLeft (supportedSectionsFunctor.{u, v} A T).mapHomotopyCategoryPlus
      ((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlusFactorsh).inv ≫
    Functor.whiskerRight (supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlusUnith
      (supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlus

private instance isRightDerivedFunctor_supportedPlusUnit :
    ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (supportedPlusUnit.{u, v} A T) (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    fun _ ↦ IsIso.comp_isIso' inferInstance (IsIso.comp_isIso'
      (Iso.isIso_inv (((supportModuleProperty A T :
        ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlusFactorsh).app _))
      (by dsimp only [Functor.whiskerRight_app]; infer_instance))

/-- **The two constructions of `RΓ_T` on `D^+(A)` agree.** Deriving degree-zero sections with
support in `T` on bounded-below objects as a functor into `Mod_{A,T}` and then including into
`D^+(A)` is isomorphic to deriving it as a functor into `Mod_A`. -/
theorem nonempty_rightDerivedFunctorPlus_supportedSections_comp_iso :
    Nonempty ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
        (supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategoryPlus ≅
      derivedSectionsWithSupportInPlus.{u, v} A T) :=
  ⟨Functor.rightDerivedUnique _
    (sectionsWithSupportInFunctor.{u, v} A T).rightDerivedFunctorPlus
    (supportedPlusUnit.{u, v} A T)
    (sectionsWithSupportInFunctor.{u, v} A T).rightDerivedFunctorPlusUnith
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{max u v} A))⟩

end PlusComparison

/-- **Stacks Project, Tag 0EF4.** Let `A` be a Noetherian ring and `T ⊆ Spec(A)` a subset
stable under specialization. Write `RΓ_T` for `RH^0_T` followed by the comparison
`D(Mod_{A,T}) ⥤ D_T(A)`, on `D^+(A)` and on `D(A)`. Then:

* `RΓ_T : D^+(A) ⥤ D_T^+(A)` is right adjoint to the inclusion `D_T^+(A) ⥤ D^+(A)`;
* if `dim(A) < ∞`, then `RΓ_T : D(A) ⥤ D_T(A)` is right adjoint to the inclusion
  `D_T(A) ⥤ D(A)`;
* in both cases `H^i_T(K) = H^i(RΓ_T(K)) = R^iH^0_T(K) = colim_{Z ⊆ T closed} H^i_Z(K)`.

Here `H^i_T(K)` is `localCohomologyWithSupportInPlus` (for `K` in `D^+(A)`) or
`localCohomologyWithSupportIn` (for `K` in `D(A)`), the cohomology of the derived functor of
`H^0_T : Mod_A ⥤ Mod_A`. For each of the two cases the theorem states: the adjunction; that the
adjoint `RΓ_T`, followed by the inclusion of `D_T(A)`, is isomorphic to that derived functor; and,
for every `K` and `i`, that `H^i(RΓ_T(K))`, `R^iH^0_T(K) = H^i(RH^0_T(K))` (the `i`-th
cohomology in `Mod_{A,T}`, viewed as an `A`-module) and the filtered colimit of `H^i_Z(K)` over
the closed subsets `Z ⊆ T` (`closedSupportIdeal_isFiltered`) are each isomorphic to `H^i_T(K)`.
Only the adjunction on `D(A)` uses `dim(A) < ∞`. -/
@[stacks 0EF4]
theorem nonempty_inclusion_adj_and_localCohomologyWithSupportIn_colimit
    (A : Type u) [CommRing A] [IsNoetherianRing A] (T : Set (PrimeSpectrum A))
    (hT : StableUnderSpecialization T) :
    Nonempty
        ((supportedPlusProperty.{u, v} A T).ι ⊣
          ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
            comparisonPlus.{u, v} A T hT)) ∧
      Nonempty
        (((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
            comparisonPlus.{u, v} A T hT) ⋙ (supportedPlusProperty.{u, v} A T).ι ≅
          derivedSectionsWithSupportInPlus.{u, v} A T) ∧
      (∀ (i : ℤ) (K : DerivedCategory.Plus (ModuleCat.{max u v} A)),
        Nonempty
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u v} A) i).obj
                ((supportedPlusProperty.{u, v} A T).ι.obj
                  (((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
                    comparisonPlus.{u, v} A T hT).obj K)) ≅
              localCohomologyWithSupportInPlus A T K i) ∧
          Nonempty
            (((DerivedCategory.Plus.homologyFunctor (ModulesSupportedIn.{u, max u v} A T) i).obj
                ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus.obj K)).obj ≅
              localCohomologyWithSupportInPlus A T K i) ∧
          Nonempty
            (colimit ((closedSupportDiagram.{u, v} A T i).obj (DerivedCategory.Plus.ι.obj K)) ≅
              localCohomologyWithSupportInPlus A T K i)) ∧
      (ringKrullDim A < ⊤ →
        Nonempty
          ((DerivedCategoryB.derivedCategoryB
              (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι ⊣
            (derivedSupportedSections.{u, v} A T ⋙
              supportedModulesComparison.{u, max u v} A T))) ∧
      Nonempty
        ((derivedSupportedSections.{u, v} A T ⋙ supportedModulesComparison.{u, max u v} A T) ⋙
            (DerivedCategoryB.derivedCategoryB
              (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι ≅
          derivedSectionsWithSupportIn.{u, v} A T) ∧
      (∀ (i : ℤ) (K : DerivedCategory (ModuleCat.{max u v} A)),
        Nonempty
            ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
                ((DerivedCategoryB.derivedCategoryB
                  (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι.obj
                  ((derivedSupportedSections.{u, v} A T ⋙
                    supportedModulesComparison.{u, max u v} A T).obj K)) ≅
              localCohomologyWithSupportIn A T K i) ∧
          Nonempty
            (((DerivedCategory.homologyFunctor (ModulesSupportedIn.{u, max u v} A T) i).obj
                ((derivedSupportedSections.{u, v} A T).obj K)).obj ≅
              localCohomologyWithSupportIn A T K i) ∧
          Nonempty
            (colimit ((closedSupportDiagram.{u, v} A T i).obj K) ≅
              localCohomologyWithSupportIn A T K i)) := by
  obtain ⟨eP⟩ := nonempty_rightDerivedFunctorPlus_supportedSections_comp_iso.{u, v} A T
  obtain ⟨ψ⟩ := comparisonPlus_comp_ι_iso.{u, v} A T hT
  obtain ⟨eU⟩ := nonempty_derivedSupportedSections_comp_iso.{u, v} A T hT
  let L := (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι
  let fP : ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus ⋙
      comparisonPlus.{u, v} A T hT) ⋙ (supportedPlusProperty.{u, v} A T).ι ≅
        derivedSectionsWithSupportInPlus.{u, v} A T :=
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ ψ ≪≫ eP
  let fU : (derivedSupportedSections.{u, v} A T ⋙ supportedModulesComparison.{u, max u v} A T) ⋙
      (DerivedCategoryB.derivedCategoryB
        (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))).ι ≅
        derivedSectionsWithSupportIn.{u, v} A T :=
    Functor.associator _ _ _ ≪≫ eU
  refine ⟨inclusion_adj_derivedSupportedSectionsPlus.{u, v} A T hT, ⟨fP⟩,
    fun i K => ⟨⟨(DerivedCategory.Plus.homologyFunctor _ i).mapIso (fP.app K)⟩, ⟨?_⟩,
      nonempty_colimitClosedSupportIsoPlus.{u, v} A T hT i K⟩,
    fun hdim => inclusion_adj_derivedSupportedSectionsComparison.{u, v} A T hT hdim, ⟨fU⟩,
    fun i K => ⟨⟨(DerivedCategory.homologyFunctor _ i).mapIso (fU.app K)⟩, ⟨?_⟩,
      ⟨colimitClosedSupportIso.{u, v} A T hT i K⟩⟩⟩
  · exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso L i).app
      (DerivedCategory.Plus.ι.obj
        ((supportedSectionsFunctor.{u, v} A T).rightDerivedFunctorPlus.obj K))).symm ≪≫
      (DerivedCategory.Plus.homologyFunctor _ i).mapIso (eP.app K)
  · exact ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso L i).app
      ((derivedSupportedSections.{u, v} A T).obj K)).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (eU.app K)

end Stacks.LocalCohomology

end
