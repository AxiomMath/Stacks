module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyFixedCover
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HypercohomologyCechComputes
public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialAbelian
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.TruncationTower

/-!
# Cohomology of a morphism of modules, computed on a fixed Čech covering

Let `𝒪` be a sheaf of commutative rings on a topological space and `f : ℱ ⟶ 𝒢` a morphism of
sheaves of `𝒪`-modules. When the Čech class maps of a covering `𝒰` are bijective (for instance
when `ℱ` and `𝒢` are acyclic on the finite intersections, [Stacks, Tag 0FLH]), `f` induces zero
on `H^{q+1}` exactly when it carries every Čech `(q+1)`-cocycle of `𝒰` to a Čech coboundary of `𝒰`.
The same holds for the cohomology of the underlying abelian sheaves ([Stacks, Tag 01F1]).

On a scheme `Z` this applies to the de Rham differential, which is linear over
`h^{-1}𝒪_S` but not over `𝒪_Z`: a quasi-coherent `𝒪_Z`-module read over a sheaf of rings mapping
to `𝒪_Z` is acyclic on affine opens ([Stacks, Tags 01F1, 01XB]).

## Main results

* `Stacks.Cech.Hypercohomology.hypercohomologyMap_eq_zero_iff_forall_exists_cechD`.
* `Stacks.Cech.Hypercohomology.rightDerived_toSheaf_map_eq_zero_iff`: the comparison with the
  cohomology of the underlying abelian sheaves.
* `Stacks.Cech.Hypercohomology.rightDerived_toSheaf_map_eq_zero_iff_cech`: the criterion on a
  scheme, for a covering with affine finite intersections.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing abSections)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] CechCochains.Cochain
attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- **A morphism of sheaves of modules is zero on cohomology exactly when it carries every Čech
cocycle of a fixed covering to a Čech coboundary**, when the Čech class maps of that covering
are surjective for the source and injective for the target in the degree considered. -/
theorem hypercohomologyMap_eq_zero_iff_forall_exists_cechD {F G : SheafOfModules.{u} (ringSheaf O)}
    (f : F ⟶ G) (q : ℕ)
    (hF : Function.Surjective (cechClass O U hU (singlePlus O F 0) (((q + 1 : ℕ) : ℤ) + 0)))
    (hG : Function.Injective (cechClass O U hU (singlePlus O G 0) (((q + 1 : ℕ) : ℤ) + 0))) :
    hypercohomologyMap O (singlePlusMapAt O f 0) (((q + 1 : ℕ) : ℤ) + 0) = 0 ↔
      ∀ c : CechCochains.Cochain U (abSections F) (q + 1),
        CechCochains.cechD U (abSections F) (q + 1) c = 0 →
          ∃ t : CechCochains.Cochain U (abSections G) q,
            CechCochains.cechD U (abSections G) q t =
              Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map f).hom (q + 1)
                c := by
  refine ⟨fun h c hc => ?_, fun h => ModuleCat.hom_ext (LinearMap.ext fun x => ?_)⟩
  · have hmap := hypercohomologyMap_cechCocycleClassAt U hU 0 f c hc
    rw [h] at hmap
    exact exists_cechD_eq_of_cechCocycleClassAt_eq_zero U hU G 0 hG _ _ hmap.symm
  · obtain ⟨c, hc, rfl⟩ := exists_cechCocycleClassAt_eq_of_surjective U hU F 0 (q + 1) hF x
    rw [ModuleCat.hom_zero, LinearMap.zero_apply]
    refine (hypercohomologyMap_cechCocycleClassAt U hU 0 f c hc).trans ?_
    obtain ⟨t, ht⟩ := h c hc
    exact cechCocycleClassAt_eq_zero U hU G 0 t _ _ ht

/-- The ringed space `(X, 𝒪)` of a sheaf of commutative rings `𝒪` on a topological space. -/
abbrev ringedSpaceOf : AlgebraicGeometry.RingedSpace.{u, u} where
  carrier := X
  presheaf := O.obj
  IsSheaf := O.property

/-- A module placed in degree zero, then forgotten to abelian sheaves, is its underlying abelian
sheaf placed in degree zero. -/
def toSheafSinglePlusIso :
    SheafOfModules.toSheaf (ringSheaf O) ⋙
        Stacks.DerivedIndexing.singlePlusFunctor (AbelianSheaf X) 0 ≅
      Stacks.DerivedIndexing.singlePlusFunctor (SheafOfModules.{u} (ringSheaf O)) 0 ⋙
        (SheafOfModules.toSheaf (ringSheaf O)).mapCochainComplexPlus :=
  Functor.fullyFaithfulCancelRight (CochainComplex.Plus.ι _)
    (HomologicalComplex.singleMapHomologicalComplex (SheafOfModules.toSheaf (ringSheaf O))
      (ComplexShape.up ℤ) 0).symm

/-- **The cohomology of the underlying abelian sheaf is the hypercohomology of the module placed
in degree zero** ([Stacks, Tag 01F1]), naturally in the module. -/
def rightDerivedToSheafIso (n : ℕ) :
    SheafOfModules.toSheaf (ringSheaf O) ⋙ (sectionsFunctor X ⊤).rightDerived n ≅
      Stacks.DerivedIndexing.singlePlusFunctor (SheafOfModules.{u} (ringSheaf O)) 0 ⋙
        DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (ringSheaf O) (op ⊤)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor _ (n : ℤ) ⋙
        forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _ (Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor X ⊤) n) ≪≫
    Functor.isoWhiskerRight (toSheafSinglePlusIso O)
      (DerivedCategory.Plus.Q ⋙ (sectionsFunctor X ⊤).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft _ (realizationNatIso (ringedSpaceOf O) n)

/-- **A morphism of sheaves of modules induces zero on the cohomology of the underlying abelian
sheaves exactly when it induces zero on hypercohomology** in degree `n`. -/
theorem rightDerived_toSheaf_map_eq_zero_iff {F G : SheafOfModules.{u} (ringSheaf O)}
    (f : F ⟶ G) (n : ℕ) :
    ((sectionsFunctor X ⊤).rightDerived n).map ((SheafOfModules.toSheaf _).map f) = 0 ↔
      hypercohomologyMap O (singlePlusMapAt O f 0) (n : ℤ) = 0 := by
  have e := rightDerivedToSheafIso O n
  refine ⟨fun h => ?_, fun h => Stacks.Cohomology.TopDegree.map_eq_zero_of_natIso e f ?_⟩
  · exact (forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u}).map_injective
      ((Stacks.Cohomology.TopDegree.map_eq_zero_of_natIso e.symm f h).trans (Functor.map_zero
        (forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u}) _ _).symm)
  · show (forget₂ (ModuleCat.{u} ((ringSheaf O).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
      (hypercohomologyMap O (singlePlusMapAt O f 0) (n : ℤ)) = 0
    rw [h, Functor.map_zero]

section Scheme

variable {Z : AlgebraicGeometry.Scheme.{u}}
  (A : Sheaf (Opens.grothendieckTopology Z) CommRingCat.{u})
  (α : ringSheaf A ⟶ Z.ringCatSheaf)

/-- **A quasi-coherent module, read as a module over a sheaf of rings mapping to `𝒪_Z`, is acyclic
on affine opens.** Its cohomology over `V` is that of the underlying abelian sheaf
([Stacks, Tag 01F1] for both sheaves of rings), which vanishes in positive degrees on an affine
open ([Stacks, Tag 01XB]). -/
theorem isZero_rightDerived_evaluation_restrictScalars (M : Z.Modules) [M.IsQuasicoherent]
    (V : Z.Opens) (hV : AlgebraicGeometry.IsAffineOpen V) (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation (ringSheaf A) (op V)).rightDerived m).obj
      ((SheafOfModules.restrictScalars α).obj M)) := by
  have h₂ : IsZero ((((sheafSections (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj
      (op V)).rightDerived m).obj ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M)) :=
    (Functor.map_isZero (forget₂ _ AddCommGrpCat.{u})
      (AlgebraicGeometry.isZero_rightDerived_evaluation_of_isAffineOpen Z M V hV m hm)).of_iso
      ((Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso Z.ringCatSheaf V m).app
        M).symm
  have h₃ : IsZero ((forget₂ (ModuleCat.{u} ((ringSheaf A).obj.obj (op V))) AddCommGrpCat.{u}).obj
      (((SheafOfModules.evaluation (ringSheaf A) (op V)).rightDerived m).obj
        ((SheafOfModules.restrictScalars α).obj M))) :=
    h₂.of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedSectionsForgetIso (ringSheaf A) V
      m).app ((SheafOfModules.restrictScalars α).obj M))
  exact ModuleCat.isZero_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero h₃)

variable {A α} in
/-- A quasi-coherent module placed in degree zero, read over `A`, is acyclic on the finite
intersections of a covering whose finite intersections are affine. -/
theorem isZero_rightDerived_singlePlus_restrictScalars (M : Z.Modules) [M.IsQuasicoherent]
    {I : Type u} (U : I → Z.Opens)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), AlgebraicGeometry.IsAffineOpen (⨅ k, U (s k)))
    (q : ℤ) (r : ℕ) (s : Fin (r + 1) → I) (m : ℕ) (hm : 0 < m) :
    IsZero (((SheafOfModules.evaluation (ringSheaf A) (op (⨅ k, U (s k)))).rightDerived m).obj
      ((singlePlus A ((SheafOfModules.restrictScalars α).obj M) 0).1.X q)) := by
  by_cases hq : q = 0
  · subst hq
    exact (isZero_rightDerived_evaluation_restrictScalars A α M _ (haff r s) m hm).of_iso
      (((SheafOfModules.evaluation (ringSheaf A) (op (⨅ k, U (s k)))).rightDerived m).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _))
  · have := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive.{u, u} (ringSheaf A)
      (op (⨅ k, U (s k)))
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- **Cohomology of the underlying abelian sheaves, computed on a fixed affine covering.** Let `ψ`
be a morphism of `A`-modules between two quasi-coherent `𝒪_Z`-modules read over a sheaf of rings
`A ⟶ 𝒪_Z`, and let `U` be a covering of `Z` all of whose finite intersections are affine. Then
`ψ` induces zero on `H^{q+1}(Z, -)` of the underlying abelian sheaves exactly when it carries every
Čech `(q+1)`-cocycle of `U` to a Čech coboundary of `U`. -/
theorem rightDerived_toSheaf_map_eq_zero_iff_cech (M N : Z.Modules) [M.IsQuasicoherent]
    [N.IsQuasicoherent]
    (ψ : (SheafOfModules.restrictScalars α).obj M ⟶ (SheafOfModules.restrictScalars α).obj N)
    {I : Type u} (U : I → Z.Opens) (hU : ⊤ = ⨆ i, U i)
    (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), AlgebraicGeometry.IsAffineOpen (⨅ k, U (s k)))
    (q : ℕ) :
    ((sectionsFunctor Z.carrier ⊤).rightDerived (q + 1)).map
        ((SheafOfModules.toSheaf _).map ψ) = 0 ↔
      ∀ c : CechCochains.Cochain U (abSections ((SheafOfModules.restrictScalars α).obj M)) (q + 1),
        CechCochains.cechD U _ (q + 1) c = 0 →
          ∃ t : CechCochains.Cochain U (abSections ((SheafOfModules.restrictScalars α).obj N)) q,
            CechCochains.cechD U _ q t =
              Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map ψ).hom (q + 1)
                c := by
  rw [rightDerived_toSheaf_map_eq_zero_iff A ψ (q + 1)]
  exact hypercohomologyMap_eq_zero_iff_forall_exists_cechD A U hU ψ q
    (bijective_cechClass_of_acyclic A U hU _
      (isZero_rightDerived_singlePlus_restrictScalars M U haff) _).2
    (bijective_cechClass_of_acyclic A U hU _
      (isZero_rightDerived_singlePlus_restrictScalars N U haff) _).1

end Scheme

end Stacks.Cech.Hypercohomology
