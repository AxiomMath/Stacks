module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.HomologyComparisonCounit
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# `Rε_*` on complexes with quasi-coherent cohomology

Let `S` be a scheme, `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of ringed sites of
Stacks 08H7, and `ε^* ⊣ Rε_*` the adjunction on unbounded derived categories of
`AlgebraicGeometry.SmallEtale.derivedAssociatedModuleAdjunction`.  This file carries out the part
of the proof of Stacks 071Q which follows the computation of the cohomology sheaves of `Rε_*`.
The homology comparison `H^q(ε_* I) ⟶ ε_* H^q(I)` is invertible at every K-injective complex `I`
with quasi-coherent cohomology
(`AlgebraicGeometry.SmallEtale.isIso_homologyComparison_restrictModuleOfSheaf`, which is where
Stacks 03DW, 01XB and 0BKZ enter), and from it:

* `H^q(Rε_* E) ≅ ε_* H^q(E)` for every `E` with quasi-coherent cohomology, so `Rε_* E` has
  quasi-coherent cohomology;
* the counit `ε^* Rε_* E ⟶ E` is an isomorphism for every such `E`;
* the unit `F ⟶ Rε_* ε^* F` is an isomorphism for every `F` with quasi-coherent cohomology.

## Main results

* `AlgebraicGeometry.SmallEtale.isIso_derivedRestrictModuleHomologyComparison_app`: the edge
  morphism `H^q(Rε_* E) ⟶ ε_* H^q(E)` is an isomorphism.
* `AlgebraicGeometry.SmallEtale.isQuasicoherent_homology_derivedRestrictModule`: `Rε_* E` has
  quasi-coherent cohomology.
* `AlgebraicGeometry.SmallEtale.isIso_derivedAssociatedModuleAdjunction_counit_app`: the counit
  of `ε^* ⊣ Rε_*` is an isomorphism at `E`.
* `AlgebraicGeometry.SmallEtale.isIso_derivedAssociatedModuleAdjunction_unit_app`: the unit of
  `ε^* ⊣ Rε_*` is an isomorphism at `F`.

## References

* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison

universe w₁ w₂ u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every object of the derived category of `𝒪`-modules on the small étale site of `S` is the
image of a K-injective complex. -/
theorem exists_isKInjective_iso
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))) :
    ∃ I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ, I.IsKInjective ∧
      Nonempty (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
        ≅ E) := by
  obtain ⟨I, f, hI, hf⟩ := exists_quasiIso_isKInjective B S hS (DerivedCategory.Q.objPreimage E)
  exact ⟨I, hI, ⟨(DerivedCategory.quotientCompQhIso _).app I ≪≫
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

/-- The cohomology sheaves of a K-injective complex are those of the object of the derived
category it represents. -/
def homologyIsoOfQhObjIso [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]
    {I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ}
    {E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))}
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅ E)
    (m : ℤ) :
    (DerivedCategory.homologyFunctor _ m).obj E ≅ I.homology m :=
  (DerivedCategory.homologyFunctor _ m).mapIso e.symm ≪≫
    (DerivedCategory.homologyFunctorFactorsh _ m).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≪≫
    (HomotopyCategory.homologyFunctorFactors _ (ComplexShape.up ℤ) m).app I

/-- A complex representing an object of the derived category with quasi-coherent cohomology has
quasi-coherent cohomology. -/
theorem isQuasicoherentOnSite_homology_of_qhObjIso
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]
    {I : CochainComplex (SheafOfModules.{u} (structureSheaf B S hS)) ℤ}
    {E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS))}
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅ E)
    (hE : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj E).IsQuasicoherentOnSite) (m : ℤ) :
    (I.homology m).IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} (structureSheaf B S hS)).prop_of_iso
    (homologyIsoOfQhObjIso B S hS e m) (hE m)

/-- A natural transformation out of the derived category is invertible at `E` with
quasi-coherent cohomology once it is so at K-injective complexes with quasi-coherent cohomology. -/
private theorem isIso_app_of_isKInjective_of_isQuasicoherentOnSite
    [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]
    {D : Type*} [Category D]
    {F G : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)) ⥤ D} (τ : F ⟶ G)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj E).IsQuasicoherentOnSite)
    (h : ∀ I : CochainComplex _ ℤ, I.IsKInjective → (∀ m, (I.homology m).IsQuasicoherentOnSite) →
      IsIso (τ.app (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I)))) :
    IsIso (τ.app E) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_iso B S hS E
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  exact h I hI (isQuasicoherentOnSite_homology_of_qhObjIso B S hS e hE)

section Derived

variable [HasDerivedCategory.{w₁} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{w₂} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **`H^q(Rε_* E) = ε_* H^q(E)`** for `E` with quasi-coherent cohomology: the edge morphism of
`Rε_*` is an isomorphism at `E`. -/
theorem isIso_derivedRestrictModuleHomologyComparison_app
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj E).IsQuasicoherentOnSite) (q : ℤ) :
    IsIso ((derivedHomologyComparison (restrictModuleOfSheaf B S hS) (derivedRestrictModule B S hS)
      (derivedRestrictModuleUnit B S hS) (exists_quasiIso_isKInjective B S hS) q).app E) := by
  refine isIso_app_of_isKInjective_of_isQuasicoherentOnSite B S hS _ E hE fun I hI hqc => ?_
  have := isIso_homologyComparison_restrictModuleOfSheaf B S hS I hI hqc q
  exact isIso_derivedHomologyComparison_app_of_isKInjective _ _ _ _ q I hI

/-- **`Rε_*` preserves quasi-coherent cohomology**: for `E` with quasi-coherent cohomology,
`H^m(Rε_* E) ≅ ε_* H^m(E)` is quasi-coherent. -/
theorem isQuasicoherent_homology_derivedRestrictModule
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj E).IsQuasicoherentOnSite) (m : ℤ) :
    ((DerivedCategory.homologyFunctor _ m).obj
      ((derivedRestrictModule B S hS).obj E)).IsQuasicoherent := by
  have := isIso_derivedRestrictModuleHomologyComparison_app B S hS E hE m
  exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
    (asIso ((derivedHomologyComparison (restrictModuleOfSheaf B S hS)
      (derivedRestrictModule B S hS) (derivedRestrictModuleUnit B S hS)
      (exists_quasiIso_isKInjective B S hS) m).app E)).symm
    (isQuasicoherent_restrictModule B S hS _ (hE m))

/-- **The counit `ε^* Rε_* E ⟶ E` is an isomorphism** for `E` with quasi-coherent cohomology.  At a
K-injective representative `I` it is, up to isomorphisms, the counit `ε^* ε_* I ⟶ I` on
complexes, whose effect on `H^q` is the comparison `H^q(ε_* I) ⟶ ε_* H^q(I)` followed by the counit
at the quasi-coherent `H^q(I)`. -/
theorem isIso_derivedAssociatedModuleAdjunction_counit_app
    (E : DerivedCategory (SheafOfModules.{u} (structureSheaf B S hS)))
    (hE : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj E).IsQuasicoherentOnSite) :
    IsIso ((derivedAssociatedModuleAdjunction B S hS).counit.app E) := by
  refine isIso_app_of_isKInjective_of_isQuasicoherentOnSite B S hS _ E hE fun I hI hqc => ?_
  let c := (Adjunction.mapHomologicalComplexAdjunction (associatedModuleOfSheafAdjunction B S hS)
    (ComplexShape.up ℤ)).counit.app I
  have hQ : IsIso (DerivedCategory.Q.map c) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso, quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact isIso_homologyMap_counit_of_isIso_homologyComparison
      (associatedModuleOfSheafAdjunction B S hS) I q
      (isIso_homologyComparison_restrictModuleOfSheaf B S hS I hI hqc q)
      (isIso_counit B S hS _ (hqc q) (isQuasicoherent_restrictModule B S hS _ (hqc q)))
  have hQh : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map c)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso _) c).2 hQ
  let := Stacks.Cohomology.SupportedComplexes.isLeftDerivedFunctor_mapDerivedCategory_of_exact
    (G₀ := associatedModuleOfSheaf B S hS)
  let := Stacks.Cohomology.SupportedComplexes.isLeftDerivedFunctor_mapDerivedCategory_comp_of_exact
    (G₀ := associatedModuleOfSheaf B S hS) (derivedRestrictModule B S hS)
  let := Functor.isRightDerivedFunctor_comp_of_coresolutions
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (derivedRestrictModuleUnit B S hS)
    (associatedModuleOfSheaf B S hS).mapDerivedCategory
    (Stacks.Cohomology.SupportedComplexes.exists_quasiIso_qh_map_bijective
      (exists_quasiIso_isKInjective B S hS))
  have hfac := (Adjunction.mapHomotopyCategoryAdjunction (associatedModuleOfSheafAdjunction B S hS)
    (ComplexShape.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    (associatedModuleOfSheaf B S hS).mapDerivedCategoryFactorsh.hom
    (derivedRestrictModuleUnit B S hS) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)
  have hβ := isIso_derivedRestrictModuleUnit_app_of_isKInjective B S hS I hI
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance
    ((congrArg IsIso hfac).mpr (IsIso.comp_isIso' inferInstance hQh))

/-- **The unit `F ⟶ Rε_* ε^* F` is an isomorphism** for `F` with quasi-coherent cohomology.  By the
triangle identity and the counit at `ε^* F`, `ε^*` of the unit is an isomorphism; in each degree
the unit is then a morphism of quasi-coherent `𝒪_S`-modules which `ε^*` carries to an isomorphism,
and `ε^*` is fully faithful on quasi-coherent modules. -/
theorem isIso_derivedAssociatedModuleAdjunction_unit_app
    (F : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf))
    (hF : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj F).IsQuasicoherent) :
    IsIso ((derivedAssociatedModuleAdjunction B S hS).unit.app F) := by
  have hGF : ∀ m, ((DerivedCategory.homologyFunctor _ m).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj F)).IsQuasicoherentOnSite :=
    fun m => (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).prop_of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (associatedModuleOfSheaf B S hS) m).app F).symm
      (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS _ (hF m))
  have hε := isIso_derivedAssociatedModuleAdjunction_counit_app B S hS _ hGF
  have hGη : IsIso ((associatedModuleOfSheaf B S hS).mapDerivedCategory.map
      ((derivedAssociatedModuleAdjunction B S hS).unit.app F)) := by
    have : (associatedModuleOfSheaf B S hS).mapDerivedCategory.map
        ((derivedAssociatedModuleAdjunction B S hS).unit.app F) =
        inv ((derivedAssociatedModuleAdjunction B S hS).counit.app
          ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj F)) := by
      rw [← cancel_mono ((derivedAssociatedModuleAdjunction B S hS).counit.app
        ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj F)), IsIso.inv_hom_id]
      exact (derivedAssociatedModuleAdjunction B S hS).left_triangle_components F
    rw [this]
    infer_instance
  rw [DerivedCategory.isIso_iff]
  intro q
  set η := (derivedAssociatedModuleAdjunction B S hS).unit.app F
  have hT := isQuasicoherent_homology_derivedRestrictModule B S hS _ hGF q
  have h1 : IsIso ((associatedModuleOfSheaf B S hS).map
      ((DerivedCategory.homologyFunctor _ q).map η)) := by
    have : IsIso ((DerivedCategory.homologyFunctor _ q).map
        ((associatedModuleOfSheaf B S hS).mapDerivedCategory.map η)) := inferInstance
    exact (NatIso.isIso_map_iff
      (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        (associatedModuleOfSheaf B S hS) q) η).1 this
  let φ : (⟨_, hF q⟩ : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) ⟶
      ⟨_, hT⟩ := ObjectProperty.homMk ((DerivedCategory.homologyFunctor _ q).map η)
  have h2 : IsIso ((associatedModuleQcohOnSite B S hS).map φ) := by
    have : IsIso ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (structureSheaf B S hS)).ι.map ((associatedModuleQcohOnSite B S hS).map φ)) := h1
    exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _
  have h3 : IsIso φ := (fullyFaithfulAssociatedModuleQcohOnSite B S hS).isIso_of_isIso_map φ
  exact (inferInstance : IsIso ((SheafOfModules.isQuasicoherent S.ringCatSheaf).ι.map φ))

end Derived

end AlgebraicGeometry.SmallEtale

end
