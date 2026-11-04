module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeFirstChernClass
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison

/-!
# The de Rham first Chern class in the sheaf-of-modules realization

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. The de Rham first Chern class of
`StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.FilteredFirstChernClass` is constructed in
the hypercohomology of the de Rham complex read in sheaves of abelian groups, because `d log` is
only additive. The Čech description of hypercohomology, its cup product and its long exact
sequences live in the hypercohomology of the de Rham complex read in sheaves of `A`-modules. By
[Stacks, Tag 01F1] the two agree; this file transports the comparison to the de Rham complex, to
its brutal truncations and to the graded piece `Ω¹[-1]`, compatibly with the inclusions and the
projection.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamAbelianComplexPlusIso`: the de Rham complex of abelian
  sheaves is the underlying complex of the de Rham complex of sheaves of `A`-modules.
* `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationPlusIso`: the same for the brutal
  truncations.
* `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationπ`: the projection
  `σ^{≥1}Ω^• ⟶ Ω¹[-1]` of the de Rham complex of abelian sheaves.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIso`,
  `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianIso` and
  `AlgebraicGeometry.SheafOfModules.shiftedFormsOneCohomologyIso`: the transported comparisons.
* `AlgebraicGeometry.SheafOfModules.filteredFirstChernClassModule`: the Hodge-filtered first
  Chern class `γ₁(L)` of [Stacks, Tag 0FME] in the sheaf-of-modules realization.

## Main results

* `AlgebraicGeometry.SheafOfModules.truncatedDeRhamCohomologyAbelianMap_comp_iso` and
  `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationπ_map_comp_iso`: the comparisons are
  compatible with the inclusion `σ^{≥p}Ω^• ⟶ Ω^•` and the projection `σ^{≥1}Ω^• ⟶ Ω¹[-1]`.
* `AlgebraicGeometry.SheafOfModules.deRhamAbelianTruncationπ_filteredFirstChernClass`: `γ₁(L)`
  projects to `d log` of the class of `L` in `H¹(X, 𝒪_X^*)`, read in `H²(X, Ω¹[-1])`.
* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIso_deRhamFirstChernClassAbelian` and
  `AlgebraicGeometry.SheafOfModules.hypercohomologyMap_truncSC_g_filteredFirstChernClassModule`:
  the same two facts in the sheaf-of-modules realization, `c₁^{dR}(L)` being the image of
  `γ₁(L)` under the inclusion.
* `AlgebraicGeometry.SheafOfModules.rightDerived_logarithmicDifferential_classOf`: for a morphism
  of schemes, `d log` of the class of `L` is the Hodge first Chern class carried along
  `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0FME](https://stacks.math.columbia.edu/tag/0FME)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cech.Hypercohomology (truncPlus singlePlus truncSC ιTruncPlus hypercohomology
  hypercohomologyMap abelianHypercohomology realizationIsoOfIso)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-! ### The de Rham complex and its truncations -/

/-- **The de Rham complex of abelian sheaves is the underlying complex** of the de Rham complex
of sheaves of `A`-modules: extension by zero commutes with forgetting the module structure. -/
def deRhamAbelianComplexPlusIso :
    deRhamAbelianComplexPlus B D ≅
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj
        (deRhamComplexPlus (X := X) B D) :=
  ObjectProperty.isoMk _ (HomologicalComplex.mapHomologicalComplexExtendIso
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplex B D) embeddingUpNat)

/-- The identification of the de Rham complex of abelian sheaves with the underlying complex of
the de Rham complex of sheaves of `A`-modules, on complexes. -/
abbrev deRhamAbelianComplexIntIso :
    deRhamAbelianComplexInt B D ≅
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex (up ℤ)).obj
        (deRhamComplexInt (X := X) B D) :=
  HomologicalComplex.mapHomologicalComplexExtendIso
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplex B D) embeddingUpNat

/-- **The brutal truncation of the de Rham complex of abelian sheaves is the underlying complex
of the brutal truncation** of the de Rham complex of sheaves of `A`-modules. -/
def deRhamAbelianTruncationPlusIso (p : ℤ) :
    deRhamAbelianTruncationPlus B D p ≅
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj
        (truncPlus A (deRhamComplexInt (X := X) B D) p) :=
  ObjectProperty.isoMk _
    ({ hom := HomologicalComplex.stupidTruncMap (deRhamAbelianComplexIntIso B D).hom
          (embeddingUpIntGE p)
       inv := HomologicalComplex.stupidTruncMap (deRhamAbelianComplexIntIso B D).inv
          (embeddingUpIntGE p)
       hom_inv_id := by
        rw [← HomologicalComplex.stupidTruncMap_comp, Iso.hom_inv_id,
          HomologicalComplex.stupidTruncMap_id]
       inv_hom_id := by
        rw [← HomologicalComplex.stupidTruncMap_comp, Iso.inv_hom_id,
          HomologicalComplex.stupidTruncMap_id] } ≪≫
      (HomologicalComplex.mapStupidTruncGEIso
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A))
        (deRhamComplexInt (X := X) B D) p).symm)

/-- **The identification of the truncations is compatible with the inclusions** into the de Rham
complex. -/
theorem deRhamAbelianTruncationPlusIso_hom_ι (p : ℤ) :
    ιDeRhamAbelianTruncationPlus B D p ≫ (deRhamAbelianComplexPlusIso B D).hom =
      (deRhamAbelianTruncationPlusIso B D p).hom ≫
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.map
          (ιTruncPlus A (deRhamComplexPlus (X := X) B D) p) := by
  refine ObjectProperty.hom_ext _ ?_
  change HomologicalComplex.ιStupidTrunc _ _ ≫ (deRhamAbelianComplexIntIso B D).hom =
    (HomologicalComplex.stupidTruncMap (deRhamAbelianComplexIntIso B D).hom
        (embeddingUpIntGE p) ≫ inv (HomologicalComplex.mapStupidTruncGEComparison
          (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A))
            (deRhamComplexInt (X := X) B D) p)) ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex (up ℤ)).map
        (HomologicalComplex.ιStupidTrunc (deRhamComplexInt (X := X) B D) (embeddingUpIntGE p))
  have h : inv (HomologicalComplex.mapStupidTruncGEComparison
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplexInt (X := X) B D) p) ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex (up ℤ)).map
        (HomologicalComplex.ιStupidTrunc (deRhamComplexInt (X := X) B D) (embeddingUpIntGE p)) =
      HomologicalComplex.ιStupidTrunc _ (embeddingUpIntGE p) :=
    (IsIso.inv_comp_eq _).2 (HomologicalComplex.mapStupidTruncGEComparison_ι _ _ _).symm
  rw [Category.assoc, h, HomologicalComplex.stupidTruncMap_ιStupidTrunc]

/-! ### The graded piece `Ω¹[-1]` -/

/-- **The projection `σ^{≥1}Ω^• ⟶ Ω¹[-1]`** of the de Rham complex of abelian sheaves onto its
bottom term, as a morphism of bounded below complexes. -/
def deRhamAbelianTruncationπ :
    deRhamAbelianTruncationPlus B D 1 ⟶
      singleOneComplexPlus X.carrier ((deRhamAbelianComplex B D).X 1) :=
  ObjectProperty.homMk
    (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) 1 ≫
      (HomologicalComplex.single _ (up ℤ) 1).map (deRhamAbelianIntXIsoOne B D).hom)

/-- **`Ω¹[-1]` of abelian sheaves is the underlying complex of `Ω¹[-1]` of sheaves of
`A`-modules.** -/
def deRhamAbelianSingleOneIso :
    singleOneComplexPlus X.carrier ((deRhamAbelianComplex B D).X 1) ≅
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.obj
        (singlePlus A ((deRhamComplexInt (X := X) B D).X 1) 1) :=
  ObjectProperty.isoMk _
    ((HomologicalComplex.single _ (up ℤ) 1).mapIso
        ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapIso
          ((deRhamComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl).symm) ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (up ℤ) 1).app _).symm)

/-- **The identifications are compatible with the projections onto `Ω¹[-1]`.** -/
theorem deRhamAbelianTruncationπ_comp_singleOneIso :
    deRhamAbelianTruncationπ B D ≫ (deRhamAbelianSingleOneIso B D).hom =
      (deRhamAbelianTruncationPlusIso B D 1).hom ≫
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.map
          (truncSC A (deRhamComplexInt (X := X) B D) 1).g := by
  refine ObjectProperty.hom_ext _ ?_
  have hπ := HomologicalComplex.mapStupidTruncGEComparison_stupidTruncGEπ
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplexInt (X := X) B D) 1
  have hπ' : inv (HomologicalComplex.mapStupidTruncGEComparison
      (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (deRhamComplexInt (X := X) B D) 1) ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex (up ℤ)).map
        (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamComplexInt (X := X) B D) 1) =
      StacksDraft.StupidTruncation.stupidTruncGEπ _ 1 ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (up ℤ) 1).inv.app _ := by
    rw [IsIso.inv_comp_eq, reassoc_of% hπ, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have hext : (deRhamAbelianComplexIntIso B D).hom.f 1 =
      (deRhamAbelianIntXIsoOne B D).hom ≫ (_root_.SheafOfModules.toSheaf
        (underlyingRingSheaf A)).map ((deRhamComplex B D).extendXIso embeddingUpNat
          (i := 1) (i' := 1) rfl).inv :=
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ rfl
  change (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) 1 ≫
      (HomologicalComplex.single _ (up ℤ) 1).map (deRhamAbelianIntXIsoOne B D).hom) ≫
      ((HomologicalComplex.single _ (up ℤ) 1).map ((_root_.SheafOfModules.toSheaf
        (underlyingRingSheaf A)).map ((deRhamComplex B D).extendXIso embeddingUpNat
          (i := 1) (i' := 1) rfl).inv) ≫ (HomologicalComplex.singleMapHomologicalComplex
          (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)) (up ℤ) 1).inv.app _) =
    (HomologicalComplex.stupidTruncMap (deRhamAbelianComplexIntIso B D).hom
        (embeddingUpIntGE 1) ≫ inv (HomologicalComplex.mapStupidTruncGEComparison
          (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A))
            (deRhamComplexInt (X := X) B D) 1)) ≫
      ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapHomologicalComplex (up ℤ)).map
        (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamComplexInt (X := X) B D) 1)
  symm
  rw [Category.assoc, hπ', HomologicalComplex.stupidTruncMap_stupidTruncGEπ_assoc, hext]
  exact congrArg (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) 1 ≫ ·)
    ((HomologicalComplex.single (AbelianSheaf X.carrier) (up ℤ) 1).map_comp_assoc _ _ _)

/-! ### The transported comparisons -/

/-- **Relative de Rham cohomology in the abelian-sheaf realization is the hypercohomology of the
de Rham complex of sheaves of `A`-modules**, as abelian groups ([Stacks, Tag 01F1]). -/
def deRhamCohomologyAbelianIso (n : ℤ) :
    deRhamCohomologyAbelian B D n ≅
      (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (hypercohomology A (deRhamComplexPlus (X := X) B D) n) :=
  realizationIsoOfIso (baseRingedSpace A) (deRhamAbelianComplexPlusIso B D) n

/-- The hypercohomology of a brutal truncation of the de Rham complex in the two
realizations. -/
def truncatedDeRhamCohomologyAbelianIso (p n : ℤ) :
    truncatedDeRhamCohomologyAbelian B D p n ≅
      (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (hypercohomology A (truncPlus A (deRhamComplexInt (X := X) B D) p) n) :=
  realizationIsoOfIso (baseRingedSpace A) (deRhamAbelianTruncationPlusIso B D p) n

/-- The hypercohomology of `Ω¹[-1]` in the two realizations. -/
def shiftedFormsOneCohomologyIso (n : ℤ) :
    abelianHypercohomology (singleOneComplexPlus X.carrier ((deRhamAbelianComplex B D).X 1)) n ≅
      (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        (hypercohomology A (singlePlus A ((deRhamComplexInt (X := X) B D).X 1) 1) n) :=
  realizationIsoOfIso (baseRingedSpace A) (deRhamAbelianSingleOneIso B D) n

/-- **The comparisons are compatible with the inclusion of a brutal truncation.** -/
theorem truncatedDeRhamCohomologyAbelianMap_comp_iso (p n : ℤ) :
    truncatedDeRhamCohomologyAbelianMap B D p n ≫ (deRhamCohomologyAbelianIso B D n).hom =
      (truncatedDeRhamCohomologyAbelianIso B D p n).hom ≫
        (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (hypercohomologyMap A (ιTruncPlus A (deRhamComplexPlus (X := X) B D) p) n) :=
  Stacks.Cech.Hypercohomology.realizationIsoOfIso_naturality (baseRingedSpace A) _ _ _ _
    (deRhamAbelianTruncationPlusIso_hom_ι B D p) n

/-- **The comparisons are compatible with the projection onto `Ω¹[-1]`.** -/
theorem deRhamAbelianTruncationπ_map_comp_iso (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (deRhamAbelianTruncationπ B D))) ≫
        (shiftedFormsOneCohomologyIso B D n).hom =
      (truncatedDeRhamCohomologyAbelianIso B D 1 n).hom ≫
        (forget₂ (ModuleCat.{u} ((underlyingRingSheaf A).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (hypercohomologyMap A (truncSC A (deRhamComplexInt (X := X) B D) 1).g n) :=
  Stacks.Cech.Hypercohomology.realizationIsoOfIso_naturality (baseRingedSpace A) _ _ _ _
    (deRhamAbelianTruncationπ_comp_singleOneIso B D) n

/-! ### The image of the Hodge-filtered first Chern class in `Ω¹[-1]` -/

/-- A morphism of abelian sheaves placed in degree one, as a morphism of bounded below
complexes. -/
abbrev singleOneComplexPlusMap {Y : TopCat.{u}} {F G : AbelianSheaf Y} (g : F ⟶ G) :
    singleOneComplexPlus Y F ⟶ singleOneComplexPlus Y G :=
  ObjectProperty.homMk ((CochainComplex.singleFunctor _ 1).map g)

/-- **`d log : 𝒪_X^*[-1] ⟶ σ^{≥1}Ω^•` followed by the projection onto `Ω¹[-1]` is `d log` placed
in degree one.** -/
theorem filteredLogarithmicDifferentialComplexMapPlus_π :
    filteredLogarithmicDifferentialComplexMapPlus B D ≫ deRhamAbelianTruncationπ B D =
      singleOneComplexPlusMap (logarithmicDifferentialAbelianSheafHom B D) := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.to_single_hom_ext ?_)
  have hι := congrArg (fun ψ => ψ.f 1) (filteredLogarithmicDifferentialComplexMap_ι B D)
  simp only [HomologicalComplex.comp_f,
    StacksDraft.StupidTruncation.ιStupidTruncGE_f _ 1 1 le_rfl] at hι
  change (filteredLogarithmicDifferentialComplexMap B D).f 1 ≫
      (StacksDraft.StupidTruncation.stupidTruncGEπ (deRhamAbelianComplexInt B D) 1 ≫
        (HomologicalComplex.single _ (up ℤ) 1).map (deRhamAbelianIntXIsoOne B D).hom).f 1 =
    ((HomologicalComplex.single _ (up ℤ) 1).map (logarithmicDifferentialAbelianSheafHom B D)).f 1
  rw [HomologicalComplex.comp_f, StacksDraft.StupidTruncation.stupidTruncGEπ_f, ← Category.assoc,
    ← Category.assoc, hι, logarithmicDifferentialComplexMap, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
  simp only [logarithmicDifferentialAbelian, Category.assoc, Iso.inv_hom_id_assoc]

/-- The identification `H¹(X, F) ≅ H²(X, F[-1])` is natural in the abelian sheaf. -/
theorem sheafCohomologyOneIsoShiftedCohomologyTwo_naturality {Y : TopCat.{u}}
    {F G : AbelianSheaf Y} (g : F ⟶ G) :
    ((sectionsFunctor Y ⊤).rightDerived 1).map g ≫
        (sheafCohomologyOneIsoShiftedCohomologyTwo Y G).hom =
      (sheafCohomologyOneIsoShiftedCohomologyTwo Y F).hom ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
          ((sectionsFunctor Y ⊤).rightDerivedFunctorPlus.map
            (DerivedCategory.Plus.Q.map (singleOneComplexPlusMap g))) := by
  let γ : (sectionsFunctor Y ⊤).rightDerived 1 ≅
      DerivedCategory.Plus.singleFunctor (AbelianSheaf Y) 1 ⋙
        (sectionsFunctor Y ⊤).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} (1 + 1) :=
    Stacks.DerivedIndexing.rightDerivedIso (sectionsFunctor Y ⊤) 1 ≪≫
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorShiftIso
        (sectionsFunctor Y ⊤).rightDerivedFunctorPlus 1 1).symm
  exact γ.hom.naturality g

section Classes

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- **The Hodge-filtered first Chern class projects to the shifted logarithmic differential**: the
image of `γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` under `σ^{≥1}Ω^• ⟶ Ω¹[-1]` is the image of the class of `L`
in `H¹(X, 𝒪_X^*)` under `d log`, read in `H²(X, Ω¹[-1]) = H¹(X, Ω¹)`. This is the second
assertion of [Stacks, Tag 0FME]. -/
theorem deRhamAbelianTruncationπ_filteredFirstChernClass
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
        ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map (deRhamAbelianTruncationπ B D)))).hom
        (filteredFirstChernClass B D c) =
      (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom.hom
        ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
          (logarithmicDifferentialAbelianSheafHom B D)).hom
          ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm c)) := by
  let M : ∀ {K L : CochainComplex.Plus (AbelianSheaf X.carrier)}, (K ⟶ L) → _ := fun f =>
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} 2).map
      ((sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map f))
  have hcomp : M (filteredLogarithmicDifferentialComplexMapPlus B D) ≫
      M (deRhamAbelianTruncationπ B D) =
      M (singleOneComplexPlusMap (logarithmicDifferentialAbelianSheafHom B D)) := by
    simp only [M, ← Functor.map_comp, filteredLogarithmicDifferentialComplexMapPlus_π]
  have key : (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier (unitsAbelianSheaf X)).hom ≫
      M (filteredLogarithmicDifferentialComplexMapPlus B D) ≫ M (deRhamAbelianTruncationπ B D) =
      ((sectionsFunctor X.carrier ⊤).rightDerived 1).map
          (logarithmicDifferentialAbelianSheafHom B D) ≫
        (sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom := by
    rw [hcomp, sheafCohomologyOneIsoShiftedCohomologyTwo_naturality]
  exact ConcreteCategory.congr_hom key _

/-- **The Hodge-filtered first Chern class in the sheaf-of-modules realization**: the class
`γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` of [Stacks, Tag 0FME], carried to the hypercohomology of the brutal
truncation of the de Rham complex of sheaves of `A`-modules. -/
def filteredFirstChernClassModule
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    hypercohomology A (truncPlus A (deRhamComplexInt (X := X) B D) 1) 2 :=
  (truncatedDeRhamCohomologyAbelianIso B D 1 2).hom.hom (filteredFirstChernClass B D c)

/-- **The de Rham first Chern class, carried to the sheaf-of-modules realization, is the image of
the Hodge-filtered one** under the inclusion `σ^{≥1}Ω^• ⟶ Ω^•`. -/
theorem deRhamCohomologyAbelianIso_deRhamFirstChernClassAbelian
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (deRhamCohomologyAbelianIso B D 2).hom.hom (deRhamFirstChernClassAbelian B D c) =
      (hypercohomologyMap A (ιTruncPlus A (deRhamComplexPlus (X := X) B D) 1) 2).hom
        (filteredFirstChernClassModule B D c) := by
  rw [deRhamFirstChernClassAbelian_eq]
  exact ConcreteCategory.congr_hom (truncatedDeRhamCohomologyAbelianMap_comp_iso B D 1 2) _

/-- **The Hodge-filtered first Chern class in the sheaf-of-modules realization projects to the
shifted logarithmic differential** of the class of the invertible module in `H¹(X, 𝒪_X^*)`,
under `σ^{≥1}Ω^• ⟶ Ω¹[-1]`. -/
theorem hypercohomologyMap_truncSC_g_filteredFirstChernClassModule
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    (hypercohomologyMap A (truncSC A (deRhamComplexInt (X := X) B D) 1).g 2).hom
        (filteredFirstChernClassModule B D c) =
      (shiftedFormsOneCohomologyIso B D 2).hom.hom
        ((sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom.hom
          ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
            (logarithmicDifferentialAbelianSheafHom B D)).hom
            ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm c))) := by
  rw [← deRhamAbelianTruncationπ_filteredFirstChernClass]
  exact (ConcreteCategory.congr_hom (deRhamAbelianTruncationπ_map_comp_iso B D 2) _).symm

end Classes

/-! ### Morphisms of schemes -/

/-- **For a morphism of schemes, logarithmic differentiation into the de Rham complex is
logarithmic differentiation into `Ω_{X/S}` followed by the degree-one generator**
`Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`, as morphisms of sheaves of abelian groups. -/
theorem logarithmicDifferentialSheafHom_deRhamAlgebras {Y S : Scheme.{u}} (p : Y ⟶ S) :
    logarithmicDifferentialSheafHom (Scheme.Hom.deRhamAlgebras p) =
      Scheme.Hom.logarithmicDifferentialSheafHom p ≫
        (_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map
          (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)) := by
  apply Sheaf.hom_ext
  ext U s
  obtain ⟨u, rfl⟩ : ∃ u : (Y.sheaf.obj.obj U)ˣ, Additive.ofMul u = s := ⟨s, rfl⟩
  change logarithmicDifferential (Scheme.Hom.deRhamAlgebras p) U u = _
  change _ = ((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)).val.app
    U).hom ((Scheme.Hom.logarithmicDifferentialSheafHom p).hom.app U (Additive.ofMul u))
  rw [Scheme.Hom.logarithmicDifferentialSheafHom_app]
  exact ((((Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)).val.app
    U).hom.map_smul _ _)).symm

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup in
/-- **The two identifications of Tag 09NU agree on Picard classes**: for an invertible module on
a scheme, the identification for ringed spaces with local stalks and the one over
`Stacks.Picard.ofScheme` both send its class to the first-cohomology class of its torsor of
generators. -/
theorem h1UnitsAddEquivPicardGroup_symm_classOf_eq {Y : Scheme.{u}} (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).property L) :
    (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup Y.toRingedSpace).symm
        (Stacks.SheafOfModules.Picard.classOf Y.toRingedSpace.sheaf.obj
          (structureSheaf Y.toRingedSpace.sheaf).property L hL) =
      (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard Y).symm
        (Stacks.SheafOfModules.picardClass Y.toRingedSpace.presheaf
          (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL) := by
  exact (Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf
    Y.toRingedSpace L hL).trans
      (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_symm_classOf Y L hL).symm

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup in
/-- **For a morphism of schemes, the class entering the Hodge-filtered first Chern class is the
Hodge first Chern class**: the image of the class of an invertible module `L` in
`H¹(X, 𝒪_X^*)` under `d log : 𝒪_X^* ⟶ Ω¹` of the de Rham complex is the Hodge first Chern class
`c₁^{Hodge}(L) ∈ H¹(X, Ω_{X/S})` of [Stacks, Tag 0FLE] carried along `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`. -/
theorem rightDerived_logarithmicDifferential_classOf {Y S : Scheme.{u}} (p : Y ⟶ S)
    (D : DeRhamDifferential (Scheme.Hom.deRhamAlgebras p)) (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).property L) :
    (((sectionsFunctor Y.carrier ⊤).rightDerived 1).map
        (logarithmicDifferentialAbelianSheafHom (Scheme.Hom.deRhamAlgebras p) D)).hom
        ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup Y.toRingedSpace).symm
          (Stacks.SheafOfModules.Picard.classOf Y.toRingedSpace.sheaf.obj
            (structureSheaf Y.toRingedSpace.sheaf).property L hL)) =
      (((sectionsFunctor Y.carrier ⊤).rightDerived 1).map
        ((_root_.SheafOfModules.toSheaf Y.ringCatSheaf).map
          (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials p)))).hom
        (Scheme.Hom.hodgeFirstChernClass p
          (Stacks.SheafOfModules.picardClass Y.toRingedSpace.presheaf
            (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) L hL)) := by
  rw [h1UnitsAddEquivPicardGroup_symm_classOf_eq]
  change (((sectionsFunctor Y.carrier ⊤).rightDerived 1).map
      (logarithmicDifferentialSheafHom (Scheme.Hom.deRhamAlgebras p))).hom _ = _
  rw [logarithmicDifferentialSheafHom_deRhamAlgebras]
  exact (ConcreteCategory.congr_hom (Functor.map_comp _ _ _) _).trans rfl

end AlgebraicGeometry.SheafOfModules

end
