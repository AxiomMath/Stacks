module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.RealizationChernClass
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# First cohomology of `Ω¹` as the hypercohomology of `Ω¹[-1]`

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω¹` be the sheaf of relative differential `1`-forms, read as a sheaf of `A`-modules. The first
cohomology `H¹(X, Ω¹)` of its underlying abelian sheaf is identified with the degree-two
hypercohomology `H²(X, Ω¹[-1])` of `Ω¹` placed in degree one, computed in sheaves of
`A`-modules: first by the degree shift `H¹(X, F) ≅ H²(X, F[-1])` for abelian sheaves, then by the
comparison of [Stacks, Tag 01F1] between abelian sheaves and sheaves of `A`-modules. The
identification is natural in endomorphisms of `Ω¹` as a sheaf of `A`-modules.

This is the identification under which the projection of the Hodge-filtered first Chern class
`γ₁(L) ∈ H²(X, σ^{≥1}Ω^•)` onto `H²(X, Ω¹[-1])` is the Hodge first Chern class of `L`
([Stacks, Remark 0FME]).

## Main definitions

* `AlgebraicGeometry.SheafOfModules.shiftedFormsOneComparison`: the identification
  `H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])`, as an additive equivalence.

## Main results

* `AlgebraicGeometry.SheafOfModules.shiftedFormsOneComparison_naturality`: naturality in an
  endomorphism of `Ω¹`.
* `AlgebraicGeometry.SheafOfModules.hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule`:
  the projection of `γ₁(L)` onto `H²(X, Ω¹[-1])` is the logarithmic differential of the class of
  `L`.

## References

* [Stacks Project, Remark 0FME](https://stacks.math.columbia.edu/tag/0FME)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cech.Hypercohomology

universe u

/-- **Transport of an endomorphism of a single complex across an additive functor.** For an
additive functor `T`, an isomorphism `e : N ≅ M` and `f : M ⟶ M`, the map induced by `T(f)` on the
single complex `T(M)[-1]`, followed by the identification `T(M)[-1] ≅ T(N[-1])` along `e`, is that
identification followed by the image under `T` of the map induced by `e ∘ f ∘ e⁻¹` on `N[-1]`. -/
theorem HomologicalComplex.single_map_comp_singleMapHomologicalComplex_inv {C D : Type*}
    [Category* C] [Category* D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    [HasZeroObject D] (T : C ⥤ D) [T.Additive] {M N : C} (e : N ≅ M) (f : M ⟶ M) :
    (HomologicalComplex.single D (up ℤ) 1).map (T.map f) ≫
        ((HomologicalComplex.single D (up ℤ) 1).map (T.map e.inv) ≫
          (HomologicalComplex.singleMapHomologicalComplex T (up ℤ) 1).inv.app N) =
      ((HomologicalComplex.single D (up ℤ) 1).map (T.map e.inv) ≫
          (HomologicalComplex.singleMapHomologicalComplex T (up ℤ) 1).inv.app N) ≫
        (T.mapHomologicalComplex (up ℤ)).map
          ((HomologicalComplex.single C (up ℤ) 1).map (e.hom ≫ f ≫ e.inv)) := by
  have key := (HomologicalComplex.singleMapHomologicalComplex T (up ℤ) 1).inv.naturality
    (e.hom ≫ f ≫ e.inv)
  dsimp only [Functor.comp_map] at key
  rw [Category.assoc, ← key, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_assoc]

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The identification `H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])`**: the degree shift for abelian sheaves
followed by the comparison of Tag 01F1 with the hypercohomology of `Ω¹[-1]` computed in sheaves of
`A`-modules. -/
def shiftedFormsOneComparison :
    ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj ((deRhamAbelianComplex B D).X 1) ≃+
      hypercohomology A (singlePlus A ((deRhamComplexInt (X := X) B D).X 1) 1) 2 :=
  ((sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier ((deRhamAbelianComplex B D).X 1)) ≪≫
    shiftedFormsOneCohomologyIso B D 2).addCommGroupIsoToAddEquiv

/-- The identification on an element. -/
theorem shiftedFormsOneComparison_apply
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj ((deRhamAbelianComplex B D).X 1)) :
    shiftedFormsOneComparison B D x =
      (shiftedFormsOneCohomologyIso B D 2).hom.hom
        ((sheafCohomologyOneIsoShiftedCohomologyTwo X.carrier
          ((deRhamAbelianComplex B D).X 1)).hom.hom x) :=
  rfl

/-- An endomorphism of `Ω¹` read in the degree-one term of the de Rham complex extended by zero. -/
def formsOneIntMap (f : (deRhamComplex B D).X 1 ⟶ (deRhamComplex B D).X 1) :
    (deRhamComplexInt (X := X) B D).X 1 ⟶ (deRhamComplexInt (X := X) B D).X 1 :=
  ((deRhamComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl).hom ≫ f ≫
    ((deRhamComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl).inv

/-- The identification of `Ω¹[-1]` of abelian sheaves with the underlying complex of `Ω¹[-1]` of
sheaves of `A`-modules is natural in endomorphisms of `Ω¹`. -/
theorem deRhamAbelianSingleOneIso_naturality
    (f : (deRhamComplex B D).X 1 ⟶ (deRhamComplex B D).X 1) :
    singleOneComplexPlusMap ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).map f) ≫
        (deRhamAbelianSingleOneIso B D).hom =
      (deRhamAbelianSingleOneIso B D).hom ≫
        (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).mapCochainComplexPlus.map
          (singlePlusMapAt A (formsOneIntMap B D f) 1) := by
  refine ObjectProperty.hom_ext _ ?_
  exact HomologicalComplex.single_map_comp_singleMapHomologicalComplex_inv
    (_root_.SheafOfModules.toSheaf (underlyingRingSheaf A))
    ((deRhamComplex B D).extendXIso embeddingUpNat (i := 1) (i' := 1) rfl) f

/-- **The identification `H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])` is natural in endomorphisms of `Ω¹`** as a
sheaf of `A`-modules. -/
theorem shiftedFormsOneComparison_naturality
    (f : (deRhamComplex B D).X 1 ⟶ (deRhamComplex B D).X 1)
    (x : ((sectionsFunctor X.carrier ⊤).rightDerived 1).obj ((deRhamAbelianComplex B D).X 1)) :
    shiftedFormsOneComparison B D
        ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
          ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).map f)).hom x) =
      hypercohomologyMap A (singlePlusMapAt A (formsOneIntMap B D f) 1) 2
        (shiftedFormsOneComparison B D x) := by
  have hshift := ConcreteCategory.congr_hom (sheafCohomologyOneIsoShiftedCohomologyTwo_naturality
    ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).map f)) x
  have hreal := realizationIsoOfIso_naturality (baseRingedSpace A) (deRhamAbelianSingleOneIso B D)
    (deRhamAbelianSingleOneIso B D)
    (singleOneComplexPlusMap ((_root_.SheafOfModules.toSheaf (underlyingRingSheaf A)).map f))
    (singlePlusMapAt A (formsOneIntMap B D f) 1) (deRhamAbelianSingleOneIso_naturality B D f) 2
  refine (congrArg (fun z => (shiftedFormsOneCohomologyIso B D 2).hom.hom z) hshift).trans ?_
  exact ((ConcreteCategory.comp_apply _ _ _).symm.trans
    ((ConcreteCategory.congr_hom hreal _).trans (ConcreteCategory.comp_apply _ _ _)))

section Classes

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

attribute [local instance] Stacks.Cohomology.Generators.picardGroupAddCommGroup

/-- **The projection of the Hodge-filtered first Chern class onto `H²(X, Ω¹[-1])` is the
logarithmic differential of the class of `L`** in `H¹(X, Ω¹)`, under the identification
`H¹(X, Ω¹) ≅ H²(X, Ω¹[-1])` ([Stacks, Remark 0FME]). -/
theorem hypercohomologyMap_truncPlusπ_filteredFirstChernClassModule
    (c : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    hypercohomologyMap A (truncPlusπ (deRhamComplexInt (X := X) B D) 1) 2
        (filteredFirstChernClassModule B D c) =
      shiftedFormsOneComparison B D
        ((((sectionsFunctor X.carrier ⊤).rightDerived 1).map
          (logarithmicDifferentialAbelianSheafHom B D)).hom
          ((Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup X).symm c)) :=
  hypercohomologyMap_truncSC_g_filteredFirstChernClassModule B D c

end Classes

end AlgebraicGeometry.SheafOfModules

end
