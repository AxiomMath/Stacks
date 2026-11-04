module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingHomEquivNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurrySourceNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDualGlobalFunctoriality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomRepresentativePair
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.IntoAKInjectiveComplexGlobalValue

/-!
# The tensor–internal-Hom bijection on representatives

Let `(C, O)` be a ringed site, `A`, `B` K-flat complexes of `O`-modules, `I` a K-injective
complex and `T = Tot(A ⊗_O B)`. A morphism of complexes `f : A ⟶ SheafHom(B, I)` and a morphism
of complexes `g : T ⟶ I` which correspond under the currying isomorphism of Stacks 0A90 on
global sections give morphisms of `D(O)` which correspond under the tensor–internal-Hom
bijection of Stacks 08J8:

`Q(f) ↦ (Q A ⊗^𝐋 Q B ≅ Q T) ≫ Q(g)`.

## Main results

* `AlgebraicGeometry.RingedSite.derivedHomGlobalSectionsComparison_naturality_map`: the
  identification of the degree-zero global hypercohomology of a derived internal Hom with the
  cohomology of global sections of a K-injective internal Hom complex is natural for every
  morphism of complexes between two such internal Hom complexes.
* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_model`: the bijection of Stacks 08J8 on
  representatives.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- **The comparison of global hypercohomology with global sections is natural for any morphism
of K-injective internal Hom complexes.** -/
theorem derivedHomGlobalSectionsComparison_naturality_map
    {A I A' I' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [I'.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective]
    [((sheafHomComplex X A' I').obj).IsKInjective]
    (φ : (sheafHomComplex X A I).obj ⟶ (sheafHomComplex X A' I').obj)
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj I))) : Type u)) :
    (derivedHomGlobalSectionsComparison X A' I').hom
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map ((derivedSheafHomComparison X A I).hom ≫
            DerivedCategory.Q.map φ ≫ (derivedSheafHomComparison X A' I').inv)) x) =
      HomologicalComplex.homologyMap (globalSectionsComplexMap X φ) 0
        ((derivedHomGlobalSectionsComparison X A I).hom x) := by
  have hgs : (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X φ) =
      (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv := by
    have h : DerivedCategory.Q.map (globalSectionsComplexMap X φ) ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).hom =
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).hom ≫
          (derivedModuleGlobalSections X).map (DerivedCategory.Q.map φ) :=
      globalSectionsKInjectiveIso_naturality X φ
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hD : (derivedModuleGlobalSections X).map ((derivedSheafHomComparison X A I).hom ≫
            DerivedCategory.Q.map φ ≫ (derivedSheafHomComparison X A' I').inv) ≫
        ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv) =
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
          (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        DerivedCategory.Q.map (globalSectionsComplexMap X φ) := by
    rw [Category.assoc, hgs]
    simp only [Functor.map_comp, Category.assoc, Iso.map_inv_hom_id_assoc]
  have hD' : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map ((derivedSheafHomComparison X A I).hom ≫
            DerivedCategory.Q.map φ ≫ (derivedSheafHomComparison X A' I').inv)) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A' I').hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A' I').obj)).inv) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
            (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          (DerivedCategory.Q.map (globalSectionsComplexMap X φ)) := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hD]
  have e1 := ConcreteCategory.congr_hom hD' x
  have e2 := ConcreteCategory.congr_hom
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.naturality
      (globalSectionsComplexMap X φ))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map (derivedSheafHomComparison X A I).hom ≫
        (globalSectionsKInjectiveIso X ((sheafHomComplex X A I).obj)).inv) x)
  rw [derivedHomGlobalSectionsComparison_hom, derivedHomGlobalSectionsComparison_hom]
  exact (congrArg (fun z => (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u} 0).hom.app
    (globalSectionsComplex X (sheafHomComplex X A' I').obj) z) e1).trans e2

/-- The derived currying isomorphism of Stacks 08J9 at classes of complexes, with the target
`RSheafHom(QB, QI)` read as the class of `SheafHom(B, I)`: the class of the currying isomorphism
of Stacks 0A90, followed by the K-flat comparison of the derived tensor product. -/
theorem derivedCurryIso_hom_model
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective] :
    haveI := isKInjective_sheafHomComplex_of_isKFlat X B I hB
    ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
        (derivedSheafHomComparison X B I).inv ≫
      (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj I)).hom =
    (derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
      DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
        (derivedSheafHomComparison X
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv ≫
          ((derivedSheafHomBifunctor X).map
            ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B
              hB).hom.op).app (DerivedCategory.Q.obj I) := by
  have := isKInjective_sheafHomComplex_of_isKFlat X B I hB
  rw [derivedCurryIso_eq_representativeCurryingIso X A B I hB]
  show ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
        (derivedSheafHomComparison X B I).inv ≫
      ((((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).map
          (derivedSheafHomComparison X B I).hom ≫
          (derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom) ≫
        DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
          ((derivedSheafHomComparison X
              (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv ≫
            ((derivedSheafHomBifunctor X).map
              ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B
                hB).hom.op).app (DerivedCategory.Q.obj I))) = _
  rw [Category.assoc, Iso.map_inv_hom_id_assoc]

/-- `derivedCurryIso_hom_model` on degree-zero global hypercohomology. -/
theorem derivedCurryIso_globalMap_model
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) [I.IsKInjective]
    (x₀ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj A))).obj
          (DerivedCategory.Q.obj (sheafHomComplex X B I).obj))) : Type u)) :
    haveI := isKInjective_sheafHomComplex_of_isKFlat X B I hB
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj I)).hom)
        (derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj A))
          (derivedSheafHomComparison X B I).inv x₀) =
      derivedHomGlobalMap X
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom
          (𝟙 (DerivedCategory.Q.obj I))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
              DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
                (derivedSheafHomComparison X
                  (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv))
          x₀) := by
  have := isKInjective_sheafHomComplex_of_isKFlat X B I hB
  have h := derivedCurryIso_hom_model X A B I hB
  have h1 : derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj A))
        (derivedSheafHomComparison X B I).inv ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedCurryIso X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
            (DerivedCategory.Q.obj I)).hom) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            ((derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
              DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
                (derivedSheafHomComparison X
                  (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv)) ≫
        derivedHomGlobalMap X
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom
          (𝟙 (DerivedCategory.Q.obj I)) := by
    dsimp only [derivedHomGlobalMap]
    simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
      Category.comp_id]
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h]
    simp only [Category.assoc]
  exact ConcreteCategory.congr_hom h1 x₀

/-- Every class of a morphism of complexes `f : A ⟶ I` with `A` K-flat and `I` K-injective is
the image of a derived global class under the comparison, which the identification of Stacks
08JA sends to `Q(f)`. -/
private theorem exists_comparison_eq_and_globalSectionsEquiv_eq
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] (f : A ⟶ I) :
    ∃ x, (derivedHomGlobalSectionsComparison X A I).hom x = globalHomologyClass X A I f ∧
      derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj I) x =
        DerivedCategory.Q.map f := by
  refine ⟨(derivedHomGlobalSectionsComparison X A I).inv (globalHomologyClass X A I f),
    Iso.inv_hom_id_apply _ _, ?_⟩
  rw [derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat X A I hA]
  change derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I _ = _
  rw [derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_eq_comparison, Iso.inv_hom_id_apply,
    sheafHomGlobalHomologyEquivDerivedCategoryHom_globalHomologyClass]

/-- **The tensor–internal-Hom bijection of Stacks 08J8 on representatives.** Let `A`, `B` be
K-flat complexes with `T = Tot(A ⊗_O B)` K-flat, `I` a K-injective complex, and let
`f : A ⟶ SheafHom(B, I)` and `g : T ⟶ I` be morphisms of complexes whose classes in the global
sections correspond under the currying isomorphism of Stacks 0A90. Then the bijection carries the
class of `f` to the class of `g`, read through the K-flat comparison `Q A ⊗^𝐋 Q B ≅ Q T`. -/
theorem derivedCurryHomEquiv_model
    (A B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hT : Stacks.SheafOfModules.IsKFlat X.O
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B))
    [I.IsKInjective]
    (f : A ⟶ (sheafHomComplex X B I).obj)
    (g : (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) ⟶ I)
    (hfg : HomologicalComplex.homologyMap
        (globalSectionsComplexMap X (sheafHomTensorCurryIso X A B I).hom) 0
          (globalHomologyClass X A (sheafHomComplex X B I).obj f) =
      globalHomologyClass X _ I g) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
        (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X B I).inv) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A B hB).hom ≫
        DerivedCategory.Q.map g := by
  have hH : ((sheafHomComplex X B I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X B I hB
  have : ((sheafHomComplex X A (sheafHomComplex X B I).obj).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X A _ hA
  have : ((sheafHomComplex X
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).obj).IsKInjective :=
    isKInjective_sheafHomComplex_of_isKFlat X _ I hT
  obtain ⟨x₀, hx₀, h₀⟩ := exists_comparison_eq_and_globalSectionsEquiv_eq X A _ hA f
  have h₁ : derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj A)
      (((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj B))).obj
        (DerivedCategory.Q.obj I))
      (derivedHomGlobalMap X (𝟙 (DerivedCategory.Q.obj A))
        (derivedSheafHomComparison X B I).inv x₀) =
      DerivedCategory.Q.map f ≫ (derivedSheafHomComparison X B I).inv := by
    dsimp only [derivedHomGlobalMap]
    rw [derivedSheafHomGlobalSectionsEquiv_naturality, h₀, Category.id_comp]
  obtain ⟨y, hy', hy⟩ := exists_comparison_eq_and_globalSectionsEquiv_eq X _ I hT g
  have e1 : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        ((derivedSheafHomComparison X A (sheafHomComplex X B I).obj).hom ≫
          DerivedCategory.Q.map (sheafHomTensorCurryIso X A B I).hom ≫
            (derivedSheafHomComparison X
              (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj B) I).inv)) x₀ = y := by
    have hn := derivedHomGlobalSectionsComparison_naturality_map X
      (sheafHomTensorCurryIso X A B I).hom x₀
    rw [hx₀, hfg, ← hy'] at hn
    exact (ConcreteCategory.bijective_of_isIso _).1 hn
  rw [← h₁, derivedCurryHomEquiv_globalSections, derivedCurryGlobalEquiv_apply,
    derivedCurryIso_globalMap_model X A B I hB x₀, e1,
    derivedSheafHomGlobalSectionsEquiv_naturality_source, hy]

/-- The bijection of Stacks 08J8 is natural in the source `U` and in `K` and `M`, with the four
objects explicit. -/
theorem derivedCurryHomEquiv_comp_map
    (U U' K K' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (k : U' ⟶ U) (l : K' ⟶ K) (m : M ⟶ M')
    (θ : U ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj M) :
    derivedCurryHomEquiv X U' K' M'
        (k ≫ θ ≫ (((derivedSheafHomBifunctor X).map l.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op K')).map m)) =
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app K' ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj U).map l) ≫
        derivedCurryHomEquiv X U K M θ ≫ m :=
  derivedCurryHomEquiv_naturality X k l m θ

/-- `derivedCurryHomEquiv_comp_map` with an identity in the source variable. -/
theorem derivedCurryHomEquiv_comp_map_of_id
    (U K K' M M' :
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (l : K' ⟶ K) (m : M ⟶ M') (θ : U ⟶ ((derivedSheafHomBifunctor X).obj (op K)).obj M) :
    derivedCurryHomEquiv X U K' M'
        (θ ≫ (((derivedSheafHomBifunctor X).map l.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op K')).map m)) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj U).map l ≫
        derivedCurryHomEquiv X U K M θ ≫ m := by
  simpa only [Category.id_comp, CategoryTheory.Functor.map_id, NatTrans.id_app] using
    derivedCurryHomEquiv_comp_map X U U K K' M M' (𝟙 U) l m θ

end AlgebraicGeometry.RingedSite

end
