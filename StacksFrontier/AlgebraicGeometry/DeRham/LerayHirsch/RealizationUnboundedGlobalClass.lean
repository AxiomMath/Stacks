module

public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-!
# The realization comparison with the unbounded model, on classes of global cocycles

Let `V` be a ringed space and `N` a bounded below complex of `𝒪_V`-modules. By [Stacks, Tag 01F1]
the hypercohomology of the underlying complex of abelian sheaves is the hypercohomology computed
in `𝒪_V`-modules; `Stacks.Cech.Hypercohomology.realizationUnbounded` is this comparison with the
unbounded model `RΓ(V, -)` of derived global sections in modules, in which the Leray
identification of [Stacks, Tag 0D5W] and the classes of global cocycles
(`Stacks.Cohomology.DerivedGlobalCupProduct.globalClass`) live. It sends the class of a global
cocycle of the underlying complex of abelian sheaves to the class of the same section
(`realizationUnbounded_abelianGlobalClass`), and it is natural in the complex.

## Main definitions

* `Stacks.Cech.Hypercohomology.realizationUnbounded`: the comparison of [Stacks, Tag 01F1] with the
  unbounded model of derived global sections.
* `Stacks.Cech.Hypercohomology.abelianGlobalClass`: the class in abelian hypercohomology of a
  global cocycle.

## Main results

* `Stacks.Cech.Hypercohomology.unit_comp_realization`: the realization comparison against the
  derived-functor units.
* `Stacks.Cech.Hypercohomology.homologyπ_comp_realizationUnbounded`: the same on cohomology.
* `Stacks.Cech.Hypercohomology.realizationUnbounded_abelianGlobalClass`: the comparison on classes
  of global cocycles.
* `Stacks.Cech.Hypercohomology.realizationUnbounded_naturality`: it is natural in the complex.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray

universe u

namespace Stacks.Cech.Hypercohomology

/-! ### Identities for an exact functor between abelian categories -/

section Generic

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Two factorizations of one isomorphism, rearranged. -/
private theorem hom_comp_inv_eq {C : Type*} [Category* C] {a b c d : C} (x : a ≅ b) (y : b ≅ d)
    (z : a ⟶ c) (w : c ≅ d) (h : x.hom ≫ y.hom = z ≫ w.hom) : y.hom ≫ w.inv = x.inv ≫ z := by
  rw [Iso.comp_inv_eq, Category.assoc, ← h, Iso.inv_hom_id_assoc]

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (T : A ⥤ B) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]

/-- The factorization of the induced functor through the localization, read in the unbounded
derived category against the localization comparisons. -/
private theorem ι_map_qcq_comp_mapDerivedCategoryFactors_inv [EnoughInjectives A]
    (P : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((DerivedCategory.Plus.quotientCompQhIso B).hom.app
        (T.mapCochainComplexPlus.obj P)) ≫ T.mapDerivedCategoryFactors.inv.app P.obj =
      DerivedCategory.Plus.ι.map
        (T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj P) ≫
          T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app P)) := by
  have hz : DerivedCategory.Plus.ι.map
      (T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app P)) =
      T.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app P.obj) :=
    congrArg T.mapDerivedCategory.map (Stacks.DerivedIndexing.ι_map_quotientCompQhIso_hom_app P)
  have hf : DerivedCategory.Plus.ι.map
      (T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj P)) =
      T.mapDerivedCategoryFactorsh.inv.app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.obj) := rfl
  have hk := hom_comp_inv_eq (T.mapDerivedCategoryFactorsh.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P.obj))
    ((DerivedCategory.quotientCompQhIso B).app
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj))
    (T.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso A).hom.app P.obj))
    (T.mapDerivedCategoryFactors.app P.obj)
    (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso T P.obj)
  rw [DerivedCategory.Plus.ι.map_comp, hf, hz,
    Stacks.DerivedIndexing.ι_map_quotientCompQhIso_hom_app]
  exact hk

/-- An identification `e` of the localization of `T(N)` with the induced functor at the
localization of `N`, compatible with the factorizations, followed by the comparison of the induced
functor with the right derived functor, is the unit of the right derived functor. -/
private theorem qcq_comp_comp_rdIso_inv [EnoughInjectives A] (N : CochainComplex.Plus A)
    (e : DerivedCategory.Plus.Q.obj (T.mapCochainComplexPlus.obj N) ⟶
      T.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Q.obj N))
    (he : (DerivedCategory.Plus.quotientCompQhIso B).hom.app (T.mapCochainComplexPlus.obj N) ≫ e =
      T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj N) ≫
        T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app N)) :
    (DerivedCategory.Plus.quotientCompQhIso B).hom.app (T.mapCochainComplexPlus.obj N) ≫ e ≫
        T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app (DerivedCategory.Plus.Q.obj N) =
      T.rightDerivedFunctorPlusUnith.app ((HomotopyCategory.Plus.quotient A).obj N) ≫
        T.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app N) := by
  have h₂ := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app T
    ((HomotopyCategory.Plus.quotient A).obj N)
  have h₂' := (Iso.eq_comp_inv (T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app
    (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj N)))).2 h₂
  have h₁ := T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.naturality
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app N)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) he).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h₂'.symm)))))

/-- **The unit of an exact functor, read in the unbounded derived category**: followed by the
comparison of the right derived functor with the induced functor, it is the inverse of the
factorization of the induced functor through the localization. -/
private theorem ι_map_unit_comp_rdIso_hom [EnoughInjectives A] (P : CochainComplex.Plus A) :
    DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit T).app P ≫
        T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app (DerivedCategory.Plus.Q.obj P)) =
      T.mapDerivedCategoryFactors.inv.app P.obj := by
  have h₁ := T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
    ((DerivedCategory.Plus.quotientCompQhIso A).hom.app P)
  have h₂ := Functor.unit_comp_rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_app T
    ((HomotopyCategory.Plus.quotient A).obj P)
  have e : (Functor.mapCochainComplexPlusDerivedUnit T).app P ≫
        T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app (DerivedCategory.Plus.Q.obj P) =
      (DerivedCategory.Plus.quotientCompQhIso B).inv.app (T.mapCochainComplexPlus.obj P) ≫
        T.mapDerivedCategoryPlusFactorsh.inv.app ((HomotopyCategory.Plus.quotient A).obj P) ≫
        T.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.quotientCompQhIso A).hom.app P) :=
    (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ _) h₂)))))
  rw [e, DerivedCategory.Plus.ι.map_comp]
  refine (congrArg (_ ≫ ·) (ι_map_qcq_comp_mapDerivedCategoryFactors_inv T P).symm).trans ?_
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **An exact functor carries the class of a cycle to the class of its image**, through the
comparison of the right derived functor with the induced functor and the commutation of the
induced functor with cohomology. -/
private theorem homologyπ_comp_unit_comp_mapHomologyIso [EnoughInjectives A]
    (P : CochainComplex.Plus A) (n : ℤ) :
    (T.mapCochainComplexPlus.obj P).obj.homologyπ n ≫
        (DerivedCategory.homologyFunctorFactors B n).inv.app (T.mapCochainComplexPlus.obj P).obj ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          ((Functor.mapCochainComplexPlusDerivedUnit T).app P ≫
            T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
              (DerivedCategory.Plus.Q.obj P)) ≫
        (T.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj P.obj) =
      ((P.obj.sc n).mapCyclesIso T).hom ≫
        T.map (P.obj.homologyπ n ≫ (DerivedCategory.homologyFunctorFactors A n).inv.app P.obj) := by
  have h₁ : (DerivedCategory.Plus.homologyFunctor B n).map
      ((Functor.mapCochainComplexPlusDerivedUnit T).app P ≫
        T.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
          (DerivedCategory.Plus.Q.obj P)) =
      (DerivedCategory.homologyFunctor B n).map (T.mapDerivedCategoryFactors.inv.app P.obj) :=
    congrArg (DerivedCategory.homologyFunctor B n).map (ι_map_unit_comp_rdIso_hom T P)
  have h₂ := T.mapDerivedCategoryHomologyIso_hom_app_Q n P.obj
  have h₃ : (DerivedCategory.homologyFunctor B n).map (T.mapDerivedCategoryFactors.inv.app P.obj) ≫
      (T.mapDerivedCategoryHomologyIso n).hom.app (DerivedCategory.Q.obj P.obj) =
      (DerivedCategory.homologyFunctorFactors B n).hom.app
          ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.obj) ≫
        (T.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app P.obj ≫
          T.map ((DerivedCategory.homologyFunctorFactors A n).inv.app P.obj) := by
    rw [h₂, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hπ := CategoryTheory.ShortComplex.homologyπ_comp_mapHomologyIso_hom (P.obj.sc n) T
  refine (congrArg (fun z => _ ≫ _ ≫ z) ((congrArg (· ≫ _) h₁).trans h₃)).trans ?_
  refine (congrArg (_ ≫ ·) ((DerivedCategory.homologyFunctorFactors B n).inv_hom_id_app_assoc
    _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hπ).trans ?_)
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (T.map_comp _ _).symm)

/-- Pasting of commuting diagrams: under the factorizations `hA`, `hD`, `hE`, `hU`, `hB` and
`hF`, the composite `π ≫ hi ≫ U ≫ (a ≫ b ≫ c ≫ (d ≫ e)) ≫ fm` is `mc ≫ z`. -/
private theorem realization_paste {C : Type*} [Category* C]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ Q₃ Q₄ Q₆ R₀ : C}
    (π : P₀ ⟶ P₁) (hi : P₁ ⟶ P₂) (U : P₂ ⟶ P₃) (a : P₃ ⟶ P₄) (b : P₄ ⟶ P₅) (c : P₅ ⟶ P₆)
    (d : P₆ ⟶ P₇) (e : P₇ ⟶ P₈) (fm : P₈ ⟶ P₉) (U₁ : P₂ ⟶ Q₃) (U₂ : Q₃ ⟶ P₆) (d' : Q₃ ⟶ Q₄)
    (U₁₂ : P₂ ⟶ Q₄) (w : Q₄ ⟶ P₇) (e' : Q₄ ⟶ Q₆) (x : Q₆ ⟶ P₈) (mc : P₀ ⟶ R₀) (y : R₀ ⟶ Q₆)
    (z : R₀ ⟶ P₉) (hA : U ≫ a ≫ b ≫ c = U₁ ≫ U₂) (hD : U₂ ≫ d = d' ≫ w) (hE : w ≫ e = e' ≫ x)
    (hU : U₁₂ = U₁ ≫ d') (hB : π ≫ hi ≫ U₁₂ ≫ e' = mc ≫ y) (hF : y ≫ x ≫ fm = z) :
    π ≫ hi ≫ U ≫ (a ≫ b ≫ c ≫ (d ≫ e)) ≫ fm = mc ≫ z := by
  have hA' : U ≫ a ≫ b ≫ c ≫ d ≫ e = U₁₂ ≫ e' ≫ x := by
    rw [reassoc_of% hA, reassoc_of% hD, hE, hU, Category.assoc]
  simp only [Category.assoc]
  rw [reassoc_of% hA', reassoc_of% hB, hF]

end Generic

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable (V : RingedSpace.{u, u})

/-- **Hypercohomology of the underlying abelian sheaves is hypercohomology in modules**
([Stacks, Tag 01F1]), with the unbounded model `RΓ(V, -)` of derived global sections in modules:
`realizationIso` followed by the comparison of the bounded below and the unbounded models. -/
def realizationUnbounded (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V)))
    (n : ℤ) :
    abelianHypercohomology
        ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N) n ≅
      (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).obj
        (cohomologyModule (DerivedCategory.Q.obj N.obj) n) :=
  realizationIso V N n ≪≫
    (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).mapIso
      ((DerivedCategory.homologyFunctor _ n).mapIso
        ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).app N))

variable {V}

/-- `toSheafQIso` read in the unbounded derived category. -/
private theorem ι_map_toSheafQIso_hom_app
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    DerivedCategory.Plus.ι.map ((toSheafQIso V).hom.app N) =
      (SheafOfModules.toSheaf (structureSheafRing V)).mapDerivedCategoryFactors.inv.app N.obj :=
  DerivedCategory.Plus.ι.map_preimage _

/-- `toSheafQIso` against the factorizations through the homotopy category. -/
private theorem qcq_comp_toSheafQIso_hom_app
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    (DerivedCategory.Plus.quotientCompQhIso (AbelianSheaf V.carrier)).hom.app
        ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N) ≫
      (toSheafQIso V).hom.app N =
    (SheafOfModules.toSheaf (structureSheafRing V)).mapDerivedCategoryPlusFactorsh.inv.app
        ((HomotopyCategory.Plus.quotient _).obj N) ≫
      (SheafOfModules.toSheaf (structureSheafRing V)).mapDerivedCategoryPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso _).hom.app N) := by
  apply DerivedCategory.Plus.ι.map_injective
  rw [DerivedCategory.Plus.ι.map_comp, ι_map_toSheafQIso_hom_app]
  exact ι_map_qcq_comp_mapDerivedCategoryFactors_inv _ N

/-- **The unit of the exact functor `toSheaf`** is `toSheafQIso` followed by the comparison of the
induced functor with the right derived functor. -/
private theorem unit_toSheaf_eq
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    ((toSheafQIso V).hom.app N ≫
        (SheafOfModules.toSheaf
          (structureSheafRing V)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
          (DerivedCategory.Plus.Q.obj N) :
        ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q).obj N ⟶ (DerivedCategory.Plus.Q ⋙
            (SheafOfModules.toSheaf (structureSheafRing V)).rightDerivedFunctorPlus).obj N) =
      (Functor.mapCochainComplexPlusDerivedUnit
        (SheafOfModules.toSheaf (structureSheafRing V))).app N := by
  have h := qcq_comp_comp_rdIso_inv (SheafOfModules.toSheaf (structureSheafRing V)) N _
    (qcq_comp_toSheafQIso_hom_app N)
  exact ((Iso.eq_inv_comp ((DerivedCategory.Plus.quotientCompQhIso _).app _)).2 h).trans
    (Functor.mapCochainComplexPlusDerivedUnit_app _ N).symm

open Stacks.Cohomology.ModuleComparison in
/-- **The unit across the realization comparison, in `D⁺(Ab)`.** The abelian unit of global
sections at the underlying complex, followed by the first three factors of `realizationNatIso`,
is the unit of `forget` at `Γ(V, N)` followed by `forget` of the module unit of global
sections. -/
theorem unit_comp_realization
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    (Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor V.carrier ⊤)).app
        ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N) ≫
      (sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map ((toSheafQIso V).hom.app N) ≫
      (sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map
        ((SheafOfModules.toSheaf
          (structureSheafRing V)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
          (DerivedCategory.Plus.Q.obj N)) ≫
      (rightDerivedFunctorPlus_sections_forget_iso V ⊤).inv.app (DerivedCategory.Plus.Q.obj N) =
    (Functor.mapCochainComplexPlusDerivedUnit
        (forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤))) AddCommGrpCat.{u})).app
        ((_root_.SheafOfModules.evaluation (structureSheafRing V)
          (op ⊤)).mapCochainComplexPlus.obj N) ≫
      (forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).rightDerivedFunctorPlus.map
        ((Functor.mapCochainComplexPlusDerivedUnit
          (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))).app N) := by
  have c₁ := Functor.mapCochainComplexPlusDerivedUnit_comp
    (SheafOfModules.toSheaf (structureSheafRing V)) (sectionsFunctor V.carrier ⊤)
    (abelianSectionsComparison V ⊤) (abelianSectionsComparison_fac V ⊤) N
  have c₂ := Functor.mapCochainComplexPlusDerivedUnit_comp
    (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))
    (forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤))) AddCommGrpCat.{u})
    (moduleSectionsComparison V ⊤) (moduleSectionsComparison_fac V ⊤) N
  have hm := (Functor.map_comp_assoc (sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus
    ((toSheafQIso V).hom.app N)
    ((SheafOfModules.toSheaf
      (structureSheafRing V)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
      (DerivedCategory.Plus.Q.obj N))
    ((rightDerivedFunctorPlus_sections_forget_iso V ⊤).inv.app
      (DerivedCategory.Plus.Q.obj N))).symm.trans
    (congrArg (fun z => (sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map z ≫
      (rightDerivedFunctorPlus_sections_forget_iso V ⊤).inv.app (DerivedCategory.Plus.Q.obj N))
      (unit_toSheaf_eq N))
  have hi : (abelianSectionsComparison V ⊤).app (DerivedCategory.Plus.Q.obj N) ≫
      (rightDerivedFunctorPlus_sections_forget_iso V ⊤).inv.app (DerivedCategory.Plus.Q.obj N) =
      (moduleSectionsComparison V ⊤).app (DerivedCategory.Plus.Q.obj N) :=
    (asIso (abelianSectionsComparison V ⊤)).hom_inv_id_app_assoc _ _
  refine (congrArg (_ ≫ ·) hm).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) c₁.symm).trans ((Category.assoc _ _ _).trans ?_)
  exact (congrArg (_ ≫ ·) hi).trans c₂

/-- **The unit of the module sections functor across the model comparison**: read in the unbounded
derived category and followed by the comparison of the bounded below and the unbounded derived
global sections, it is the unit `Γ(V, N) ⟶ RΓ(V, N)` of the unbounded model. -/
private theorem ι_map_unit_comp_boundedDerivedSectionsIso
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) :
    DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit
        (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))).app N) ≫
      (Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso V ⊤).hom.app
        (DerivedCategory.Plus.Q.obj N) =
    sectionsUnitQ V ⊤ N.obj := by
  have e₁ : DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit
        (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))).app N) =
      (DerivedCategory.quotientCompQhIso _).inv.app
          ((_root_.SheafOfModules.evaluation (structureSheafRing V)
            (op ⊤)).mapCochainComplexPlus.obj N).obj ≫
        DerivedCategory.Plus.ι.map ((sectionsOverOpen V ⊤).rightDerivedFunctorPlusUnith.app
          ((HomotopyCategory.Plus.quotient _).obj N)) ≫
        DerivedCategory.Plus.ι.map ((sectionsOverOpen V ⊤).rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.quotientCompQhIso _).hom.app N)) :=
    (DerivedCategory.Plus.ι.map_comp _ _).trans (congrArg₂ (· ≫ ·)
      (Stacks.DerivedIndexing.ι_map_quotientCompQhIso_inv_app _)
      (DerivedCategory.Plus.ι.map_comp _ _))
  have hn := (Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso V ⊤).hom.naturality
    ((DerivedCategory.Plus.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing V))).hom.app N)
  have hb := Stacks.Cohomology.DerivedSectionsModels.boundedDerivedSectionsIso_hom_app V ⊤
    ((HomotopyCategory.Plus.quotient _).obj N)
  refine (congrArg (· ≫ _) e₁).trans ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans ?_)))
  refine (congrArg (_ ≫ ·) hn).trans ((Category.assoc _ _ _).symm.trans ?_)
  refine (congrArg (· ≫ _) hb).trans ?_
  exact congrArg (fun z => _ ≫ (derivedSectionsOverOpen V ⊤).map z)
    (Stacks.DerivedIndexing.ι_map_quotientCompQhIso_hom_app N)

/-- **The class in abelian hypercohomology of a global cocycle** `s` of a bounded below complex
`L` of abelian sheaves: the class of `s` in the cohomology of `Γ(Y, L)`, followed by the unit
`Γ(Y, -) ⟶ R⁺Γ(Y, -)`. -/
def abelianGlobalClass {Y : TopCat.{u}} (L : CochainComplex.Plus (AbelianSheaf Y)) (n : ℤ)
    (s : ((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj.cycles n) :
    abelianHypercohomology L n :=
  (((sectionsFunctor Y ⊤).mapCochainComplexPlus.obj L).obj.homologyπ n ≫
    (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ n).map
        ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor Y ⊤)).app L)).hom s

open Stacks.Cohomology.ModuleComparison in
/-- `realizationIso` written out as a composite. -/
private theorem realizationIso_hom_eq
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ) :
    (realizationIso V N n).hom =
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          ((sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map ((toSheafQIso V).hom.app N)) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          ((sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map
            ((SheafOfModules.toSheaf
              (structureSheafRing V)).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
              (DerivedCategory.Plus.Q.obj N))) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          ((rightDerivedFunctorPlus_sections_forget_iso V ⊤).inv.app
            (DerivedCategory.Plus.Q.obj N)) ≫
        (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
          ((forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤)))
            AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
            ((_root_.SheafOfModules.evaluation (structureSheafRing V)
              (op ⊤)).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N))) ≫
        (forgetPlusHomologyIso V n).hom.app
          ((_root_.SheafOfModules.evaluation (structureSheafRing V)
            (op ⊤)).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj N)) :=
  rfl

/-- **The unit across the realization comparison, on cohomology**, at the level of morphisms: a
cocycle of `Γ(V, N)`, sent to the abelian hypercohomology of the underlying complex by the abelian
unit and then by `realizationUnbounded`, is the same cocycle sent to `Hⁿ(V, N)` by the module unit,
with the module structure forgotten. -/
theorem homologyπ_comp_realizationUnbounded
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ) :
    ((sectionsFunctor V.carrier ⊤).mapCochainComplexPlus.obj
          ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj
            N)).obj.homologyπ n ≫
        (DerivedCategory.homologyFunctorFactors _ n).inv.app _ ≫
        (DerivedCategory.Plus.homologyFunctor _ n).map
          ((Functor.mapCochainComplexPlusDerivedUnit (sectionsFunctor V.carrier ⊤)).app
            ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N)) ≫
        (realizationUnbounded V N n).hom =
      (((sectionsComplex V N.obj).sc n).mapCyclesIso
          (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u})).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).map
          ((sectionsComplex V N.obj).homologyπ n ≫
            (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex V N.obj) ≫
            (DerivedCategory.homologyFunctor _ n).map (sectionsUnitQ V ⊤ N.obj)) := by
  have hA := congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    (unit_comp_realization N)
  simp only [Functor.map_comp] at hA
  have hD := congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
    ((forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
      ((Functor.mapCochainComplexPlusDerivedUnit
        (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))).app N))
  simp only [Functor.map_comp] at hD
  have hE := ((forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).hom.naturality
    (DerivedCategory.Plus.ι.map ((Functor.mapCochainComplexPlusDerivedUnit
        (_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤))).app N))
  have hB := homologyπ_comp_unit_comp_mapHomologyIso
    (forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤))) AddCommGrpCat.{u})
    ((_root_.SheafOfModules.evaluation (structureSheafRing V) (op ⊤)).mapCochainComplexPlus.obj N) n
  have hx := (Functor.map_comp _ _ _).symm.trans (congrArg
    (forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
      (((DerivedCategory.homologyFunctor _ n).map_comp _ _).symm.trans
        (congrArg (DerivedCategory.homologyFunctor _ n).map
          (ι_map_unit_comp_boundedDerivedSectionsIso N))))
  have hF := (congrArg ((forget₂ (ModuleCat.{u} ((structureSheafRing V).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).map ((sectionsComplex V N.obj).homologyπ n ≫
        (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex V N.obj)) ≫ ·)
      hx).trans
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ (Category.assoc _ _ _)))
  have key := realization_paste _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (hA.trans (Functor.map_comp _ _ _)) hD hE
    ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map_comp _ _) hB hF
  rw [show (realizationUnbounded V N n).hom = (realizationIso V N n).hom ≫ _ from rfl,
    realizationIso_hom_eq]
  exact key

/-- **The unit across the realization comparison** ([Stacks, Tag 01F1]), on elements: for a
global cocycle `sA` of the underlying complex of abelian sheaves and the same section `s` read as
a global cocycle of `Γ(V, N)`, `realizationUnbounded` sends the class of `sA` to the class of
`s`. -/
theorem realizationUnbounded_abelianGlobalClass
    (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ)
    (sA : ((sectionsFunctor V.carrier ⊤).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N)).obj.cycles n)
    (s : (sectionsComplex V N.obj).cycles n)
    (h : (((sectionsFunctor V.carrier ⊤).mapCochainComplexPlus.obj
      ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N)).obj.iCycles
        n).hom sA = ((sectionsComplex V N.obj).iCycles n).hom s) :
    (realizationUnbounded V N n).hom.hom
        (abelianGlobalClass
          ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.obj N) n sA) =
      globalClass N.obj n s := by
  have e := ConcreteCategory.congr_hom (homologyπ_comp_realizationUnbounded N n) sA
  have hc : (((sectionsComplex V N.obj).sc n).mapCyclesIso
      (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u})).hom.hom sA = s := by
    have hi := ConcreteCategory.congr_hom
      (((sectionsComplex V N.obj).sc n).mapCyclesIso_hom_iCycles
        (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u})) sA
    exact (ModuleCat.mono_iff_injective ((sectionsComplex V N.obj).iCycles n)).1 inferInstance
      (hi.trans h)
  exact e.trans (congrArg (fun z => ((sectionsComplex V N.obj).homologyπ n ≫
    (DerivedCategory.homologyFunctorFactors _ n).inv.app (sectionsComplex V N.obj) ≫
      (DerivedCategory.homologyFunctor _ n).map (sectionsUnitQ V ⊤ N.obj)).hom z) hc)

variable (V) in
/-- **`realizationUnbounded` is natural in the complex.** -/
theorem realizationUnbounded_naturality
    {N N' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing V))} (a : N ⟶ N') (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        ((sectionsFunctor V.carrier ⊤).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map
          ((SheafOfModules.toSheaf (structureSheafRing V)).mapCochainComplexPlus.map a))) ≫
        (realizationUnbounded V N' n).hom =
      (realizationUnbounded V N n).hom ≫
        (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ n).map
            ((baseSections V).map (DerivedCategory.Q.map a.hom))) := by
  have h₁ := realizationIso_naturality V a n
  have h₂ := congrArg (fun z => (forget₂ (ModuleCat.{u} (baseRing V)) AddCommGrpCat.{u}).map
    ((DerivedCategory.homologyFunctor _ n).map z))
    ((Stacks.Cohomology.DerivedSectionsModels.derivedSectionsFunctorIso V ⊤).hom.naturality a)
  simp only [Functor.map_comp] at h₂
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

end Stacks.Cech.Hypercohomology

end
