module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryNatTrans
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition

/-!
# A transformation of exact functors, on a single object of the derived category

Let `τ : T ⟶ S` be a natural transformation between exact functors of abelian categories. The
functors induce `T̄, S̄ : D⁺(A) ⥤ D⁺(B)` and `τ` induces `τ̄ : T̄ ⟶ S̄`
(`Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans`). On a complex `X[0]` concentrated in
degree zero, `τ̄` is `τ_X[0]`, read through the comparisons `T̄(X[0]) ≅ T(X)[0]` and
`S̄(X[0]) ≅ S(X)[0]` of `CategoryTheory.Functor.mapDerivedCategoryPlusObjSingleIso`.

## Main results

* `Stacks.DerivedFunctor.mapDerivedCategoryPlusNatTrans_app_single` — the compatibility above.
* `Stacks.DerivedFunctor.singleMapHomologicalComplex_hom_naturality` — the same statement one level
  down, for complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace Stacks.DerivedFunctor

section Complexes

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [HasZeroMorphisms A] [HasZeroMorphisms B] [HasZeroObject A] [HasZeroObject B]
  {T S : A ⥤ B} [T.PreservesZeroMorphisms] [S.PreservesZeroMorphisms]
  {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι)

/-- **A transformation of functors, applied degreewise to a single complex**, is the single complex
of its component, read through `T(X[j]) ≅ T(X)[j]` and `S(X[j]) ≅ S(X)[j]`. -/
theorem singleMapHomologicalComplex_hom_naturality (τ : T ⟶ S) (X : A) :
    (NatTrans.mapHomologicalComplex τ c).app ((HomologicalComplex.single A c j).obj X) ≫
        (HomologicalComplex.singleMapHomologicalComplex S c j).hom.app X =
      (HomologicalComplex.singleMapHomologicalComplex T c j).hom.app X ≫
        (HomologicalComplex.single B c j).map (τ.app X) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← τ.naturality_assoc]

end Complexes

section HomotopyPlus

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] {T S : A ⥤ B} [T.Additive] [S.Additive]

/-- **`mapHomotopyCategoryPlusObjSingleIso`, seen in the homotopy category of complexes.** -/
private theorem map_mapHomotopyCategoryPlusObjSingleIso_hom (F : A ⥤ B) [F.Additive]
    (n : ℤ) (X : A) :
    (HomotopyCategory.Plus.ι B).map (F.mapHomotopyCategoryPlusObjSingleIso n X).hom =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X) :=
  Functor.map_preimage _ _

/-- **A transformation of additive functors on a single bounded-below complex**: under
`T(X[n]) ≅ T(X)[n]` and `S(X[n]) ≅ S(X)[n]`, its component at `X[n]` is `τ_X[n]`. -/
private theorem mapHomotopyCategory_app_single_comp_mapHomotopyCategoryPlusObjSingleIso_hom
    (τ : T ⟶ S) (n : ℤ) (X : A) :
    (τ.mapHomotopyCategory (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.singleFunctor A n).obj X).obj ≫
      (S.mapHomotopyCategoryPlusObjSingleIso n X).hom.hom =
      (T.mapHomotopyCategoryPlusObjSingleIso n X).hom.hom ≫
        ((HomotopyCategory.Plus.singleFunctor B n).map (τ.app X)).hom := by
  show (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single A (ComplexShape.up ℤ) n).obj X)) ≫
      (HomotopyCategory.Plus.ι B).map (S.mapHomotopyCategoryPlusObjSingleIso n X).hom =
      (HomotopyCategory.Plus.ι B).map (T.mapHomotopyCategoryPlusObjSingleIso n X).hom ≫
        (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single B (ComplexShape.up ℤ) n).map (τ.app X))
  rw [map_mapHomotopyCategoryPlusObjSingleIso_hom,
    map_mapHomotopyCategoryPlusObjSingleIso_hom]
  exact ((Functor.map_comp _ _ _).symm.trans (congrArg _
    (singleMapHomologicalComplex_hom_naturality (ComplexShape.up ℤ) n τ X))).trans
    (Functor.map_comp _ _ _)

/-- **`F(X[n]) ≅ F(X)[n]` is natural in `X`** on bounded-below homotopy categories. -/
private theorem mapHomotopyCategoryPlusObjSingleIso_hom_naturality (n : ℤ) {X X' : A} (g : X ⟶ X') :
    S.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.singleFunctor A n).map g) ≫
      (S.mapHomotopyCategoryPlusObjSingleIso n X').hom =
      (S.mapHomotopyCategoryPlusObjSingleIso n X).hom ≫
        (HomotopyCategory.Plus.singleFunctor B n).map (S.map g) := by
  refine (HomotopyCategory.Plus.ι B).map_injective ?_
  have eg : (HomotopyCategory.Plus.ι B).map (S.mapHomotopyCategoryPlus.map
      ((HomotopyCategory.Plus.singleFunctor A n).map g)) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.single A (ComplexShape.up ℤ) n).map g)) := rfl
  have eg' : (HomotopyCategory.Plus.ι B).map
      ((HomotopyCategory.Plus.singleFunctor B n).map (S.map g)) =
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((HomologicalComplex.single B (ComplexShape.up ℤ) n).map (S.map g)) := rfl
  rw [Functor.map_comp, Functor.map_comp, map_mapHomotopyCategoryPlusObjSingleIso_hom,
    map_mapHomotopyCategoryPlusObjSingleIso_hom, eg, eg']
  exact (Functor.map_comp _ _ _).symm.trans ((congrArg _
    ((HomologicalComplex.singleMapHomologicalComplex S (ComplexShape.up ℤ) n).hom.naturality
      g)).trans (Functor.map_comp _ _ _))

end HomotopyPlus

section Plus

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] [EnoughInjectives A]
  {T S : A ⥤ B} [T.Additive] [S.Additive]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]

/-- **The induced transformation on a single object.** Under the comparisons
`T̄(X[0]) ≅ T(X)[0]` and `S̄(X[0]) ≅ S(X)[0]`, the component of `τ̄` at `X[0]` is `τ_X[0]`. -/
theorem mapDerivedCategoryPlusNatTrans_app_single (τ : T ⟶ S) (X : A) :
    (mapDerivedCategoryPlusNatTrans τ).app ((DerivedCategory.Plus.singleFunctor A 0).obj X) ≫
        (S.mapDerivedCategoryPlusObjSingleIso X).hom =
      (T.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (τ.app X) := by
  rw [Functor.mapDerivedCategoryPlusObjSingleIso_hom,
    Functor.mapDerivedCategoryPlusObjSingleIso_hom]
  have h1 := (mapDerivedCategoryPlusNatTrans τ).naturality
    ((Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app X)
  have h4 := (Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.naturality (τ.app X)
  have h2 : DerivedCategory.Plus.ι.map ((mapDerivedCategoryPlusNatTrans τ).app
        (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.singleFunctor A 0).obj X))) ≫
      DerivedCategory.Plus.ι.map
        (S.mapDerivedCategoryPlusFactorsh.hom.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) =
      DerivedCategory.Plus.ι.map
        (T.mapDerivedCategoryPlusFactorsh.hom.app
          ((HomotopyCategory.Plus.singleFunctor A 0).obj X)) ≫
      DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj) :=
    mapDerivedNatTrans_factorsh_app τ _
  have h3 := mapHomotopyCategory_app_single_comp_mapHomotopyCategoryPlusObjSingleIso_hom τ 0 X
  have h3' : DerivedCategory.Qh.map ((τ.mapHomotopyCategory (ComplexShape.up ℤ)).app
        ((HomotopyCategory.Plus.singleFunctor A 0).obj X).obj) ≫
      DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Qh.map (S.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) =
      DerivedCategory.Plus.ι.map
        (DerivedCategory.Plus.Qh.map (T.mapHomotopyCategoryPlusObjSingleIso 0 X).hom) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
        ((HomotopyCategory.Plus.singleFunctor B 0).map (τ.app X))) :=
    (Functor.map_comp DerivedCategory.Qh _ _).symm.trans
      ((congrArg DerivedCategory.Qh.map h3).trans (Functor.map_comp _ _ _))
  have H1 := congrArg DerivedCategory.Plus.ι.map h1
  have H4 := congrArg DerivedCategory.Plus.ι.map h4
  simp only [Functor.map_comp, Functor.comp_map] at H1 H4
  refine DerivedCategory.Plus.ι.map_injective ?_
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% H1, reassoc_of% h2]
  refine congrArg (_ ≫ ·) (congrArg (_ ≫ ·) ?_)
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h3')).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) H4))

omit [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] in
/-- **`F̄(X[0]) ≅ F(X)[0]` is natural in `X`.** -/
theorem mapDerivedCategoryPlusObjSingleIso_hom_naturality {X X' : A} (g : X ⟶ X') :
    S.mapDerivedCategoryPlus.map ((DerivedCategory.Plus.singleFunctor A 0).map g) ≫
        (S.mapDerivedCategoryPlusObjSingleIso X').hom =
      (S.mapDerivedCategoryPlusObjSingleIso X).hom ≫
        (DerivedCategory.Plus.singleFunctor B 0).map (S.map g) := by
  rw [Functor.mapDerivedCategoryPlusObjSingleIso_hom,
    Functor.mapDerivedCategoryPlusObjSingleIso_hom]
  have h1 := (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.naturality g
  have h2 := S.mapDerivedCategoryPlusFactorsh.hom.naturality
    ((HomotopyCategory.Plus.singleFunctor A 0).map g)
  have h4 := (Functor.singleFunctorPlusIsoCompQh (A := B) 0).inv.naturality (S.map g)
  have h3 := mapHomotopyCategoryPlusObjSingleIso_hom_naturality (S := S) 0 g
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, h1, Functor.map_comp_assoc]
  refine congrArg (_ ≫ ·) ?_
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h2).trans ?_)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  have h3' : (S.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).map
        ((HomotopyCategory.Plus.singleFunctor A 0).map g) ≫
      DerivedCategory.Plus.Qh.map (S.mapHomotopyCategoryPlusObjSingleIso 0 X').hom =
      DerivedCategory.Plus.Qh.map (S.mapHomotopyCategoryPlusObjSingleIso 0 X).hom ≫
        (HomotopyCategory.Plus.singleFunctor B 0 ⋙ DerivedCategory.Plus.Qh).map (S.map g) :=
    (Functor.map_comp DerivedCategory.Plus.Qh _ _).symm.trans
      ((congrArg DerivedCategory.Plus.Qh.map h3).trans (Functor.map_comp _ _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h3').trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h4)))

end Plus

end Stacks.DerivedFunctor

end
