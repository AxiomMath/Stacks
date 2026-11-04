module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectBidual

/-!
# The biduality map is natural

Let `(X, O_X)` be a ringed space. The dual `K ↦ K^∨ = RSheafHom(K, O_X)` of
`Stacks.SheafOfModules.derivedDual` is the value on objects of the contravariant functor
`Stacks.SheafOfModules.derivedDualFunctor`, and the canonical biduality map
`Stacks.SheafOfModules.derivedBidualMap : K ⟶ (K^∨)^∨` of [Stacks, Tag 08DQ] is natural in `K`:
it is the component of a natural transformation `𝟭 ⟶ (-)^∨∨`.

## Main definitions

* `Stacks.SheafOfModules.derivedDualFunctor`: the functor `K ↦ K^∨` on `D(O_X)ᵒᵖ`.
* `Stacks.SheafOfModules.derivedBidualNatTrans`: the natural transformation `𝟭 ⟶ (-)^∨∨`
  whose components are the biduality maps.

## Main results

* `Stacks.SheafOfModules.derivedBidualMap_naturality`: the biduality map is natural.

## References

* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] derivedMonoidalStructure

attribute [local implicit_reducible] CategoryTheory.sheafCompose

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The dual as a functor**: `K ↦ K^∨ = RSheafHom(K, O_X)`, contravariant on `D(O_X)`. Its value
on an object is `Stacks.SheafOfModules.derivedDual` by definition. -/
abbrev derivedDualFunctor :
    (DerivedCategory (StructureSheafModules Rc))ᵒᵖ ⥤ DerivedCategory (StructureSheafModules Rc) :=
  (derivedSheafHom Rc).flip.obj (RingedSite.derivedStructureSheaf (ringedSite Rc))

/-- The dual functor computes the dual on objects. -/
theorem derivedDualFunctor_obj (K : DerivedCategory (StructureSheafModules Rc)) :
    (derivedDualFunctor Rc).obj (op K) = derivedDual Rc K :=
  rfl

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

/-- A bifunctor evaluated on an identity in its first variable and a morphism in its second. -/
private lemma bifunctor_map_id_app_comp {C D E : Type*} [Category C] [Category D] [Category E]
    (T : C ⥤ D ⥤ E) (A : C) {B B' : D} (b : B ⟶ B') :
    (T.map (𝟙 A)).app B ≫ (T.obj A).map b = (T.obj A).map b := by
  simp

/-- A bifunctor evaluated on a morphism in its first variable and an identity in its second. -/
private lemma bifunctor_map_app_comp_map_id {C D E : Type*} [Category C] [Category D]
    [Category E] (T : C ⥤ D ⥤ E) {A A' : C} (a : A ⟶ A') (B : D) :
    (T.map a).app B ≫ (T.obj A').map (𝟙 B) = (T.map a).app B := by
  simp

/-- Postcomposing both sides of a commutative square with a further morphism. -/
private lemma comp_comp_of_eq {C : Type*} [Category C] {W X Y Z T : C} {a : W ⟶ X} {b : X ⟶ Z}
    {c : W ⟶ Y} {d : Y ⟶ Z} (h : a ≫ b = c ≫ d) (e : Z ⟶ T) :
    a ≫ b ≫ e = c ≫ d ≫ e := by
  rw [← Category.assoc, h, Category.assoc]

/-- **The biduality map is natural**: for `f : K ⟶ K'` the square formed by `f`, its double dual
and the two biduality maps `K ⟶ (K^∨)^∨` and `K' ⟶ (K'^∨)^∨` commutes. -/
theorem derivedBidualMap_naturality {K K' : DerivedCategory (StructureSheafModules Rc)}
    (f : K ⟶ K') :
    f ≫ derivedBidualMap Rc K' =
      derivedBidualMap Rc K ≫
        (derivedDualFunctor Rc).map ((derivedDualFunctor Rc).map f.op).op := by
  let O := RingedSite.derivedStructureSheaf (ringedSite Rc)
  let D := derivedDualFunctor Rc
  have hev := derivedSheafHomEvaluation_natural Rc f (𝟙 O) (𝟙 O)
  have h0 : derivedSheafHomMap Rc (𝟙 O) (𝟙 O) = 𝟙 (((derivedSheafHom Rc).obj (op O)).obj O) :=
    RingedSite.derivedSheafHomMap_id _ _ _ _
  have hl : derivedTensorMap Rc (𝟙 (((derivedSheafHom Rc).obj (op O)).obj O)) f =
      ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op O)).obj O)).map f :=
    bifunctor_map_id_app_comp _ _ _
  have ha : derivedSheafHomMap Rc f (𝟙 O) = D.map f.op :=
    bifunctor_map_app_comp_map_id _ _ _
  have hr : derivedSheafHomMap Rc (D.map f.op) (𝟙 O) = D.map (D.map f.op).op :=
    bifunctor_map_app_comp_map_id _ _ _
  rw [h0, hl, ha, hr] at hev
  rw [derivedBidualMap_eq, derivedBidualMap_eq]
  calc _ = (λ_ K).inv ≫ (𝟙_ _ ◁ f) ≫
        (((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K').hom ≫
          derivedSheafHomEvaluation Rc K' O O := (reassoc_of% leftUnitor_inv_naturality f) _
    _ = (λ_ K).inv ≫
        (((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K).hom ≫
        ((derivedTensor Rc).obj (((derivedSheafHom Rc).obj (op O)).obj O)).map f ≫
          derivedSheafHomEvaluation Rc K' O O :=
            congrArg _ (comp_comp_of_eq
              (((derivedTensor Rc).map (derivedDualStructureSheafIso Rc).inv).naturality f) _)
    _ = (λ_ K).inv ≫
        (((derivedTensor Rc).mapIso (derivedDualStructureSheafIso Rc).symm).app K).hom ≫
        derivedSheafHomEvaluation Rc K O O ≫ D.map (D.map f.op).op := congrArg _ (congrArg _ hev)
    _ = _ := ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _))).symm

/-- **The biduality maps form a natural transformation** `𝟭 ⟶ (-)^∨∨`. -/
def derivedBidualNatTrans :
    𝟭 (DerivedCategory (StructureSheafModules Rc)) ⟶
      (derivedDualFunctor Rc).rightOp ⋙ derivedDualFunctor Rc where
  app K := derivedBidualMap Rc K
  naturality _ _ f := derivedBidualMap_naturality Rc f

end Stacks.SheafOfModules

end
