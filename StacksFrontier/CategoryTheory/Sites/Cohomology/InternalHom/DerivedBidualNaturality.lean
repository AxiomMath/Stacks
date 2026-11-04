module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.LeftUnitorNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedBidual

/-!
# The canonical map to the double derived dual is natural

Let `(C, O)` be a ringed site. The canonical map `K ⟶ (K^∨)^∨` of
`AlgebraicGeometry.RingedSite.derivedBidual` is natural in `K`: its three constituents, the left
unit constraint, the identification `O ≅ RSheafHom(O, O)` in the tensor factor and the
evaluation morphism of Stacks 0A97, are.

## Main results

* `AlgebraicGeometry.RingedSite.derivedBidual_naturality`, and the transformation
  `AlgebraicGeometry.RingedSite.derivedBidualTrans : 𝟭 ⟶ (-)^∨∨`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u}
      X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

variable (T : Stacks.SheafOfModules.DerivedTensorProduct X)

/-- **The canonical map to the double derived dual is natural**: for `f : K ⟶ K'`,
`f ≫ (K' ⟶ K'^∨∨) = (K ⟶ K^∨∨) ≫ f^∨∨`. -/
theorem derivedBidual_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : K ⟶ K') :
    f ≫ derivedBidual X T K' =
      derivedBidual X T K ≫ ((derivedSheafHomBifunctor X).map
        (((derivedSheafHomBifunctor X).map f.op).app (derivedStructureSheaf X)).op).app
          (derivedStructureSheaf X) := by
  have hl := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso_naturality X
    (derivedTensorProductDatumOfSite X T) f
  have hl' : f ≫ (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
        (derivedTensorProductDatumOfSite X T) K').inv =
      (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
        (derivedTensorProductDatumOfSite X T) K).inv ≫
        ((derivedTensorProductDatumOfSite X T).tensor.obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)).map f := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← hl, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hs : ((derivedTensorProductDatumOfSite X T).tensor.obj
        (Stacks.DerivedTensor.RingedSite.unitObject X)).map f ≫
        (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K' =
      (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).app K ≫
        (T.tensor.obj (((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).obj
          (derivedStructureSheaf X))).map f :=
    (T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv).naturality f
  have hev := derivedSheafHomEvaluation_natural X T (derivedInternalHomOfBifunctor X) f
    (𝟙 (derivedStructureSheaf X)) (𝟙 (derivedStructureSheaf X))
  simp only [derivedSheafHomMap_id, derivedTensorMap, derivedSheafHomMap,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id,
    op_id] at hev
  let l := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso X
    (derivedTensorProductDatumOfSite X T)
  let s := T.tensor.map (derivedStructureSheafHomIso X (derivedStructureSheaf X)).inv
  let ev := derivedSheafHomEvaluation X T (derivedInternalHomOfBifunctor X)
  let O := derivedStructureSheaf X
  calc f ≫ derivedBidual X T K'
      = (f ≫ (l K').inv) ≫ s.app K' ≫ ev K' O O := (Category.assoc _ _ _).symm
    _ = ((l K).inv ≫ ((derivedTensorProductDatumOfSite X T).tensor.obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)).map f) ≫ s.app K' ≫ ev K' O O :=
        congrArg (· ≫ s.app K' ≫ ev K' O O) hl'
    _ = (l K).inv ≫ (((derivedTensorProductDatumOfSite X T).tensor.obj
          (Stacks.DerivedTensor.RingedSite.unitObject X)).map f ≫ s.app K') ≫ ev K' O O :=
        (Category.assoc _ _ _).trans (congrArg ((l K).inv ≫ ·) (Category.assoc _ _ _).symm)
    _ = (l K).inv ≫ (s.app K ≫ (T.tensor.obj (((derivedSheafHomBifunctor X).obj
          (op O)).obj O)).map f) ≫ ev K' O O :=
        congrArg (fun t ↦ (l K).inv ≫ t ≫ ev K' O O) hs
    _ = (l K).inv ≫ s.app K ≫ ((T.tensor.obj (((derivedSheafHomBifunctor X).obj
          (op O)).obj O)).map f ≫ ev K' O O) :=
        congrArg ((l K).inv ≫ ·) (Category.assoc _ _ _)
    _ = (l K).inv ≫ s.app K ≫ (ev K O O ≫ ((derivedSheafHomBifunctor X).map
          (((derivedSheafHomBifunctor X).map f.op).app O).op).app O) :=
        congrArg (fun t ↦ (l K).inv ≫ s.app K ≫ t) hev
    _ = _ := ((Category.assoc _ _ _).trans (congrArg ((l K).inv ≫ ·) (Category.assoc _ _ _))).symm

/-- **The canonical map to the double derived dual as a natural transformation**
`𝟭 ⟶ (-)^∨∨`, the dual being `RSheafHom(-, O)`. -/
def derivedBidualTrans :
    𝟭 (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      ((derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X)).rightOp ⋙
        (derivedSheafHomBifunctor X).flip.obj (derivedStructureSheaf X) where
  app K := derivedBidual X T K
  naturality _ _ f := derivedBidual_naturality X T f

/-- The component of `derivedBidualTrans` at `K` is the canonical map `derivedBidual X T K`. -/
@[simp]
lemma derivedBidualTrans_app
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedBidualTrans X T).app K = derivedBidual X T K :=
  rfl

end AlgebraicGeometry.RingedSite
