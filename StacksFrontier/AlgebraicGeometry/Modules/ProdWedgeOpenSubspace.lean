module

public import StacksFrontier.AlgebraicGeometry.Modules.TensorOpenSubspaceMulPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRestrictOpenFunctorial
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf

/-!
# The wedge-product morphism crosses restriction to an open subspace

Let `X` be a ringed space, `U ⊆ X` open, `iF : F ⟶ H` and `iG : G ⟶ H` morphisms of sheaves of
`𝒪_X`-modules, and `AF`, `AG`, `A` bundles of tensor, exterior and symmetric algebras of `F`, `G`
and `H`. The wedge product `SheafOfModules.prodWedgeHom : ⋀^pF ⊗ ⋀^qG ⟶ ⋀^{p+q}H` is by
definition the tensor product of the two functorial maps on exterior powers followed by the
multiplication of the exterior algebra of `H`,

`prodWedgeHom = (⋀^p iF ⊗ ⋀^q iG) ≫ mul`,

so carrying it across restriction to `U` is carrying those two factors across: the tensor product
crosses by the naturality of `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U`
(`SheafOfModules.openSubspaceTensorBifunctorIso_naturality`) and the multiplication by the
multiplication square (`SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf`).

The exterior powers of `F|_U`, `G|_U` and `H|_U` do not appear: the statement is written entirely
in restrictions of data on `X` together with `SheafOfModules.openSubspaceAlg`, so the only
exterior algebra in it is the restriction of the one on `X`. Identifying that restriction with an
exterior algebra chosen on `U` is a separate step, available on pieces as
`SheafOfModules.openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso` and on
homogeneous local sections as `SheafOfModules.exteriorRestrictOpenSubspaceIso_mul`.

## Main results

* `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom`: the wedge-product
  morphism, restricted to an open subspace and read through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at the
  source, is the tensor product of the two restricted functorial maps on exterior powers followed
  by the multiplication of the restricted exterior algebra.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf AlgebraicGeometry Opposite PresheafOfModules
  TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)

universe u

namespace SheafOfModules

/-- A commuting square of isomorphisms, transposed: from `φ ≫ e'.hom = e.hom ≫ ψ` read the
composite that starts with `e.inv`. -/
theorem invCompOfCompHom {C : Type*} [Category C] {A B P Q : C} (e : A ≅ B) (e' : P ≅ Q)
    (φ : A ⟶ P) (ψ : B ⟶ Q) (h : φ ≫ e'.hom = e.hom ≫ ψ) : e.inv ≫ φ = ψ ≫ e'.inv :=
  (Iso.inv_comp_eq e).2 (by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id])

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {F G H : SheafOfModules.{u} (structureSheafRing X)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) H)
  (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ)

/-- `SheafOfModules.prodWedgeHom` unfolded: the tensor product of the two functorial maps on
exterior powers, followed by the multiplication of the exterior algebra of the target. -/
private theorem prodWedgeHomUnfold :
    prodWedgeHom AF AG A iF iG p q =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
          ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ),
            AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) :
              (AF.exteriorPower p, AG.exteriorPower q) ⟶
                (A.exteriorPower p, A.exteriorPower q)) ≫
        GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ) :=
  rfl

/-- The wedge-product morphism `⋀^pF ⊗ ⋀^qG ⟶ ⋀^{p+q}H` crosses restriction to an open subspace:
read through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` at the source, the restriction of
`SheafOfModules.prodWedgeHom` is the tensor product of the restrictions of the two functorial maps
on exterior powers, followed by the multiplication of the restricted exterior algebra of `H`. -/
theorem openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom :
    (openSubspaceTensorBifunctorIso U (AF.exteriorPower p) (AG.exteriorPower q)).inv ≫
        (openSubspaceRestriction U).map (prodWedgeHom AF AG A iF iG p q) =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((openSubspaceRestriction U).map
              (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ)),
            (openSubspaceRestriction U).map
              (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ))) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower p),
                (openSubspaceRestriction U).obj (AG.exteriorPower q)) ⟶
              ((openSubspaceRestriction U).obj (A.exteriorPower p),
                (openSubspaceRestriction U).obj (A.exteriorPower q))) ≫
        GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf)
          (openSubspaceAlg A.exterior U) (p : ℤ) (q : ℤ) :=
  Eq.trans
    (congrArg (fun z => (openSubspaceTensorBifunctorIso U (AF.exteriorPower p)
        (AG.exteriorPower q)).inv ≫ (openSubspaceRestriction U).map z)
      (prodWedgeHomUnfold AF AG A iF iG p q))
    (Eq.trans
      (congrArg (fun z => (openSubspaceTensorBifunctorIso U (AF.exteriorPower p)
          (AG.exteriorPower q)).inv ≫ z)
        ((openSubspaceRestriction U).map_comp
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf)).map
            ((AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ),
              AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG (q : ℤ)) :
                (AF.exteriorPower p, AG.exteriorPower q) ⟶
                  (A.exteriorPower p, A.exteriorPower q)))
          (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ))))
      (Eq.trans (Category.assoc _ _ _).symm
        (Eq.trans
          (congrArg (fun z => z ≫ (openSubspaceRestriction U).map
              (GradedAlgebra.mulSheaf A.exterior (p : ℤ) (q : ℤ)))
            (invCompOfCompHom
              (openSubspaceTensorBifunctorIso U (AF.exteriorPower p) (AG.exteriorPower q))
              (openSubspaceTensorBifunctorIso U (A.exteriorPower p) (A.exteriorPower q))
              _ _
              (openSubspaceTensorBifunctorIso_naturality U
                (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF (p : ℤ))
                (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
                  iG (q : ℤ)))))
          (Eq.trans (Category.assoc _ _ _)
            (congrArg (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                (restrictToOpen X U).sheaf)).map
              (((openSubspaceRestriction U).map
                  (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
                    iF (p : ℤ)),
                (openSubspaceRestriction U).map
                  (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra
                    iG (q : ℤ))) :
                ((openSubspaceRestriction U).obj (AF.exteriorPower p),
                    (openSubspaceRestriction U).obj (AG.exteriorPower q)) ⟶
                  ((openSubspaceRestriction U).obj (A.exteriorPower p),
                    (openSubspaceRestriction U).obj (A.exteriorPower q))) ≫ z)
              (openSubspaceTensorBifunctorIso_inv_comp_map_mulSheaf U A.exterior (p : ℤ)
                (q : ℤ)))))))

end SheafOfModules

end
