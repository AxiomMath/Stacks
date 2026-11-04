module

public import StacksFrontier.AlgebraicGeometry.Modules.ProdWedgeOpenSubspace
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsLocalKunneth
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothFormsSplittingDependence

/-!
# The restricted wedge product, read at exterior algebras chosen on the open subspace

Let `X` be a ringed space, `U ⊆ X` open, `M` a sheaf of `𝒪_X`-modules, `A` an exterior algebra of
`M` on `X` and `B` an exterior algebra of `M|_U` on `U`. `SheafOfModules.openSubspaceAlg` is the
restriction `A|_U`, itself an exterior algebra of `M|_U`
(`SheafOfModules.isExteriorAlgebra_openSubspaceAlg`), and
`SheafOfModules.exteriorRestrictOpenSubspaceIso` is the resulting comparison `e : (A|_U)_n ≅ B_n`.
`SheafOfModules.exteriorRestrictOpenSubspaceIso_mul` says `e` is multiplicative **on homogeneous
local sections**. This file says it as a **square of morphisms of sheaves of modules**,

`mul_{A|_U} i j ≫ e (i+j) = (e i ⊗ e j) ≫ mul_B i j`,

and then uses that square to rewrite the right-hand side of
`SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom` — whose only algebra is
the restriction of the one on `X` — as a wedge product of exterior algebras **chosen on `U`**.
That is the shape in which a consumer over the open subspace meets the restricted wedge product:
the comparisons of [Stacks, Section 0FMK] are built from a bundle of algebras on the open
subscheme itself, not from the restriction of a bundle on `X`.

The same square read with both vertical comparisons assembled into isomorphisms identifies the
**targets** of the two readings: the restriction of the cokernel of the wedge-product morphism is
the cokernel of the wedge-product morphism on `U`. That cokernel is the ambient object of the
graded piece of the wedge filtration, so this is the identification a statement about the graded
piece over `U` has to be matched against.

## Main results

* `SheafOfModules.mulSheaf_comp_exteriorRestrictOpenSubspaceIso`: the comparison between the
  restricted exterior algebra and an exterior algebra chosen on the open subspace commutes with
  the morphism-level multiplications, in the tensor-bifunctor spelling.
* `SheafOfModules.openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso`:
  the restricted wedge-product morphism is the wedge-product morphism of bundles of algebras
  chosen on `U`, read through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` and the two source comparisons at the
  source and through the target comparison at the target.
* `…_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom`, the same identity with the
  source identification moved to the other side, so that both vertical maps are isomorphisms and
  the identity is a commuting square.
* `SheafOfModules.prodWedgeHomCokernelOpenSubspaceIso`: the restriction of the cokernel of the
  wedge-product morphism is the cokernel of the wedge-product morphism of the bundles chosen on
  `U`.

The three bundles of algebras over the open subspace are hypotheses — arbitrary
`SheafOfModules.TensorExteriorSymmetricAlgebras` of the three restricted sheaves of modules — so
nothing here transports a bundle across restriction; a consumer supplies the bundle it already
has, which over an open subscheme is `SheafOfModules.ringedSpaceAlgebras` of that subscheme.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Section 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf CategoryTheory.Limits AlgebraicGeometry Opposite
  PresheafOfModules TopologicalSpace
open Stacks.Cohomology.HigherDirectImage (restrictToOpen)
open Stacks.SheafOfModules.PushforwardSheafification

universe u

namespace Stacks.CategoryTheory

/-- Moving the first of two composed isomorphisms across an equation: if `e⁻¹ ≫ a = f ≫ c` then
`a = (e ≪≫ f) ≫ c`. -/
theorem eq_trans_hom_comp_of_inv_comp_eq {D : Type*} [_root_.CategoryTheory.Category D]
    {P Q R T : D} (e : P ≅ Q) (f : Q ≅ R) (a : P ⟶ T) (c : R ⟶ T)
    (h : e.inv ≫ a = f.hom ≫ c) : a = (e ≪≫ f).hom ≫ c := by
  rw [Iso.trans_hom, Category.assoc, ← h, Iso.hom_inv_id_assoc]

end Stacks.CategoryTheory

namespace SheafOfModules

open Stacks.SheafOfModules

/-- Two composites of the values of a bifunctor on pairs of morphisms agree as soon as the two
components agree, that is, as soon as `f₁ ≫ f₂ = u₁ ≫ u₂` and `g₁ ≫ g₂ = v₁ ≫ v₂`. -/
theorem bifunctorMapCompMapEq {C D E : Type*} [Category C] [Category D] [Category E]
    (Φ : C × D ⥤ E) {a₀ a₁ a₂ a₃ : C} {b₀ b₁ b₂ b₃ : D}
    (f₁ : a₀ ⟶ a₁) (f₂ : a₁ ⟶ a₂) (g₁ : b₀ ⟶ b₁) (g₂ : b₁ ⟶ b₂)
    (u₁ : a₀ ⟶ a₃) (u₂ : a₃ ⟶ a₂) (v₁ : b₀ ⟶ b₃) (v₂ : b₃ ⟶ b₂)
    (hf : f₁ ≫ f₂ = u₁ ≫ u₂) (hg : g₁ ≫ g₂ = v₁ ≫ v₂) :
    Φ.map ((f₁, g₁) : (a₀, b₀) ⟶ (a₁, b₁)) ≫ Φ.map ((f₂, g₂) : (a₁, b₁) ⟶ (a₂, b₂)) =
      Φ.map ((u₁, v₁) : (a₀, b₀) ⟶ (a₃, b₃)) ≫ Φ.map ((u₂, v₂) : (a₃, b₃) ⟶ (a₂, b₂)) :=
  Eq.trans
    (Φ.map_comp ((f₁, g₁) : (a₀, b₀) ⟶ (a₁, b₁)) ((f₂, g₂) : (a₁, b₁) ⟶ (a₂, b₂))).symm
    (Eq.trans
      (congrArg Φ.map
        (Eq.trans (prod_comp ((f₁, g₁) : (a₀, b₀) ⟶ (a₁, b₁)) ((f₂, g₂) : (a₁, b₁) ⟶ (a₂, b₂)))
          (Eq.trans (congrArg₂ Prod.mk hf hg)
            (prod_comp ((u₁, v₁) : (a₀, b₀) ⟶ (a₃, b₃))
              ((u₂, v₂) : (a₃, b₃) ⟶ (a₂, b₂))).symm)))
      (Φ.map_comp ((u₁, v₁) : (a₀, b₀) ⟶ (a₃, b₃)) ((u₂, v₂) : (a₃, b₃) ⟶ (a₂, b₂))))

section MulSquare

variable {X : RingedSpace.{u, u}} (M : SheafOfModules.{u} (structureSheafRing X))
  (A : GradedAlgebra.{u, u} (structureSheafRing X)) (gen : M ⟶ A.piece 1)
  (hA : GradedAlgebra.IsExteriorAlgebra A gen) (U : Opens X.carrier)
  (B : GradedAlgebra.{u, u} (pushforwardRingSheaf (Opens.grothendieckTopology ↥U)
    (openSubspaceSiteFunctor U) ((structureSheafRing X).over U)))
  (gen' : (sheafPushforwardFunctor.{u} (Opens.grothendieckTopology ↥U)
    (openSubspaceSiteFunctor U) ((structureSheafRing X).over U)).obj (M.over U) ⟶ B.piece 1)
  (hB : GradedAlgebra.IsExteriorAlgebra B gen')

include hA hB

/-- The comparison `(⋀ⁿM)|_U ≅ ⋀ⁿ(M|_U)` commutes with the morphism-level multiplications: with
`e n := SheafOfModules.exteriorRestrictOpenSubspaceIso … n` the comparison between the restricted
exterior algebra `A|_U` and an exterior algebra `B` of `M|_U` chosen on `U`,

`mul_{A|_U} i j ≫ e (i+j) = (e i ⊗ e j) ≫ mul_B i j`,

the tensor product being `PresheafOfModules.tensorSheafBifunctor` on the pair of comparisons. This
is `SheafOfModules.exteriorRestrictOpenSubspaceIso_mul` — the same statement on homogeneous local
sections — read as an equality of morphisms out of the tensor product sheaf. The comparison is the
degree-`n` component of the unital homomorphism of sheaves of graded algebras that the universal
property of `A|_U` produces from the generator of `B`. -/
theorem mulSheaf_comp_exteriorRestrictOpenSubspaceIso (i j : ℤ) :
    GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf) (openSubspaceAlg A U) i j ≫
        (exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB (i + j)).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB i).hom,
            (exteriorRestrictOpenSubspaceIso M A gen hA U B gen' hB j).hom) :
            ((openSubspaceAlg A U).piece i, (openSubspaceAlg A U).piece j) ⟶
              (B.piece i, B.piece j)) ≫
        GradedAlgebra.mulSheaf (Osharp := (restrictToOpen X U).sheaf) B i j :=
  (GradedAlgebra.tensorSheafBifunctor_map_app_comp_mulSheaf
    (J := Opens.grothendieckTopology (restrictToOpen X U).carrier)
    (Osharp := (restrictToOpen X U).sheaf)
    ((isExteriorAlgebra_openSubspaceAlg M A gen hA U).isUniversal.desc B gen'
      hB.isUniversal.1) i j).symm

end MulSquare

section ProdWedge

variable {X : RingedSpace.{u, u}} (U : Opens X.carrier)
  {F G H : SheafOfModules.{u} (structureSheafRing X)}
  (AF : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) F)
  (AG : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) G)
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology X.carrier) H)
  (AF' : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj F))
  (AG' : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj G))
  (A' : TensorExteriorSymmetricAlgebras (Osharp := (restrictToOpen X U).sheaf)
    (Opens.grothendieckTopology (restrictToOpen X U).carrier)
    ((openSubspaceRestriction U).obj H))
  (iF : F ⟶ H) (iG : G ⟶ H) (p q : ℕ)

/-- The restricted wedge-product morphism is the wedge-product morphism of bundles of algebras
chosen on the open subspace. Let `AF'`, `AG'`, `A'` be bundles of tensor, exterior and symmetric
algebras of `F|_U`, `G|_U` and `H|_U` on `U`, and write `e_F`, `e_G`, `e_A` for the comparisons
`SheafOfModules.exteriorRestrictOpenSubspaceIso` between the restrictions of the exterior algebras
of `AF`, `AG`, `A` and the exterior algebras of `AF'`, `AG'`, `A'`. Then the restriction of
`SheafOfModules.prodWedgeHom`, read through `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` and `e_A` at the target, is
`e_F ⊗ e_G` followed by `SheafOfModules.prodWedgeHom` of the bundles on `U`: the restricted wedge
product is the wedge product on `U`, conjugated by the comparisons.

The proof is `SheafOfModules.openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom`, then the
multiplication square `SheafOfModules.mulSheaf_comp_exteriorRestrictOpenSubspaceIso`, and then the
crossing of the two functorial maps on exterior powers
(`SheafOfModules.openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso`) one
tensor factor at a time. -/
theorem openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso :
    (openSubspaceTensorBifunctorIso U (AF.exteriorPower p) (AG.exteriorPower q)).inv ≫
        (openSubspaceRestriction U).map (prodWedgeHom AF AG A iF iG p q) ≫
          (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
            A.exterior_isExteriorAlgebra U A'.exterior A'.exteriorGenerator
            A'.exterior_isExteriorAlgebra ((p : ℤ) + (q : ℤ))).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictToOpen X U).sheaf)).map
          (((exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                AF.exterior_isExteriorAlgebra U AF'.exterior AF'.exteriorGenerator
                AF'.exterior_isExteriorAlgebra (p : ℤ)).hom,
            (exteriorRestrictOpenSubspaceIso G AG.exterior AG.exteriorGenerator
                AG.exterior_isExteriorAlgebra U AG'.exterior AG'.exteriorGenerator
                AG'.exterior_isExteriorAlgebra (q : ℤ)).hom) :
            ((openSubspaceRestriction U).obj (AF.exteriorPower p),
                (openSubspaceRestriction U).obj (AG.exteriorPower q)) ⟶
              (AF'.exteriorPower p, AG'.exteriorPower q)) ≫
        prodWedgeHom AF' AG' A' ((openSubspaceRestriction U).map iF)
          ((openSubspaceRestriction U).map iG) p q :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg
        (fun z => z ≫ (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra U A'.exterior A'.exteriorGenerator
          A'.exterior_isExteriorAlgebra ((p : ℤ) + (q : ℤ))).hom)
        (openSubspaceTensorBifunctorIso_inv_comp_map_prodWedgeHom U AF AG A iF iG p q))
      (Eq.trans (Category.assoc _ _ _)
        (Eq.trans
          (congrArg
            (fun z => (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                (restrictToOpen X U).sheaf)).map
                (((openSubspaceRestriction U).map
                    (AF.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iF
                      (p : ℤ)),
                  (openSubspaceRestriction U).map
                    (AG.exterior_isExteriorAlgebra.pieceMap A.exterior_isExteriorAlgebra iG
                      (q : ℤ))) :
                  ((openSubspaceRestriction U).obj (AF.exteriorPower p),
                      (openSubspaceRestriction U).obj (AG.exteriorPower q)) ⟶
                    ((openSubspaceRestriction U).obj (A.exteriorPower p),
                      (openSubspaceRestriction U).obj (A.exteriorPower q))) ≫ z)
            (mulSheaf_comp_exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
              A.exterior_isExteriorAlgebra U A'.exterior A'.exteriorGenerator
              A'.exterior_isExteriorAlgebra (p : ℤ) (q : ℤ)))
          (Eq.trans (Category.assoc _ _ _).symm
            (Eq.trans
              (congrArg
                (fun z => z ≫ GradedAlgebra.mulSheaf A'.exterior (p : ℤ) (q : ℤ))
                (bifunctorMapCompMapEq
                  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                      (restrictToOpen X U).sheaf))
                  _ _ _ _ _ _ _ _
                  (openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso U
                    AF.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra iF
                    AF'.exterior_isExteriorAlgebra A'.exterior_isExteriorAlgebra (p : ℤ))
                  (openSubspaceRestriction_map_pieceMap_comp_exteriorRestrictOpenSubspaceIso U
                    AG.exterior_isExteriorAlgebra A.exterior_isExteriorAlgebra iG
                    AG'.exterior_isExteriorAlgebra A'.exterior_isExteriorAlgebra (q : ℤ))))
              (Category.assoc _ _ _))))))

/-- The crossing of the wedge-product morphism as a commuting square:
`SheafOfModules.openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso`
with the identification `(M ⊗ L)|_U ≅ M|_U ⊗ L|_U` moved to the other side, so that both vertical
maps are isomorphisms: the restriction of `SheafOfModules.prodWedgeHom`, followed by the target
comparison, is the source isomorphism followed by `SheafOfModules.prodWedgeHom` of the bundles on
`U`. The source isomorphism is the tensor-product identification followed by the tensor bifunctor
applied to the pair of source comparisons. -/
theorem openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom :
    (openSubspaceRestriction U).map (prodWedgeHom AF AG A iF iG p q) ≫
        (exteriorRestrictOpenSubspaceIso H A.exterior A.exteriorGenerator
          A.exterior_isExteriorAlgebra U A'.exterior A'.exteriorGenerator
          A'.exterior_isExteriorAlgebra ((p : ℤ) + (q : ℤ))).hom =
      ((openSubspaceTensorBifunctorIso U (AF.exteriorPower p) (AG.exteriorPower q) ≪≫
          (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              (restrictToOpen X U).sheaf)).mapIso
            (Iso.prod
              (exteriorRestrictOpenSubspaceIso F AF.exterior AF.exteriorGenerator
                AF.exterior_isExteriorAlgebra U AF'.exterior AF'.exteriorGenerator
                AF'.exterior_isExteriorAlgebra (p : ℤ))
              (exteriorRestrictOpenSubspaceIso G AG.exterior AG.exteriorGenerator
                AG.exterior_isExteriorAlgebra U AG'.exterior AG'.exteriorGenerator
                AG'.exterior_isExteriorAlgebra (q : ℤ)))).hom) ≫
        prodWedgeHom AF' AG' A' ((openSubspaceRestriction U).map iF)
          ((openSubspaceRestriction U).map iG) p q :=
  Stacks.CategoryTheory.eq_trans_hom_comp_of_inv_comp_eq _ _ _ _
    (openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso U AF AG A
      AF' AG' A' iF iG p q)

/-- The restriction of the cokernel of the wedge-product morphism is the cokernel of the
wedge-product morphism of the bundles chosen on `U`. That cokernel is the ambient object of the
graded piece of the wedge filtration of [Stacks, Section 0FMK], so this is the identification of
targets a statement about the graded piece over the open subspace is matched against.

Restriction preserves finite colimits, which identifies the restricted cokernel with the cokernel
of the restricted morphism; the commuting square
`SheafOfModules.openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom`
then identifies that with the cokernel on `U`. -/
def prodWedgeHomCokernelOpenSubspaceIso :
    (openSubspaceRestriction U).obj (cokernel (prodWedgeHom AF AG A iF iG p q)) ≅
      cokernel (prodWedgeHom AF' AG' A' ((openSubspaceRestriction U).map iF)
        ((openSubspaceRestriction U).map iG) p q) :=
  PreservesCokernel.iso (openSubspaceRestriction U) (prodWedgeHom AF AG A iF iG p q) ≪≫
    cokernel.mapIso ((openSubspaceRestriction U).map (prodWedgeHom AF AG A iF iG p q))
      (prodWedgeHom AF' AG' A' ((openSubspaceRestriction U).map iF)
        ((openSubspaceRestriction U).map iG) p q) _ _
      (openSubspaceRestriction_map_prodWedgeHom_comp_exteriorRestrictOpenSubspaceIso_hom U AF AG A
        AF' AG' A' iF iG p q)

end ProdWedge

end SheafOfModules

end
