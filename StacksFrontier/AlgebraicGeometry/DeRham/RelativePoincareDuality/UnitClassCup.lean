module

public import StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TraceUniqueness
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductCommutativity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaUnitKFlat

/-!
# Cup product with the class of an isomorphism out of the structure sheaf

Let `f : X ⟶ S` be a morphism of schemes, `K, M ∈ D(𝒪_X)` and `x : Lf^*𝒪_S ⟶ K` an isomorphism,
with class `ξ : 𝒪_S ⟶ Rf_*K` under `Lf^* ⊣ Rf_*`. Then the cup product with `ξ`,

`𝒪_S ⊗^L Rf_*M ⟶ Rf_*K ⊗^L Rf_*M ⟶ Rf_*(K ⊗^L M)`,

is an isomorphism. After the symmetry of `⊗^L` it is the projection-formula morphism
`Rf_*M ⊗^L 𝒪_S ⟶ Rf_*(M ⊗^L Lf^*𝒪_S)` of [Stacks, Tag 0B53], which is invertible
([Stacks, Tag 08EU] at `𝒪_S`), followed by `Rf_*` of `1 ⊗ x` and of the symmetry: the relative cup
product is the projection-formula morphism followed by the counit ([Stacks, Tag 0B68]), and on the
class `ξ = η ≫ Rf_*x` the counit cancels against the unit by the triangle identity.

## Main results

* `Stacks.Cohomology.DerivedRelativeCupProduct.isIso_homEquiv_map_app_comp_relativeCupProduct`.
-/

@[expose] public noncomputable section

open scoped Stacks.StandardDerivedModel Stacks.Topology.SheafTensorAdditiveOnOpens
open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Cohomology.DerivedRelativeCupProduct

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Cup product with the class of an isomorphism out of `Lf^*𝒪_Y` is an isomorphism**: for
`x : Lf^*𝒪_Y ⟶ K` invertible with class `ξ : 𝒪_Y ⟶ Rf_*K`, the map
`𝒪_Y ⊗^L Rf_*M ⟶ Rf_*K ⊗^L Rf_*M ⟶ Rf_*(K ⊗^L M)` is invertible. -/
theorem isIso_homEquiv_map_app_comp_relativeCupProduct
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (x : (derivedPullback f).obj (Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y) ⟶ K)
    [IsIso x] :
    IsIso (((derivedTensorProductFunctor Y.sheaf).map
        ((derivedAdjunction f).homEquiv _ _ x)).app ((derivedPushforward f).obj M) ≫
      relativeCupProduct f K M) := by
  have hA := derivedBraiding_naturality Y (𝟙 ((derivedPushforward f).obj M))
    ((derivedAdjunction f).homEquiv _ _ x)
  have hA' : ((derivedTensorProductFunctor Y.sheaf).obj ((derivedPushforward f).obj M)).map
        ((derivedAdjunction f).homEquiv _ _ x) ≫
      derivedBraiding Y ((derivedPushforward f).obj M) ((derivedPushforward f).obj K) =
      derivedBraiding Y ((derivedPushforward f).obj M) (DerivedProjectionFormula.singleUnit Y) ≫
        ((derivedTensorProductFunctor Y.sheaf).map ((derivedAdjunction f).homEquiv _ _ x)).app
          ((derivedPushforward f).obj M) :=
    (congrArg (· ≫ _) (DerivedProjectionFormula.uncurry_map_id_left
      (T := (derivedTensorProductFunctor Y.sheaf)) ((derivedPushforward f).obj M)
        ((derivedAdjunction f).homEquiv _ _ x)).symm).trans
      (hA.trans (congrArg (_ ≫ ·) (DerivedProjectionFormula.uncurry_map_id_right
        (T := (derivedTensorProductFunctor Y.sheaf)) ((derivedAdjunction f).homEquiv _ _ x)
          ((derivedPushforward f).obj M))))
  have hB := relativeCupProduct_braiding f M K
  have hξ : (derivedAdjunction f).homEquiv _ _ x =
      (derivedAdjunction f).unit.app (DerivedProjectionFormula.singleUnit Y) ≫
        (derivedPushforward f).map x :=
    (derivedAdjunction f).homEquiv_unit _ _ x
  have hC := relativeCupProduct_natural_right f M x
  have hD₁ := relativeCupProduct_eq_projectionFormulaMap
    f M ((derivedPullback f).obj (DerivedProjectionFormula.singleUnit Y))
  have hD₂ := DerivedProjectionFormula.projectionFormulaMap_natural_right f M
    ((derivedAdjunction f).unit.app (DerivedProjectionFormula.singleUnit Y))
  have htri : (derivedPullback f).map
        ((derivedAdjunction f).unit.app (DerivedProjectionFormula.singleUnit Y)) ≫
      (derivedAdjunction f).counit.app
        ((derivedPullback f).obj (DerivedProjectionFormula.singleUnit Y)) = 𝟙 _ :=
    (derivedAdjunction f).left_triangle_components (DerivedProjectionFormula.singleUnit Y)
  have : IsIso (derivedBraiding Y ((derivedPushforward f).obj M)
      (DerivedProjectionFormula.singleUnit Y)) := by
    dsimp only [derivedBraiding]; infer_instance
  have hβX : IsIso (derivedBraiding X M K) := by
    dsimp only [derivedBraiding]; infer_instance
  have := DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional
    f M
  -- `β ≫ (ξ ⊗ 1) ≫ cup_{K,M} = (1 ⊗ ξ) ≫ cup_{M,K} ≫ Rf_*β`
  have key := ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ relativeCupProduct f K M) hA'.symm)).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hB))
  -- the triangle identity, under `Rf_*(M ⊗ -)`
  have H := (CategoryTheory.Functor.map_comp _ _ _).symm.trans
    ((congrArg (derivedPushforward f).map ((CategoryTheory.Functor.map_comp
      ((derivedTensorProductFunctor X.sheaf).obj M) _ _).symm.trans
        ((congrArg ((derivedTensorProductFunctor X.sheaf).obj M).map htri).trans
          (CategoryTheory.Functor.map_id _ _)))).trans (CategoryTheory.Functor.map_id _ _))
  -- `(1 ⊗ η) ≫ cup_{M, Lf^*𝒪} = PF(M, 𝒪)`
  have hη := ((congrArg (_ ≫ ·) hD₁).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hD₂).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) H))))).trans
    (Category.comp_id _)
  -- `(1 ⊗ ξ) ≫ cup_{M,K} = PF(M, 𝒪) ≫ Rf_*(1 ⊗ x)`
  have hξc := ((congrArg (fun z => (_ : _ ⥤ _).map z ≫ relativeCupProduct f M K) hξ).trans
    ((congrArg (· ≫ _) (CategoryTheory.Functor.map_comp _ _ _)).trans ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) hC)))).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hη))
  have hfinal := key.trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hξc))
  have hiso : IsIso ((DerivedProjectionFormula.projectionFormulaMap f M
      (DerivedProjectionFormula.singleUnit Y) ≫
        (derivedPushforward f).map (((derivedTensorProductFunctor X.sheaf).obj M).map x)) ≫
      (derivedPushforward f).map (derivedBraiding X M K)) := by
    have h₁ := DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject_unconditional
      f M
    have h₂ := @Functor.map_isIso _ _ _ _ _ _ ((derivedTensorProductFunctor X.sheaf).obj M) x
      ‹IsIso x›
    have h₃ := @Functor.map_isIso _ _ _ _ _ _ (derivedPushforward f) _ h₂
    have h₄ := @Functor.map_isIso _ _ _ _ _ _ (derivedPushforward f) _ hβX
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₃) h₄
  have := (congrArg IsIso hfinal).mpr hiso
  exact IsIso.of_isIso_comp_left (derivedBraiding Y ((derivedPushforward f).obj M)
    (DerivedProjectionFormula.singleUnit Y)) _

end Stacks.Cohomology.DerivedRelativeCupProduct

end
