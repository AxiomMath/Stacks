module

public import StacksFrontier.CategoryTheory.Monoidal.BidualityTransfer
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso

/-!
# The biduality morphism of a ringed site, and its restriction to a slice

Let `(C, O)` be a ringed site and `K`, `L` objects of `D(O)`. The **biduality morphism**

`L ⟶ R𝓗om_O(R𝓗om_O(L, K), K)`

is the transpose, under the tensor–internal-hom bijection of [Stacks, Tag 08J8], of the
evaluation morphism `R𝓗om_O(L, K) ⊗^𝐋 L ⟶ K` precomposed with the commutativity constraint
`L ⊗^𝐋 R𝓗om_O(L, K) ≅ R𝓗om_O(L, K) ⊗^𝐋 L`. It is the canonical map of [Stacks, Tag 0A89].

For a subterminal object `U` of `C` (an open of a topological space), the restriction of the
biduality morphism to the slice site `C/U` is an isomorphism exactly when the biduality morphism
formed over `C/U` at `K|_U`, `L|_U` is one, and invertibility of the biduality morphism is
therefore local on a covering by such objects.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorBraiding`: the commutativity constraint of the
  derived tensor product.
* `AlgebraicGeometry.RingedSite.derivedBiduality`: the biduality morphism.

## Main results

* `AlgebraicGeometry.RingedSite.derivedBiduality_spec`: its defining identity
  `(β ⊗ 1) ≫ e = σ ≫ e`.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_map_derivedBiduality_iff`: restriction to `C/U`
  carries the biduality morphism to an isomorphism iff the biduality morphism of the restrictions
  is one.
* `Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedBiduality_of_cover`: invertibility of the
  biduality morphism is local on a covering by subterminal objects.

## References

* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

namespace AlgebraicGeometry.RingedSite

section Site

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- The commutativity constraint `A ⊗^𝐋 B ≅ B ⊗^𝐋 A` of the derived tensor product of
[Stacks, Tag 08J8], the braiding of `AlgebraicGeometry.RingedSite.derivedTensorSymmetric`. -/
def derivedTensorBraiding
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B).obj A :=
  letI := derivedTensorMonoidal X
  letI := derivedTensorSymmetric X
  β_ A B

/-- The commutativity constraint is natural in its second variable. -/
theorem derivedTensorBraiding_naturality_right
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : B ⟶ B') :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map g ≫
        (derivedTensorBraiding X A B').hom =
      (derivedTensorBraiding X A B).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map g).app A := by
  let := derivedTensorMonoidal X
  let := derivedTensorSymmetric X
  exact BraidedCategory.braiding_naturality_right A g

/-- The commutativity constraint is natural in its first variable. -/
theorem derivedTensorBraiding_naturality_left
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : A ⟶ A')
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map f).app B ≫
        (derivedTensorBraiding X A' B).hom =
      (derivedTensorBraiding X A B).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B).map f := by
  let := derivedTensorMonoidal X
  let := derivedTensorSymmetric X
  exact BraidedCategory.braiding_naturality_left f B

/-- `R𝓗om_O(L, K)`, the derived internal hom out of `L` into `K`. -/
abbrev derivedDualInto
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  ((derivedSheafHomBifunctor X).obj (op L)).obj K

/-- **The biduality morphism** `L ⟶ R𝓗om_O(R𝓗om_O(L, K), K)` of [Stacks, Tag 0A89]: the transpose
under the bijection of [Stacks, Tag 08J8] of the evaluation `R𝓗om_O(L, K) ⊗^𝐋 L ⟶ K` after the
commutativity constraint. -/
def derivedBiduality
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    L ⟶ derivedDualInto X K (derivedDualInto X K L) :=
  (derivedCurryHomEquiv X L (derivedDualInto X K L) K).symm
    ((derivedTensorBraiding X L (derivedDualInto X K L)).hom ≫ derivedSheafHomCounit X L K)

/-- **The defining identity of the biduality morphism**: tensored with `R𝓗om_O(L, K)` and followed
by evaluation it is the commutativity constraint followed by evaluation. -/
theorem derivedBiduality_spec
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map (derivedBiduality X K L)).app
        (derivedDualInto X K L) ≫ derivedSheafHomCounit X (derivedDualInto X K L) K =
      (derivedTensorBraiding X L (derivedDualInto X K L)).hom ≫ derivedSheafHomCounit X L K := by
  rw [← derivedCurryHomEquiv_apply, derivedBiduality, AddEquiv.apply_symm_apply]

/-- **Evaluation is dinatural in the internal-hom variable.** For `g : Z ⟶ L`, the morphism
`R𝓗om(L, K) ⟶ R𝓗om(Z, K)` induced by `g`, tensored with `Z` and followed by evaluation, is
`R𝓗om(L, K) ⊗ g` followed by evaluation. -/
theorem derivedSheafHomCounit_dinatural
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {Z L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : Z ⟶ L) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        (((derivedSheafHomBifunctor X).map g.op).app K)).app Z ≫ derivedSheafHomCounit X Z K =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (derivedDualInto X K L)).map g ≫
        derivedSheafHomCounit X L K := by
  rw [← derivedCurryHomEquiv_apply]
  have e : ((derivedSheafHomBifunctor X).map g.op).app K =
      𝟙 (derivedDualInto X K L) ≫ 𝟙 (derivedDualInto X K L) ≫
        (((derivedSheafHomBifunctor X).map g.op).app K ≫
          ((derivedSheafHomBifunctor X).obj (op Z)).map (𝟙 K)) := by
    simp only [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e, derivedCurryHomEquiv_naturality]
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
  rw [derivedSheafHomCounit]

/-- **The biduality morphism is natural** in its argument: for `g : L ⟶ L'`,
`g ≫ β_{L'} = β_L ≫ R𝓗om(R𝓗om(g, K), K)`. -/
theorem derivedBiduality_naturality
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L ⟶ L') :
    g ≫ derivedBiduality X K L' = derivedBiduality X K L ≫
      ((derivedSheafHomBifunctor X).map
        (((derivedSheafHomBifunctor X).map g.op).app K).op).app K :=
  CategoryTheory.BidualityTransfer.comp_biduality_eq
    (Stacks.SheafOfModules.derivedTensorProductFunctor X) (derivedTensorBraiding X)
    (fun f B ↦ derivedTensorBraiding_naturality_left X f B)
    (fun A _ _ f ↦ derivedTensorBraiding_naturality_right X A f) g
    (derivedSheafHomCounit X L K) (derivedSheafHomCounit X L' K)
    (derivedSheafHomCounit X _ K) (derivedSheafHomCounit X _ K)
    (fun W ↦ (Stacks.Cohomology.SliceDerivedSheafHom.bijective_derivedSheafHomCounit X W _ K).1)
    (derivedBiduality X K L) (derivedBiduality_spec X K L)
    (derivedBiduality X K L') (derivedBiduality_spec X K L')
    _ (derivedSheafHomCounit_dinatural X K g) _ (derivedSheafHomCounit_dinatural X K _)

end Site

end AlgebraicGeometry.RingedSite

namespace Stacks.Cohomology.SliceDerivedSheafHom

section Slice

variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules (X.over U).O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over U).O)
      (ComplexShape.up ℤ)]
  [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit]

omit [HasBinaryProducts X.C] [IsIso (Over.forgetAdjStar U).unit] in
/-- The slice tensor comparison is natural in its second variable. -/
theorem sliceTensorRestrictionObjIso_naturality_right
    (A : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : B ⟶ B') :
    (restrictD X U).map (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).map g) ≫
        (sliceTensorRestrictionObjIso X U A B').hom =
      (sliceTensorRestrictionObjIso X U A B).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
          ((restrictD X U).obj A)).map ((restrictD X U).map g) := by
  rw [← sliceTensorRestrictionNatIso_hom_app_app, ← sliceTensorRestrictionNatIso_hom_app_app]
  exact ((sliceTensorRestrictionNatIso X U).hom.app A).naturality g

/-- The projection formula with the extension by zero in the second factor,
`L ⊗^𝐋 j_!Z ≅ j_!(L|_U ⊗^𝐋 Z)`, from `projectionIso` and the two commutativity constraints. -/
def projectionIsoRight
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj L).obj ((extensionD X U).obj Z) ≅
      (extensionD X U).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
          ((restrictD X U).obj L)).obj Z) :=
  RingedSite.derivedTensorBraiding X L _ ≪≫ projectionIso X U Z L ≪≫
    (extensionD X U).mapIso (RingedSite.derivedTensorBraiding (X.over U) Z _)

/-- **Restriction to a subterminal object carries the biduality morphism to an isomorphism exactly
when the biduality morphism of the restrictions is one.** -/
theorem isIso_map_derivedBiduality_iff
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    IsIso ((restrictD X U).map (RingedSite.derivedBiduality X K L)) ↔
      IsIso (RingedSite.derivedBiduality (X.over U) ((restrictD X U).obj K)
        ((restrictD X U).obj L)) := by
  have := Stacks.DerivedTensor.ExtensionByZero.isIso_derivedAdjunction_unit X U
  exact CategoryTheory.BidualityTransfer.isIso_map_iff
    (Stacks.SheafOfModules.derivedTensorProductFunctor X)
    (Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U))
    (RingedSite.derivedTensorBraiding X) (RingedSite.derivedTensorBraiding (X.over U))
    (Stacks.DerivedTensor.ExtensionByZero.derivedAdjunction X U)
    (sliceTensorRestrictionObjIso X U)
    (fun f B ↦ sliceTensorRestrictionObjIso_naturality X U f B)
    (fun A _ _ g ↦ sliceTensorRestrictionObjIso_naturality_right X U A g)
    (projectionIso X U) (projectionIsoRight X U)
    (fun L _ _ g ↦ RingedSite.derivedTensorBraiding_naturality_right X L g)
    (fun L _ _ g ↦ RingedSite.derivedTensorBraiding_naturality_right (X.over U) L g)
    (RingedSite.derivedSheafHomCounit X L K) (fun Z ↦ bijective_derivedSheafHomCounit X Z L K)
    (RingedSite.derivedSheafHomCounit X _ K) (fun Z ↦ bijective_derivedSheafHomCounit X Z _ K)
    (RingedSite.derivedBiduality X K L) (RingedSite.derivedBiduality_spec X K L)
    (RingedSite.derivedSheafHomCounit (X.over U) _ _)
    (fun Z ↦ bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (RingedSite.derivedSheafHomCounit (X.over U) _ _)
    (fun Z ↦ bijective_derivedSheafHomCounit (X.over U) Z _ _)
    (RingedSite.derivedBiduality (X.over U) _ _) (RingedSite.derivedBiduality_spec (X.over U) _ _)

end Slice

section Cover

variable (X : RingedSite.{u, u, u}) [HasBinaryProducts X.C]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- **Invertibility of the biduality morphism is local.** If `Y` is a family of subterminal
objects covering the ringed site and the biduality morphism of `K|_{Y i}`, `L|_{Y i}` is an
isomorphism over each `C/Y i`, then the biduality morphism of `K`, `L` is an isomorphism. -/
theorem isIso_derivedBiduality_of_cover
    {ι : Type*} {Y : ι → X.C} (hY : X.J.CoversTop Y)
    [∀ i, IsIso (Over.forgetAdjStar (Y i)).unit]
    [∀ i, HasSheafify (X.J.over (Y i)) AddCommGrpCat.{u}]
    [∀ i, (X.J.over (Y i)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ i, (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Y i)).Additive]
    [∀ i, (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).Additive]
    [∀ i, ∀ M, ((sheafTensor.{u, u, u, u, u} (X.over (Y i)).O).obj M).Additive]
    [∀ i, ∀ (K L : CochainComplex (Modules (X.over (Y i)).O) ℤ),
      HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} (X.over (Y i)).O)
        (ComplexShape.up ℤ)]
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ i, IsIso (RingedSite.derivedBiduality (X.over (Y i)) ((restrictD X (Y i)).obj K)
      ((restrictD X (Y i)).obj L))) :
    IsIso (RingedSite.derivedBiduality X K L) :=
  Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_overFunctor hY _
    fun i ↦ (isIso_map_derivedBiduality_iff X (Y i) K L).2 (h i)

end Cover

end Stacks.Cohomology.SliceDerivedSheafHom
