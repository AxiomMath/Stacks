module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceJunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison

/-!
# The derived tensor product commutes with restriction to a slice, in the internal-Hom spelling

A ringed site carries two derived tensor products on `D(Mod(𝒪))`, and
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` identifies them.  The
comparison

`(K ⊗^L_𝒪 L)|_U ≅ K|_U ⊗^L_{𝒪|_U} L|_U`

of `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` is stated over the second
of the two.  This file reads it over the first, which is the one the derived internal Hom and the
tensor–internal-Hom bijection of [Stacks, Tag 08J8] are stated over, and keeps the naturality in
the left-hand variable.

That is the form the general case of [Stacks, Tag 08EH] needs.  There a morphism `β : I ⟶ 𝒪_X`
whose restriction to `U` is invertible has to be tensored with a perfect object `E`, and the
conclusion wanted is that `(β ⊗ 1_E)|_U` is again invertible.  That does not follow from
invertibility of `β|_U` alone: it is read off the naturality square below, which conjugates
`(β ⊗ 1_E)|_U` into `β|_U ⊗ 1_{E|_U}`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorRestrictIso`: the comparison
  `(K ⊗^L_𝒪 L)|_U ≅ K|_U ⊗^L_{𝒪|_U} L|_U` over
  `Stacks.SheafOfModules.derivedTensorProductFunctor`.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorRestrictIso_naturality_source`: the
  comparison is natural in the left-hand variable.
* `Stacks.SheafOfModules.DerivedMonoidal.isIso_restriction_map_interfaceTensorMap_source`: if the
  restriction of `u : K' ⟶ K` to `U` is invertible, so is the restriction of `u ⊗ 1_L`.

## Implementation notes

The middle factor is `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso`, the
comparison as an isomorphism of functors of both variables, rather than
`Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictIso`, the comparison at a pair of
objects: the two have the same type here, but only the first comes with the naturality that is
the whole point of the file.  Reading the naturality of a bifunctor isomorphism one variable at a
time means evaluating the two functors it compares at a morphism `(u, 𝟙 L)`, and
`sourceFunctor_map_id_right` and `targetFunctor_map_id_right` are those two values with the
identity factor cancelled.

No project tag is attached.  The comparison carries none where it is constructed — Tag 08JB is
the same statement for the derived internal Hom, not for the derived tensor product — and the
content below is that construction transported along a comparison of two spellings of one
bifunctor.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (sheafTensor)
open Stacks.DerivedTensor.RingedSite (Modules)
open Stacks.DerivedTensor.ExtensionByZero (restriction)
open Stacks.DerivedTensor.SliceRestriction

namespace Stacks.SheafOfModules.DerivedMonoidal

universe u

attribute [local instance] HasDerivedCategory.standard


variable (X : RingedSite.{u, u, u}) (U : X.C)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u} X.O).Additive] [∀ M, ((sheafTensor.{u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]
  [(sheafTensor (X.O.over U)).Additive] [∀ M, ((sheafTensor (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)]

/-- Sheafification on the slice, at the localized spelling `(X.over U).J` the derived tensor
product of `X.over U` is stated over. It needs sheafification on the one slice `X.J.over U` and
nothing else, so it is stated with that single hypothesis rather than the section variables. -/
local instance sliceHasSheafify {X : RingedSite.{u, u, u}} {U : X.C}
    [HasSheafify (X.J.over U) AddCommGrpCat.{u}] : HasSheafify (X.over U).J AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (X.J.over U) AddCommGrpCat.{u})

/-- Local bijectivity of the weak equivalences on the slice, at the localized spelling, from the
same property on the one slice `X.J.over U`. -/
local instance sliceWEqualsLocallyBijective {X : RingedSite.{u, u, u}} {U : X.C}
    [(X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (X.over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u})

/-! ### Reading a bifunctor naturality square in the left-hand variable -/

/-- **The comparison of the two derived tensor products of a ringed site is natural in the
left-hand variable**, read at a fixed object in the right-hand one. -/
theorem interfaceTensorCanonicalIso_hom_naturality_source
    {K K' L : DerivedCategory (Modules X.O)} (u : K' ⟶ K) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app L ≫
        (((interfaceTensorCanonicalIso X).app K).app L).hom =
      (((interfaceTensorCanonicalIso X).app K').app L).hom ≫
        ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).map u).app L :=
  NatTrans.congr_app ((interfaceTensorCanonicalIso X).hom.naturality u) L

/-- The same square for the inverse of the comparison. -/
theorem interfaceTensorCanonicalIso_inv_naturality_source
    {K K' L : DerivedCategory (Modules X.O)} (u : K' ⟶ K) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).map u).app L ≫
        (((interfaceTensorCanonicalIso X).app K).app L).inv =
      (((interfaceTensorCanonicalIso X).app K').app L).inv ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app L :=
  NatTrans.congr_app ((interfaceTensorCanonicalIso X).inv.naturality u) L

omit [(sheafTensor.{u, u, u, u, u} (X.O.over U)).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} (X.O.over U)).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules (X.O.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor (X.O.over U)) (ComplexShape.up ℤ)] in
/-- The source of the slice comparison, evaluated at a morphism that is the identity in its
right-hand slot: the restriction of `u ⊗ 1_L`. -/
theorem sourceFunctor_map_id_right
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    {K K' : DerivedCategory (Modules X.O)} (u : K' ⟶ K)
    (L : DerivedCategory (Modules X.O)) :
    (tensorRestrictSourceFunctor X U T).map
        ((u, 𝟙 L) : ((K', L) : DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) ⟶
          (K, L)) =
      (restriction X U).mapDerivedCategory.map ((T.tensor.map u).app L) := by
  show (restriction X U).mapDerivedCategory.map
      ((T.tensor.map u).app L ≫ (T.tensor.obj K).map (𝟙 L)) = _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- The target of the slice comparison, evaluated at a morphism that is the identity in its
right-hand slot: `u|_U ⊗ 1_{L|_U}`. -/
theorem targetFunctor_map_id_right
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    {K K' : DerivedCategory (Modules X.O)} (u : K' ⟶ K)
    (L : DerivedCategory (Modules X.O)) :
    (tensorRestrictTargetFunctor X U TU).map
        ((u, 𝟙 L) : ((K', L) : DerivedCategory (Modules X.O) × DerivedCategory (Modules X.O)) ⟶
          (K, L)) =
      (TU.tensor.map ((restriction X U).mapDerivedCategory.map u)).app
        ((restriction X U).mapDerivedCategory.obj L) := by
  show (TU.tensor.map ((restriction X U).mapDerivedCategory.map u)).app
        ((restriction X U).mapDerivedCategory.obj L) ≫
      (TU.tensor.obj ((restriction X U).mapDerivedCategory.obj K)).map
        ((restriction X U).mapDerivedCategory.map (𝟙 L)) = _
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]

/-- **The slice comparison of the derived tensor product is natural in its left-hand variable.**
This is the naturality of `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` at
a morphism whose right-hand component is an identity. -/
theorem derivedTensorRestrictNatIso_hom_app_naturality_source
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.O)
    (TU : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct (X.O.over U))
    {K K' : DerivedCategory (Modules X.O)} (u : K' ⟶ K)
    (L : DerivedCategory (Modules X.O)) :
    (restriction X U).mapDerivedCategory.map ((T.tensor.map u).app L) ≫
        (derivedTensorRestrictNatIso X U T TU).hom.app (K, L) =
      (derivedTensorRestrictNatIso X U T TU).hom.app (K', L) ≫
        (TU.tensor.map ((restriction X U).mapDerivedCategory.map u)).app
          ((restriction X U).mapDerivedCategory.obj L) := by
  rw [← sourceFunctor_map_id_right X U T u L, ← targetFunctor_map_id_right X U TU u L]
  exact (derivedTensorRestrictNatIso X U T TU).hom.naturality _

/-! ### The comparison in the internal-Hom spelling -/

/-- **The derived tensor product the derived internal Hom is stated over commutes with
restriction to a slice**: for objects `K` and `L` of `D(𝒪)` and an object `U` of the site,

`(K ⊗^L_𝒪 L)|_U ≅ K|_U ⊗^L_{𝒪|_U} L|_U`.

It is `Stacks.DerivedTensor.SliceRestriction.derivedTensorRestrictNatIso` conjugated by
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` at the site and at its
localization. -/
def interfaceTensorRestrictIso (K L : DerivedCategory (Modules X.O)) :
    (restriction X U).mapDerivedCategory.obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj L) ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).obj
          ((restriction X U).mapDerivedCategory.obj K)).obj
        ((restriction X U).mapDerivedCategory.obj L) :=
  (restriction X U).mapDerivedCategory.mapIso
      (((interfaceTensorCanonicalIso X).app K).app L) ≪≫
    (derivedTensorRestrictNatIso X U
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (X.O.over U))).app (K, L) ≪≫
    (((interfaceTensorCanonicalIso (X.over U)).app
      ((restriction X U).mapDerivedCategory.obj K)).app
        ((restriction X U).mapDerivedCategory.obj L)).symm

/-- The comparison in the internal-Hom spelling, written out as its three factors. -/
theorem interfaceTensorRestrictIso_hom (K L : DerivedCategory (Modules X.O)) :
    (interfaceTensorRestrictIso X U K L).hom =
      (restriction X U).mapDerivedCategory.map
          (((interfaceTensorCanonicalIso X).app K).app L).hom ≫
        (derivedTensorRestrictNatIso X U
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              (X.O.over U))).hom.app (K, L) ≫
          (((interfaceTensorCanonicalIso (X.over U)).app
            ((restriction X U).mapDerivedCategory.obj K)).app
              ((restriction X U).mapDerivedCategory.obj L)).inv :=
  rfl

/-- **The comparison is natural in its left-hand variable.**  For a morphism `u : K' ⟶ K` of
`D(𝒪)` the restriction of `u ⊗ 1_L` is carried to `u|_U ⊗ 1_{L|_U}`. -/
theorem interfaceTensorRestrictIso_naturality_source
    {K K' : DerivedCategory (Modules X.O)} (u : K' ⟶ K) (L : DerivedCategory (Modules X.O)) :
    (restriction X U).mapDerivedCategory.map
          (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app L) ≫
        (interfaceTensorRestrictIso X U K L).hom =
      (interfaceTensorRestrictIso X U K' L).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
            ((restriction X U).mapDerivedCategory.map u)).app
          ((restriction X U).mapDerivedCategory.obj L) := by
  have h₁ := congrArg (restriction X U).mapDerivedCategory.map
    (interfaceTensorCanonicalIso_hom_naturality_source X (L := L) u)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at h₁
  have h₂ := derivedTensorRestrictNatIso_hom_app_naturality_source X U
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (X.O.over U)) u L
  have h₃ := interfaceTensorCanonicalIso_inv_naturality_source (X.over U)
    (L := (restriction X U).mapDerivedCategory.obj L) ((restriction X U).mapDerivedCategory.map u)
  simp only [interfaceTensorRestrictIso_hom, Category.assoc]
  rw [reassoc_of% h₁]
  exact whisker_eq _ ((Category.assoc _ _ _).symm.trans ((eq_whisker h₂ _).trans
    ((Category.assoc _ _ _).trans ((whisker_eq _ h₃).trans (Category.assoc _ _ _).symm))))

/-- **An invertible restriction stays invertible after tensoring.**  If `u : K' ⟶ K` restricts to
an isomorphism on `U`, then so does `u ⊗ 1_L`.  This is the naturality square above: it
conjugates the restriction of `u ⊗ 1_L` into `u|_U ⊗ 1_{L|_U}`, which is the image of an
isomorphism under a functor. -/
theorem isIso_restriction_map_interfaceTensorMap_source
    {K K' : DerivedCategory (Modules X.O)} (u : K' ⟶ K) (L : DerivedCategory (Modules X.O))
    (hu : IsIso ((restriction X U).mapDerivedCategory.map u)) :
    IsIso ((restriction X U).mapDerivedCategory.map
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app L)) := by
  have h : (restriction X U).mapDerivedCategory.map
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map u).app L) =
      (interfaceTensorRestrictIso X U K' L).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
            ((restriction X U).mapDerivedCategory.map u)).app
          ((restriction X U).mapDerivedCategory.obj L) ≫
          (interfaceTensorRestrictIso X U K L).inv := by
    rw [← Category.assoc, ← interfaceTensorRestrictIso_naturality_source X U u L,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  have : IsIso ((Stacks.SheafOfModules.derivedTensorProductFunctor (X.over U)).map
      ((restriction X U).mapDerivedCategory.map u)) :=
    CategoryTheory.Functor.map_isIso _ _
  infer_instance

end Stacks.SheafOfModules.DerivedMonoidal

end
