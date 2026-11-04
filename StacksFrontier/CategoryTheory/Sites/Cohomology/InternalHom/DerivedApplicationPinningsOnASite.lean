module

public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedAssociatorToTensorOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.DualityPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitLeftFactorCollapse
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.UnitRightFactorCollapse

/-!
# The unit constraints of `D(O)` against the derived tensor product, on a ringed site

Let `(C, O)` be a ringed site.  This file states the two unit constraints of the monoidal
structure `AlgebraicGeometry.RingedSite.derivedTensorMonoidal` on `D(O)` with the bifunctor
spelling of their sources, the one-sided K-flat comparison of the derived tensor product at the
unit in each factor, the identification of each unit constraint with the corresponding unit
collapse of complexes, and the one-variable forms of the two-variable maps on derived internal
Hom and on derived tensor products at an identity of the structure sheaf.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedLeftUnitorHom`,
  `AlgebraicGeometry.RingedSite.derivedRightUnitorHom`: the two unit constraints of
  `AlgebraicGeometry.RingedSite.derivedTensorMonoidal`, ascribed at the bifunctor spelling of
  their sources.
* `AlgebraicGeometry.RingedSite.unitComparisonHom`,
  `AlgebraicGeometry.RingedSite.unitComparisonRightHom`: the one-sided K-flat comparison of the
  derived tensor product with the structure sheaf in degree zero in the left, respectively the
  right, factor.

## Main results

* `AlgebraicGeometry.RingedSite.derivedLeftUnitorHom_eq_comparison` and
  `AlgebraicGeometry.RingedSite.derivedRightUnitorHom_eq_comparison`: each unit constraint of
  `D(O)`, read on the class of a K-flat complex, is the K-flat comparison at the unit followed
  by the image of the corresponding unit collapse of complexes.
* `AlgebraicGeometry.RingedSite.derivedSheafHomMap_unit_left`,
  `AlgebraicGeometry.RingedSite.derivedTensorMap_unit_left`,
  `AlgebraicGeometry.RingedSite.derivedTensorMap_unit_right`: the one-variable spellings of the
  two-variable maps at an identity of the structure sheaf.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
* [Stacks Project, Tag 0FNG](https://stacks.math.columbia.edu/tag/0FNG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FPC](https://stacks.math.columbia.edu/tag/0FPC)
* [Stacks Project, Tag 0FPU](https://stacks.math.columbia.edu/tag/0FPU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
  Opposite
open Stacks.SheafOfModules.Tensor (sheafTensor tensorComplex)
open Stacks.Cohomology.ModuleSections

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)]

/-- `⊗_O` as a monoidal structure on `Mod(O)`, with its universes pinned to the diagonal. -/
local instance monoidalCategoryModSite :
    MonoidalCategory (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) :=
  SheafOfModules.monoidalCategorySheafTensor (J := X.J) X.O

/-- `Mod(O)` is monoidal closed at the `DerivedMonoidal.Mod` spelling, with its universes
pinned to the diagonal. -/
local instance monoidalClosedModSite :
    MonoidalClosed (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) :=
  SheafOfModules.monoidalClosedSheafTensor (J := X.J) X.O

/-- The monoidal structure on `Comp(Mod(O))`. -/
local instance (priority := 100000) monoidalCategoryStructComplexesPin :
    MonoidalCategoryStruct
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :=
  inferInstance

/-! ### The left unit constraint -/

/-- The left unit constraint `λ_ K : O ⊗^𝐋_O K ⟶ K` of the monoidal structure
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` on `D(O)`, with its source written as an
application of the derived tensor bifunctor. -/
def derivedLeftUnitorHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (derivedStructureSheaf X)).obj K ⟶ K :=
  letI := derivedTensorMonoidal X
  (λ_ K).hom

/-- The right unit constraint `ρ_ K : K ⊗^𝐋_O O ⟶ K` of the monoidal structure
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal` on `D(O)`, with its source written as an
application of the derived tensor bifunctor. -/
def derivedRightUnitorHom
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj K).obj
      (derivedStructureSheaf X) ⟶ K :=
  letI := derivedTensorMonoidal X
  (ρ_ K).hom

section Monoidal

attribute [local instance] derivedTensorMonoidal

/-- `AlgebraicGeometry.RingedSite.derivedLeftUnitorHom` *is* the left unitor of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`. -/
theorem derivedLeftUnitorHom_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedLeftUnitorHom X K = (λ_ K).hom :=
  rfl

/-- `AlgebraicGeometry.RingedSite.derivedRightUnitorHom` *is* the right unitor of
`AlgebraicGeometry.RingedSite.derivedTensorMonoidal`. -/
theorem derivedRightUnitorHom_eq
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedRightUnitorHom X K = (ρ_ K).hom :=
  rfl

/-- The left unit constraint of `D(O)` is natural: for `k : K' ⟶ K` the square formed by
`λ_ K` and `λ_ K'` commutes. -/
theorem derivedLeftUnitorHom_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (derivedStructureSheaf X)).map k ≫ derivedLeftUnitorHom X K =
      derivedLeftUnitorHom X K' ≫ k :=
  MonoidalCategory.leftUnitor_naturality k

/-- The right unit constraint of `D(O)` is natural: for `a : A' ⟶ A` the square formed by
`ρ_ A` and `ρ_ A'` commutes. -/
theorem derivedRightUnitorHom_naturality
    {A A' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map a).app
          (derivedStructureSheaf X) ≫ derivedRightUnitorHom X A =
      derivedRightUnitorHom X A' ≫ a :=
  MonoidalCategory.rightUnitor_naturality a

end Monoidal

/-! ### The K-flat comparison at the unit -/

/-- The one-sided K-flat comparison `O ⊗^𝐋_O Q(L) ⟶ Q(Tot(O[0] ⊗_O L))` of the derived tensor
product, for a K-flat complex `L`, with the structure sheaf in degree zero in the left factor. -/
def unitComparisonHom
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (derivedStructureSheaf X)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj
        (((tensorComplex X.O).obj (structureSheafComplex X)).obj L) :=
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
    (structureSheafComplex X) L hL).hom

/-- The one-sided K-flat comparison `Q(A) ⊗^𝐋_O O ⟶ Q(Tot(A ⊗_O O[0]))` of the derived tensor
product, with the structure sheaf in degree zero in the right factor. -/
def unitComparisonRightHom
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj A)).obj (derivedStructureSheaf X) ⟶
      DerivedCategory.Q.obj (((tensorComplex X.O).obj A).obj (structureSheafComplex X)) :=
  ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight A
    (structureSheafComplex X) hO).hom

/-- `AlgebraicGeometry.RingedSite.unitComparisonHom` is the two-sided K-flat comparison of
`AlgebraicGeometry.RingedSite.derivedTensorReseatDatum` at the unit of `Comp(Mod(O))` in the left
factor. -/
theorem unitComparisonHom_eq
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    unitComparisonHom X L hL =
      ((derivedTensorReseatDatum X).comparison
        (𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) L
        (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O) hL).hom :=
  congrArg Iso.hom ((derivedTensorReseatDatum X).comparisonRight_eq_comparison
    (𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) L
    (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O) hL)

/-- `AlgebraicGeometry.RingedSite.unitComparisonRightHom` is the two-sided K-flat comparison of
`AlgebraicGeometry.RingedSite.derivedTensorReseatDatum` at the unit of `Comp(Mod(O))` in the right
factor. -/
theorem unitComparisonRightHom_eq
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) :
    unitComparisonRightHom X A hO =
      ((derivedTensorReseatDatum X).comparison A
        (𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) hA
        (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O)).hom :=
  congrArg Iso.hom ((derivedTensorReseatDatum X).comparisonRight_eq_comparison A
    (𝟙_ (Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O)) hA
    (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O))

/-- Re-seating followed by any morphism equal to the K-flat comparison of
`AlgebraicGeometry.RingedSite.derivedTensorReseatDatum` is the K-flat derived tensor isomorphism. -/
private theorem reseatIso_comp_eq_derivedTensorIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat X.O K) (hL : Stacks.SheafOfModules.IsKFlat X.O L)
    {f : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (DerivedCategory.Q.obj K)).obj
      (DerivedCategory.Q.obj L) ⟶ DerivedCategory.Q.obj (((tensorComplex X.O).obj K).obj L)}
    (hf : f = ((derivedTensorReseatDatum X).comparison K L hK hL).hom) :
    letI := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
    (reseatIso
        (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
          (derivedTensorReseatDatum X))
        (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)).hom ≫ f =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
        (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O) hK hL).hom :=
  (congrArg _ hf).trans
    (Stacks.SheafOfModules.DerivedMonoidal.reseatIso_comp_comparison X.O
      (derivedTensorReseatDatum X) K L hK hL)

/-- The left unit constraint of `D(O)` is the left unit collapse of complexes, carried across
by the K-flat comparison of the derived tensor product: on the class of a K-flat complex `L`,

`λ_ (Q L) = (comparison at the unit) ≫ Q (Tot(O[0] ⊗_O L) ≅ L)`. -/
theorem derivedLeftUnitorHom_eq_comparison
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    derivedLeftUnitorHom X (DerivedCategory.Q.obj L) =
      unitComparisonHom X L hL ≫
        DerivedCategory.Q.map (structureSheafComplexTensorLeftIso X L).hom :=
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  reseat_leftUnitor_comp_of_unitality
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
      (derivedTensorReseatDatum X))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)
    (DerivedCategory.Q.map (structureSheafComplexTensorLeftIso X L).hom)
    (reseatIso_comp_eq_derivedTensorIso X _ L
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O) hL
      (unitComparisonHom_eq X L hL))
    (CochainComplex.KFlatMonoidal.leftUnitor_derivedTensorIso
      (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O) hL)

/-- The right unit constraint of `D(O)` is the right unit collapse of complexes, carried across
by the K-flat comparison of the derived tensor product: on the class of a K-flat complex `A`,

`ρ_ (Q A) = (comparison at the unit on the right) ≫ Q (Tot(A ⊗_O O[0]) ≅ A)`. -/
theorem derivedRightUnitorHom_eq_comparison
    (A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A)
    (hO : Stacks.SheafOfModules.IsKFlat X.O (structureSheafComplex X)) :
    derivedRightUnitorHom X (DerivedCategory.Q.obj A) =
      unitComparisonRightHom X A hO ≫
        DerivedCategory.Q.map (structureSheafComplexTensorRightIso X A).hom :=
  let := Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.O
  reseat_rightUnitor_comp_of_unitality
    (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.O
      (derivedTensorReseatDatum X))
    (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.O)
    (DerivedCategory.Q.map (structureSheafComplexTensorRightIso X A).hom)
    (reseatIso_comp_eq_derivedTensorIso X A _ hA
      (Stacks.SheafOfModules.DerivedMonoidal.kFlat_tensorUnit_complexes X.O)
      (unitComparisonRightHom_eq X A hA hO))
    (CochainComplex.KFlatMonoidal.rightUnitor_derivedTensorIso
      (Stacks.SheafOfModules.DerivedMonoidal.Mod X.O)
      (Stacks.SheafOfModules.DerivedMonoidal.exists_kFlat_resolution X.O) hA)

/-! ### One-variable spellings of the two-variable maps -/

/-- The two-variable map on derived internal Hom induced by isomorphisms `a` and `b` is an
isomorphism. -/
instance isIsoDerivedSheafHomMapAtTheUnit
    {A A' B B' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : A' ⟶ A) (b : B ⟶ B') [IsIso a] [IsIso b] :
    IsIso (derivedSheafHomMap X (derivedInternalHomOfBifunctor X) a b) := by
  change IsIso (((derivedSheafHomBifunctor X).map a.op).app B ≫
    ((derivedSheafHomBifunctor X).obj (op A')).map b)
  infer_instance

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
  HomologicalComplex.HasMapBifunctor K₁ K₂ (sheafTensor X.O) (ComplexShape.up ℤ)] in
/-- At the identity of the structure sheaf in the source, the two-variable map on derived
internal Hom is the map induced by the target alone. -/
theorem derivedSheafHomMap_unit_left
    {A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (ψ : A ⟶ B) :
    derivedSheafHomMap X (derivedInternalHomOfBifunctor X)
        (𝟙 (derivedStructureSheaf X)) ψ =
      ((derivedSheafHomBifunctor X).obj (op (derivedStructureSheaf X))).map ψ :=
  derivedSheafHomMap_id_left X (derivedInternalHomOfBifunctor X) _ ψ

/-- At the identity of the structure sheaf in the left factor, the two-variable map on derived
tensor products is the map induced by the right factor alone. -/
theorem derivedTensorMap_unit_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K' ⟶ K) :
    derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
        (𝟙 (derivedStructureSheaf X)) k =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (derivedStructureSheaf X)).map k :=
  derivedTensorMap_id_left X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) _ k

/-- At the identity in the right tensor factor, the two-variable map on derived tensor products
is the map induced by the left factor alone. -/
theorem derivedTensorMap_unit_right
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K') :
    derivedTensorMap X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) k
        (𝟙 (derivedStructureSheaf X)) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map k).app
        (derivedStructureSheaf X) :=
  derivedTensorMap_id_right X (Stacks.SheafOfModules.canonicalDerivedTensorProduct X) k _

/-- The identification `AlgebraicGeometry.RingedSite.derivedStructureSheafGlobalSectionsEquiv`
of `H⁰(C, Z)` with `Hom_{D(O)}(O, Z)` is the collapse `R𝓗om_O(O, Z) ≅ Z` run backwards on global
hypercohomology followed by the identification of `H⁰(C, R𝓗om_O(O, Z))` with
`Hom_{D(O)}(O, Z)`. -/
theorem derivedStructureSheafGlobalSectionsEquiv_apply
    (Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj Z) : Type u)) :
    derivedStructureSheafGlobalSectionsEquiv X Z x =
      derivedSheafHomGlobalSectionsEquiv X (derivedStructureSheaf X) Z
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedStructureSheafHomIso X Z).inv) x) :=
  rfl

end AlgebraicGeometry.RingedSite

end
