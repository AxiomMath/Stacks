module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StructureSheafModulesMonoidal

/-!
# The associativity constraint of `D(O_X)` on K-flat representatives

Let `(X, O_X)` be a ringed space.  The monoidal structure
`Stacks.SheafOfModules.derivedMonoidalStructure` of Stacks 0FPT on `D(O_X)` is a re-seating of
the monoidal structure of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` onto the
derived tensor bifunctor of Stacks 06YU, so its associator is the associator of that structure
conjugated by the re-seating isomorphism.  On the classes of K-flat complexes it is computed by

`(comparison K L) ▷ QM ≫ (comparison (K ⊗ L) M) ≫ Q(α_ K L M).hom =`
`  (α_ (QK) (QL) (QM)).hom ≫ (QK ◁ (comparison L M)) ≫ (comparison K (L ⊗ M))`.

## Main definitions

* `Stacks.SheafOfModules.derivedTensorComparisonHom`: the K-flat comparison of Stacks 06YU,
  ascribed at the bifunctor spelling of its source.
* `Stacks.SheafOfModules.DerivedAssociatorComparison`: the identity displayed above, as a
  proposition.

## Main results

* `Stacks.SheafOfModules.derivedAssociator_comparison`: the identity displayed above holds.

## Implementation notes

The K-flat comparison is pinned as `Stacks.SheafOfModules.derivedTensorComparisonHom`, the
associator of complexes as `Stacks.SheafOfModules.complexAssociatorHomSpace`, the associativity
clause is stated as the `Prop`-valued `def` `Stacks.SheafOfModules.DerivedAssociatorComparison`,
and `Stacks.SheafOfModules.reseatIso_comp_derivedTensorComparisonHom` is a separate declaration:
elaborating these inside the associativity clause exhausts its heartbeat budget.

The complexes are written over `StructureSheafModules Rc`, while the K-flat localization is
written over `Stacks.SheafOfModules.DerivedMonoidal.Mod Rc`. The two are the same category, but
instance search does not cross between the spellings, and does not unfold `TopCat.Sheaf` to find
`SheafOfModules.monoidalCategorySheafTensor`; so four local instances supply the monoidal
structures at the second spelling, with the site given by hand. `monoidalPreadditiveModAC` is
what supplies the additivity of `CategoryTheory.MonoidalCategory.curriedTensor` that the K-flat
localization asks for. The top-priority local instance `monoidalCategoryStructComplexesAC` avoids
a default search over the monoidal instances on the K-flat subcategories, which the statements
below cannot afford.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] Stacks.SheafOfModules.monoidalSpace'
  Stacks.SheafOfModules.symmetricSpace' Stacks.SheafOfModules.monoidalPreadditiveSpace'
  Stacks.SheafOfModules.monoidalClosedSpace'

/-- `⊗_{O_X}` at the spelling `Stacks.SheafOfModules.DerivedMonoidal.Mod Rc`. -/
local instance monoidalCategoryModAC : MonoidalCategory (DerivedMonoidal.Mod Rc) :=
  SheafOfModules.monoidalCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is bilinear on morphisms, at the `Stacks.SheafOfModules.DerivedMonoidal.Mod Rc`
spelling. -/
local instance monoidalPreadditiveModAC : MonoidalPreadditive (DerivedMonoidal.Mod Rc) :=
  SheafOfModules.monoidalPreadditiveSheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `⊗_{O_X}` is symmetric, at the `Stacks.SheafOfModules.DerivedMonoidal.Mod Rc` spelling. -/
local instance symmetricCategoryModAC : SymmetricCategory (DerivedMonoidal.Mod Rc) :=
  SheafOfModules.symmetricCategorySheafTensor (J := Opens.grothendieckTopology X) Rc

/-- `Mod(O_X)` is monoidal closed, at the `Stacks.SheafOfModules.DerivedMonoidal.Mod Rc`
spelling. -/
@[instance_reducible]
local instance monoidalClosedModAC : MonoidalClosed (DerivedMonoidal.Mod Rc) :=
  SheafOfModules.monoidalClosedSheafTensor (J := Opens.grothendieckTopology X) Rc

variable [(Tensor.sheafTensor.{u, u, u, u, u} Rc).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} Rc).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} Rc)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor Rc) (ComplexShape.up ℤ)]

attribute [local instance 10000] CochainComplex.symmetricCategory

/-- The monoidal structure on `Comp(Mod(O_X))`, as a top-priority local instance. -/
local instance (priority := 100000) monoidalCategoryStructComplexesAC :
    MonoidalCategoryStruct (CochainComplex (StructureSheafModules Rc) ℤ) := inferInstance

/-- **The K-flat comparison of Stacks 06YU**, ascribed at the bifunctor spelling of its source and
at the `⊗` spelling of its target. -/
def derivedTensorComparisonHom (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (hK : KFlat Rc K) (hL : KFlat Rc L) :
    ((derivedTensor Rc).obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ⟶
      DerivedCategory.Q.obj ((K ⊗ L : CochainComplex (StructureSheafModules Rc) ℤ)) :=
  ((derivedTensorAsSiteDatum Rc).comparison K L hK hL).hom

/-- **The re-seating isomorphism `Stacks.SheafOfModules.derivedTensorMonoidalIso` carries the
K-flat comparison to the tensorator of the K-flat localization.** -/
theorem reseatIso_comp_derivedTensorComparisonHom
    (K L : CochainComplex (StructureSheafModules Rc) ℤ)
    (hK : KFlat Rc K) (hL : KFlat Rc L) :
    letI : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
      DerivedMonoidal.derivedMonoidal Rc
    (reseatIso (derivedTensorMonoidalIso Rc) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj L)).hom ≫ derivedTensorComparisonHom Rc K L hK hL =
      (CochainComplex.KFlatMonoidal.derivedTensorIso (DerivedMonoidal.Mod Rc)
        (DerivedMonoidal.exists_kFlat_resolution Rc) hK hL).hom :=
  DerivedMonoidal.reseatIso_comp_comparison Rc (derivedTensorAsSiteDatum Rc) K L hK hL

/-- **The associator of total tensor complexes, pushed into `D(O_X)`.** -/
def complexAssociatorHomSpace (K L M : CochainComplex (StructureSheafModules Rc) ℤ) :
    DerivedCategory.Q.obj
        (((K ⊗ L : CochainComplex (StructureSheafModules Rc) ℤ) ⊗ M :
          CochainComplex (StructureSheafModules Rc) ℤ)) ⟶
      DerivedCategory.Q.obj
        ((K ⊗ (L ⊗ M : CochainComplex (StructureSheafModules Rc) ℤ) :
          CochainComplex (StructureSheafModules Rc) ℤ)) :=
  DerivedCategory.Q.map (α_ K L M).hom

/-- **The associativity constraint of `Stacks.SheafOfModules.derivedMonoidalStructure`**, ascribed
at the bifunctor spelling of its source and target. -/
def derivedAssociatorHom (A B C : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj (((derivedTensor Rc).obj A).obj B)).obj C ⟶
      ((derivedTensor Rc).obj A).obj (((derivedTensor Rc).obj B).obj C) :=
  letI := derivedMonoidalStructure Rc
  (α_ A B C).hom

/-- **Right whiskering for `Stacks.SheafOfModules.derivedMonoidalStructure`**: the action of the
derived tensor bifunctor in its first variable, which is `▷` of that structure. -/
def derivedWhiskerRight {A B : DerivedCategory (StructureSheafModules Rc)} (f : A ⟶ B)
    (C : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedTensor Rc).obj A).obj C ⟶ ((derivedTensor Rc).obj B).obj C :=
  ((derivedTensor Rc).map f).app C

/-- **Left whiskering for `Stacks.SheafOfModules.derivedMonoidalStructure`**: the action of the
derived tensor bifunctor in its second variable, which is `◁` of that structure. -/
def derivedWhiskerLeft (A : DerivedCategory (StructureSheafModules Rc))
    {B C : DerivedCategory (StructureSheafModules Rc)} (g : B ⟶ C) :
    ((derivedTensor Rc).obj A).obj B ⟶ ((derivedTensor Rc).obj A).obj C :=
  ((derivedTensor Rc).obj A).map g

section Monoidal

attribute [local instance] derivedMonoidalStructure

/-- `Stacks.SheafOfModules.derivedAssociatorHom` *is* the associator of
`Stacks.SheafOfModules.derivedMonoidalStructure`. -/
theorem derivedAssociatorHom_eq (A B C : DerivedCategory (StructureSheafModules Rc)) :
    derivedAssociatorHom Rc A B C = (α_ A B C).hom :=
  rfl

/-- `Stacks.SheafOfModules.derivedWhiskerRight` *is* the right whiskering of
`Stacks.SheafOfModules.derivedMonoidalStructure`. -/
theorem derivedWhiskerRight_eq {A B : DerivedCategory (StructureSheafModules Rc)} (f : A ⟶ B)
    (C : DerivedCategory (StructureSheafModules Rc)) :
    derivedWhiskerRight Rc f C = f ▷ C :=
  rfl

/-- `Stacks.SheafOfModules.derivedWhiskerLeft` *is* the left whiskering of
`Stacks.SheafOfModules.derivedMonoidalStructure`. -/
theorem derivedWhiskerLeft_eq (A : DerivedCategory (StructureSheafModules Rc))
    {B C : DerivedCategory (StructureSheafModules Rc)} (g : B ⟶ C) :
    derivedWhiskerLeft Rc A g = A ◁ g :=
  rfl

end Monoidal

/-- **The associativity clause of Stacks 0FPT at the ringed-space re-seating**, as a
proposition. -/
def DerivedAssociatorComparison (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
    (hK : KFlat Rc K) (hL : KFlat Rc L) (hM : KFlat Rc M) : Prop :=
  derivedWhiskerRight Rc (derivedTensorComparisonHom Rc K L hK hL)
        (DerivedCategory.Q.obj M) ≫
      derivedTensorComparisonHom Rc (K ⊗ L) M
          (DerivedMonoidal.kFlat_tensor_complexes Rc hK hL) hM ≫
        complexAssociatorHomSpace Rc K L M =
    derivedAssociatorHom Rc (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
          (DerivedCategory.Q.obj M) ≫
      derivedWhiskerLeft Rc (DerivedCategory.Q.obj K)
          (derivedTensorComparisonHom Rc L M hL hM) ≫
        derivedTensorComparisonHom Rc K (L ⊗ M) hK
          (DerivedMonoidal.kFlat_tensor_complexes Rc hL hM)

/-- **The associativity constraint of `D(O_X)` is the associator of total tensor complexes**,
carried across by the K-flat comparison of Stacks 06YU: on the classes of K-flat complexes
`K`, `L`, `M`,

`(comparison K L) ▷ QM ≫ (comparison (K ⊗ L) M) ≫ Q(α_ K L M).hom =`
`  (α_ (QK) (QL) (QM)).hom ≫ (QK ◁ (comparison L M)) ≫ (comparison K (L ⊗ M))`,

the equation spelled out in `Stacks.SheafOfModules.DerivedAssociatorComparison`. -/
theorem derivedAssociator_comparison (K L M : CochainComplex (StructureSheafModules Rc) ℤ)
    (hK : KFlat Rc K) (hL : KFlat Rc L) (hM : KFlat Rc M) :
    DerivedAssociatorComparison Rc K L M hK hL hM :=
  let : MonoidalCategory (DerivedCategory (StructureSheafModules Rc)) :=
    DerivedMonoidal.derivedMonoidal Rc
  reseat_associator_comp_of_eq (derivedTensorMonoidalIso Rc)
    (DerivedMonoidal.canonicalUnitIso Rc)
    (complexAssociatorHomSpace Rc K L M)
    (reseatIso_comp_derivedTensorComparisonHom Rc K L hK hL)
    (reseatIso_comp_derivedTensorComparisonHom Rc L M hL hM)
    (reseatIso_comp_derivedTensorComparisonHom Rc (K ⊗ L) M
      (DerivedMonoidal.kFlat_tensor_complexes Rc hK hL) hM)
    (reseatIso_comp_derivedTensorComparisonHom Rc K (L ⊗ M) hK
      (DerivedMonoidal.kFlat_tensor_complexes Rc hL hM))
    (CochainComplex.KFlatMonoidal.associator_derivedTensorIso (DerivedMonoidal.Mod Rc)
      (DerivedMonoidal.exists_kFlat_resolution Rc) hK hL hM)

end Stacks.SheafOfModules

end
