module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComplexesOfModules
public import StacksFrontier.Homology.DerivedCategory.Monoidal.KFlatLocalization

/-!
# The derived category of modules on a ringed site is symmetric monoidal, at general universes

Let `(C, O)` be a ringed site whose objects live in a universe `c` and whose morphisms and sections
live in the universe `u` of the sheaf of rings. `D(Mod(O))` with the derived tensor product of
Stacks 06YU is a symmetric monoidal category (Stacks 0FPT), K-flat resolutions coming from Stacks
06YS. The graded and colimit instances of `Mod(O)` that the monoidal structure on complexes needs
at these universes are global instances here.

## Implementation notes

This is the part of `StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory` that
does not need `C` to be a `SmallCategory.{u}`, for a site `C : Type c` with `[Category.{u} C]`; the
statements and proofs are the same, in the namespace
`Stacks.SheafOfModules.DerivedMonoidalGeneral`.
This applies to the small étale ringed site of an algebraic space.

## References

* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d c u

namespace Stacks.SheafOfModules.DerivedMonoidalGeneral

variable {C : Type c} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `Mod(O)`, the category of `O`-modules on the ringed site `(C, O)`. -/
abbrev Mod := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} R)

/-- `Comp(Mod(O))`, the category of cochain complexes of `O`-modules. -/
abbrev Complexes := CochainComplex (Mod R) ℤ

variable [HasDerivedCategory.{d} (Mod R)]

/-- `D(Mod(O))`, the unbounded derived category of `O`-modules. -/
abbrev DerivedModules := DerivedCategory (Mod R)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor

/-- Tensoring on the left with a fixed `O`-module preserves the colimits of small shapes, for the
monoidal structure whose tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor R`
(Stacks 05NB). -/
instance preservesColimitsOfSize_tensorLeft (M : Mod R) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  letI := Stacks.SheafOfModules.preservesColimits_sheafTensorObj R M
  preservesSmallestColimits_of_preservesColimits
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M)

/-- Tensoring on the right with a fixed `O`-module preserves the colimits of small shapes. -/
instance preservesColimitsOfSize_tensorRight (M : Mod R) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  letI := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj R M
  preservesSmallestColimits_of_preservesColimits
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).flip.obj M)

/-- `Mod(O)` has the colimits of every shape in `Type 0`, whatever the universes of the site:
they are sheafified colimits of presheaves of modules. -/
instance hasColimitsOfSize_mod : HasColimitsOfSize.{0, 0} (Mod R) :=
  let _ : HasColimitsOfSize.{0, 0}
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} R).obj) :=
    inferInstance
  inferInstance

/-- The coproducts along the antidiagonals of two graded `O`-modules exist. -/
instance hasTensor_mod (X₁ X₂ : GradedObject ℤ (Mod R)) : GradedObject.HasTensor X₁ X₂ :=
  fun _ => ((hasColimitsOfSize_mod R).has_colimits_of_shape _).has_colimit _

/-- Tensoring on the left commutes with the coproducts of a threefold graded tensor product. -/
instance hasTensor₄ObjExt_mod (X₁ X₂ X₃ X₄ : GradedObject ℤ (Mod R)) :
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ :=
  inferInstance

/-- Tensoring on the right commutes with the coproducts of the first two graded variables. -/
instance hasGoodTensor₁₂Tensor_mod (X₁ X₂ X₃ : GradedObject ℤ (Mod R)) :
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ :=
  inferInstance

/-- Tensoring on the left commutes with the coproducts of the last two graded variables. -/
instance hasGoodTensorTensor₂₃_mod (X₁ X₂ X₃ : GradedObject ℤ (Mod R)) :
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ :=
  inferInstance

/-- Tensoring on the left preserves the initial object. -/
instance preservesColimit_empty_tensorLeft_mod (X : Mod R) :
    PreservesColimit (Functor.empty.{0} (Mod R)) ((curriedTensor (Mod R)).obj X) :=
  inferInstanceAs (PreservesColimit _ (tensorLeft X))

/-- Tensoring on the right preserves the initial object. -/
instance preservesColimit_empty_tensorRight_mod (X : Mod R) :
    PreservesColimit (Functor.empty.{0} (Mod R)) ((curriedTensor (Mod R)).flip.obj X) :=
  inferInstanceAs (PreservesColimit _ (tensorRight X))

attribute [local instance] CochainComplex.symmetricCategory

omit [HasDerivedCategory.{d} (Mod R)] in
/-- Every complex of `O`-modules receives a quasi-isomorphism from a K-flat one, in the form
the generic construction consumes.  This is `Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso`
  with the
K-flatness read at `curriedTensor (Mod R)`, which is `Stacks.SheafOfModules.Tensor.sheafTensor R`.
-/
theorem exists_kFlat_resolution
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (G : Complexes R) :
    ∃ (P : Complexes R) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) P ∧ QuasiIso f :=
  let ⟨P, f, hP, _, hf, _⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution_ofSize R G
  ⟨P, f, hP, hf⟩

/-- **The derived category of modules on a ringed site is monoidal**, under the derived
tensor product. -/
@[instance_reducible]
def derivedMonoidal
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    MonoidalCategory (DerivedModules R) :=
  CochainComplex.KFlatMonoidal.derivedMonoidal (Mod R) (exists_kFlat_resolution R)

/-- **The derived category of modules on a ringed site is symmetric monoidal**, with the
commutativity constraint induced by the Koszul symmetry of complexes. -/
@[instance_reducible]
def derivedSymmetric
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    @SymmetricCategory (DerivedModules R) _ (derivedMonoidal R) :=
  CochainComplex.KFlatMonoidal.derivedSymmetric (Mod R) (exists_kFlat_resolution R)

/-! ### The field types of `SymmetricMonoidalDerived` -/

/-- A monoidal category structure on `D(Mod(O))`. -/
abbrev Monoidal := MonoidalCategory (DerivedModules R)

/-- A symmetry for a monoidal structure on `D(Mod(O))`. -/
abbrev Symmetric [Monoidal R] := SymmetricCategory (DerivedModules R)

/-- K-flatness of a complex of `O`-modules, Stacks Tag 06YN, in the spelling
`Stacks.DerivedTensor.RingedSite` uses. -/
abbrev KFlat (K : Complexes R) : Prop :=
  CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} R) K

/-- On K-flat complexes the tensor product of `D(Mod(O))` is the image of the total tensor
product `Tot(- ⊗_O -)`: this is what identifies it as the *derived* tensor product. -/
abbrev Comparison [Monoidal R] :=
  ∀ (K L : Complexes R), KFlat R K → KFlat R L →
    Iso (C := DerivedModules R)
      (MonoidalCategoryStruct.tensorObj (C := DerivedModules R)
        ((DerivedCategory.Q (C := Mod R)).obj K) ((DerivedCategory.Q (C := Mod R)).obj L))
      ((DerivedCategory.Q (C := Mod R)).obj (K ⊗ L))

/-- The unit of `D(Mod(O))` is the structure sheaf in degree zero. -/
abbrev UnitIso [Monoidal R] :=
  Iso (C := DerivedModules R) (𝟙_ (DerivedModules R))
    ((DerivedCategory.Q (C := Mod R)).obj
      ((CochainComplex.singleFunctor (Mod R) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} R))))

/-! ### The statement -/

/-- A symmetric monoidal structure on the derived category of modules on a ringed site, whose
tensor product is the derived tensor product — on K-flat complexes the total tensor product —
and whose unit is the structure sheaf in degree zero. -/
public structure SymmetricMonoidalDerived where
  /-- The monoidal structure on `D(Mod(O))`. -/
  monoidal : Monoidal R
  /-- The symmetry of the monoidal structure `monoidal`. -/
  symmetric : Symmetric R
  /-- On K-flat complexes the tensor product is the image of the total tensor product. -/
  comparison : Comparison R
  /-- The unit is the structure sheaf in degree zero. -/
  unitIso : UnitIso R

/-! ### The construction -/

/-- **The derived category of modules on a ringed site is symmetric monoidal**, with tensor
product the derived tensor product and unit the structure sheaf in degree zero. -/
public def symmetricMonoidalDerived : SymmetricMonoidalDerived R where
  monoidal := derivedMonoidal R
  symmetric := derivedSymmetric R
  comparison _ _ hK hL :=
    CochainComplex.KFlatMonoidal.derivedTensorIso (Mod R) (exists_kFlat_resolution R) hK hL
  unitIso :=
    CochainComplex.KFlatMonoidal.derivedUnitIso (Mod R) (exists_kFlat_resolution R)

/-! ### The monoidal structures on `Mod(O)` and `Comp(Mod(O))`, at pinned universes

The sections universe of `SheafOfModules.monoidalCategorySheafTensor` and of the three
structures built on it is `max u v` in the two site universes, which instance synthesis has to
solve from the `u` of `Mod R` at every use.  A monoidal structure on `Comp(Mod(O))` synthesized
from one whose universes are still unsolved is a structure the whiskerings of the
consumers cannot reduce through.  Each of these pins the morphism universe of the site and the
sections universe at the universe `u` of the sheaf of rings, and the object universe at `c`; the
closed structure needs the objects in `u` as well.  They are `local`: the consumers put them back
in scope by name. -/

/-- `Mod(O)` is monoidal, at pinned universes. -/
@[instance_reducible] local instance monoidalCategoryMod : MonoidalCategory (Mod R) :=
  SheafOfModules.monoidalCategorySheafTensor.{u, c, u} R

/-- `Mod(O)` is symmetric monoidal, at pinned universes. -/
@[instance_reducible] local instance symmetricCategoryMod : SymmetricCategory (Mod R) :=
  SheafOfModules.symmetricCategorySheafTensor.{u, c, u} R

/-- `⊗_O` is bilinear on morphisms, at pinned universes. -/
local instance monoidalPreadditiveMod : MonoidalPreadditive (Mod R) :=
  SheafOfModules.monoidalPreadditiveSheafTensor.{u, c, u} R

/-- `Mod(O)` is monoidal closed, at pinned universes, when the objects and the morphisms of the
site lie in the universe of the sheaf of rings. -/
@[instance_reducible] local instance monoidalClosedMod {C : Type u} [SmallCategory.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] : MonoidalClosed (Mod R) :=
  SheafOfModules.monoidalClosedSheafTensor.{u, u, u} R

/-- The graded tensor products of `O`-modules exist. -/
local instance hasTensorMod
    {C : Type c} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (Mod R)] :
    ∀ A B : GradedObject ℤ (Mod R), GradedObject.HasTensor A B :=
  fun _ _ => inferInstance

/-- `Comp(Mod(O))` is monoidal, at pinned universes. -/
@[instance_reducible] local instance monoidalComplexes : MonoidalCategory (Complexes R) :=
  HomologicalComplex.monoidalCategory _ _

end Stacks.SheafOfModules.DerivedMonoidalGeneral

end
