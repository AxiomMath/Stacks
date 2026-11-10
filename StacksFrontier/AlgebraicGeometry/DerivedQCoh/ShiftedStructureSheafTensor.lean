module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.Triangulated
public import StacksFrontier.Homology.TotalComplexTransportSingle
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorUnit

/-!
# The structure sheaf in a shifted degree as a tensor factor

Let `(Z, 𝒪_Z)` be a ringed space. The structure sheaf placed in cohomological degree `a` is
`𝒪_Z[-a]`, and a morphism out of it into `K` is a class in `H^a(Z, K)`. For `a, b : ℤ` there is a
canonical isomorphism

`𝒪_Z[-a-b] ≅ 𝒪_Z[-a] ⊗^𝐋_{𝒪_Z} 𝒪_Z[-b]`

in `D(𝒪_Z)`: both factors are K-flat complexes, so their derived tensor product is the total tensor
complex `Tot(𝒪_Z[-a] ⊗_{𝒪_Z} 𝒪_Z[-b])`, whose only nonzero term is `𝒪_Z ⊗_{𝒪_Z} 𝒪_Z = 𝒪_Z` in
degree `a + b`. Together with the identification `Lf^*(𝒪_Y[-a]) ≅ 𝒪_X[-a]` of the derived
pullback of a shifted structure sheaf, it is what turns a cup product written on corepresenting
objects into a pairing of cohomology groups in the source's degrees.

## Main definitions

* `shiftedUnitObject` is `𝒪_Z[-a]`, and `shiftedUnitComplex` the complex representing it.
* `shiftedUnitShiftIso` is `𝒪_Z[-a] ≅ (𝒪_Z[0])⟦-a⟧`, the shift isomorphism of the family of
  single-object functors.
* `shiftedUnitComplexTensorIso` is `Tot(𝒪_Z[-a] ⊗ 𝒪_Z[-b]) ≅ 𝒪_Z[-a-b]` on complexes.
* `shiftedUnitTensorIso` is the isomorphism `𝒪_Z[-a-b] ≅ 𝒪_Z[-a] ⊗^𝐋 𝒪_Z[-b]`.
* `derivedPullbackShiftedUnitIso` is `Lf^*(𝒪_Y[-a]) ≅ 𝒪_X[-a]`.
* `derivedPullbackShiftedUnitTensorIso` is `𝒪_X[-a-b] ≅ Lf^*(𝒪_Y[-a]) ⊗^𝐋_{𝒪_X} 𝒪_X[-b]`, the
  two previous isomorphisms composed.

## Implementation notes

The derived tensor product is computed on the two K-flat single complexes by the `toTensor`
field of [Stacks, Tag 06YU], which is invertible there. The shift is moved across the derived
pullback by `Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift`, which is
[Stacks, Tag 06YJ] for the compatibility of `Lf^*` with shifts. The degree bookkeeping is
Mathlib's `CategoryTheory.SingleFunctors.shiftIso` for `DerivedCategory.singleFunctors`.

## References

* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.RingedSpace

attribute [local instance] HasDerivedCategory.standard

/-- The structure sheaf of a ringed space placed in cohomological degree `a`, that is `𝒪_Z[-a]`.
A morphism out of it into `K` is a class in `H^a(Z, K)`. -/
abbrev shiftedUnitObject (Z : RingedSpace.{u, u}) (a : ℤ) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing Z)) a).obj
    (SheafOfModules.unit (structureSheafRing Z))

/-- `𝒪_Z[-a] ≅ (𝒪_Z[0])⟦-a⟧`: the structure sheaf in degree `a` is the shift by `-a` of the
structure sheaf in degree `0`. -/
def shiftedUnitShiftIso (Z : RingedSpace.{u, u}) (a : ℤ) :
    (shiftFunctor (DerivedCategory
          (SheafOfModules.{u} (structureSheafRing Z))) (-a)).obj
        (shiftedUnitObject Z 0) ≅
      shiftedUnitObject Z a :=
  ((DerivedCategory.singleFunctors
        (SheafOfModules.{u} (structureSheafRing Z))).shiftIso (-a) a 0
      (by omega)).app (SheafOfModules.unit (structureSheafRing Z))

section Tensor

variable (Z : RingedSpace.{u, u})
  [HasSheafify (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Z.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The structure sheaf placed in degree `a`, as a cochain complex of `𝒪_Z`-modules. Its image in
the derived category is `shiftedUnitObject Z a`. -/
abbrev shiftedUnitComplex (a : ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ :=
  (HomologicalComplex.single _ (ComplexShape.up ℤ) a).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))

/-- The structure sheaf placed in a single degree is a K-flat complex. -/
theorem kFlat_shiftedUnitComplex (a : ℤ) :
    Stacks.SheafOfModules.KFlat Z.sheaf (shiftedUnitComplex Z a) :=
  Stacks.SheafOfModules.isKFlat_single_obj_unit (toRingedSite Z).O a

/-- The unit constraint `𝒪_Z ⊗_{𝒪_Z} 𝒪_Z ≅ 𝒪_Z` of the tensor product of sheaves of modules. -/
def unitTensorUnitIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf) :=
  @MonoidalCategoryStruct.leftUnitor _ _
    (SheafOfModules.monoidalCategorySheafTensor Z.sheaf).toMonoidalCategoryStruct
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))

/-- **The degree identification on complexes**: `Tot(𝒪_Z[-a] ⊗_{𝒪_Z} 𝒪_Z[-b]) ≅ 𝒪_Z[-a-b]`.
The total complex has the single summand `𝒪_Z ⊗_{𝒪_Z} 𝒪_Z` in degree `a + b`, which the unit
constraint identifies with `𝒪_Z`. -/
def shiftedUnitComplexTensorIso (a b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.tensorComplex Z.sheaf).obj (shiftedUnitComplex Z a)).obj
        (shiftedUnitComplex Z b) ≅ shiftedUnitComplex Z (a + b) :=
  Functor.mapBifunctorSingleSingleUnitIso
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf) (unitTensorUnitIso Z) a b

/-- The canonical map of [Stacks, Tag 06YU] from the derived tensor product to the total tensor
complex is invertible at two shifted structure sheaves, these being K-flat. -/
instance isIso_toTensor_shiftedUnitComplex (a b : ℤ) :
    IsIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor (shiftedUnitComplex Z a)
      (shiftedUnitComplex Z b)) := by
  rw [(canonicalDerivedTensorProduct Z.sheaf).toTensor_eq_comparison _ _
    (kFlat_shiftedUnitComplex Z a) (kFlat_shiftedUnitComplex Z b)]
  infer_instance

/-- **The degree identification of the cup product**:
`𝒪_Z[-a-b] ≅ 𝒪_Z[-a] ⊗^𝐋_{𝒪_Z} 𝒪_Z[-b]`. Both shifted structure sheaves are K-flat, so the
derived tensor product of [Stacks, Tag 06YU] is computed by the total tensor complex
`Tot(𝒪_Z[-a] ⊗_{𝒪_Z} 𝒪_Z[-b])`, which is `𝒪_Z[-a-b]` by `shiftedUnitComplexTensorIso`. -/
def shiftedUnitTensorIso (a b : ℤ) :
    shiftedUnitObject Z (a + b) ≅
      ((derivedTensorProductFunctor Z.sheaf).obj (shiftedUnitObject Z a)).obj
        (shiftedUnitObject Z b) :=
  (DerivedCategory.Q.mapIso (shiftedUnitComplexTensorIso Z a b)).symm ≪≫
    (asIso ((canonicalDerivedTensorProduct Z.sheaf).toTensor (shiftedUnitComplex Z a)
      (shiftedUnitComplex Z b))).symm

/-- The degree identification of the cup product, written out. -/
theorem shiftedUnitTensorIso_hom (a b : ℤ) :
    (shiftedUnitTensorIso Z a b).hom =
      DerivedCategory.Q.map (shiftedUnitComplexTensorIso Z a b).inv ≫
        inv ((canonicalDerivedTensorProduct Z.sheaf).toTensor (shiftedUnitComplex Z a)
          (shiftedUnitComplex Z b)) :=
  rfl

end Tensor

section Pullback

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived pullback of a shifted structure sheaf**: `Lf^*(𝒪_Y[-a]) ≅ 𝒪_X[-a]`. The derived
pullback commutes with the shift, [Stacks, Tag 06YJ], and takes `𝒪_Y[0]` to `𝒪_X[0]`. -/
def derivedPullbackShiftedUnitIso (a : ℤ) :
    (derivedPullback f).obj (shiftedUnitObject Y a) ≅ shiftedUnitObject X a :=
  (derivedPullback f).mapIso (shiftedUnitShiftIso Y a).symm ≪≫
    ((derivedPullback f).commShiftIso (-a)).app (shiftedUnitObject Y 0) ≪≫
    (shiftFunctor (DerivedCategory
        (SheafOfModules.{u} (structureSheafRing X))) (-a)).mapIso
      (derivedPullbackSingleUnitIso f) ≪≫
    shiftedUnitShiftIso X a

/-- **The degree identification of the cup product, with the first factor pulled back**:
`𝒪_X[-a-b] ≅ Lf^*(𝒪_Y[-a]) ⊗^𝐋_{𝒪_X} 𝒪_X[-b]`. This is `shiftedUnitTensorIso` on `X` followed by
the identification `𝒪_X[-a] ≅ Lf^*(𝒪_Y[-a])` in the left factor. -/
def derivedPullbackShiftedUnitTensorIso (a b : ℤ) :
    shiftedUnitObject X (a + b) ≅
      ((derivedTensorProductFunctor X.sheaf).obj
        ((derivedPullback f).obj (shiftedUnitObject Y a))).obj (shiftedUnitObject X b) :=
  shiftedUnitTensorIso X a b ≪≫
    ((derivedTensorProductFunctor X.sheaf).flip.obj (shiftedUnitObject X b)).mapIso
      (derivedPullbackShiftedUnitIso f a).symm

end Pullback

end Stacks.RingedSpace

end
