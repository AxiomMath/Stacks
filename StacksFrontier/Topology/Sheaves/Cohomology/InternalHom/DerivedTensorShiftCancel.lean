module

public import StacksFrontier.CategoryTheory.Monoidal.InvertibleObjectShift
public import StacksFrontier.Homology.DerivedCategory.Monoidal.CurriedTensorCommShift
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The derived tensor product commutes with the shift, and opposite shifts cancel

Let `(X, 𝒪_X)` be a ringed space.  For the monoidal structure of Tag 0FPT on `D(𝒪_X)` both
`K ⊗^L -` and `- ⊗^L K` commute with the shift, and consequently shifting the two tensor factors
in opposite directions leaves the derived tensor product unchanged:

`M⟦-n⟧ ⊗^L N⟦n⟧ ≅ M ⊗^L N`.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.commShift_derivedTensorLeft` and
  `commShift_derivedTensorRight`: the two commutations on a ringed site.
* `Stacks.Cohomology.MonoidalDerived.commShift_derivedTensorLeft` and
  `commShift_derivedTensorRight`: the same on a ringed space.
* `Stacks.Cohomology.MonoidalDerived.derivedTensorShiftCancelIso`:
  **`M⟦-n⟧ ⊗^L N⟦n⟧ ≅ M ⊗^L N`**.
* `Stacks.Cohomology.MonoidalDerived.derivedTensorSingleShiftCancelIso`: the same read at the
  single-degree functors, **`A[n] ⊗^L B[-n] ≅ A[0] ⊗^L B[0]`**.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

universe d

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/-- **`K ⊗^L -` commutes with the shift** on the derived category of modules on a ringed site,
for the monoidal structure of Tag 0FPT. -/
@[instance_reducible]
def commShift_derivedTensorLeft (K : DerivedModules R) :
    letI := derivedMonoidal R
    (MonoidalCategory.tensorLeft K).CommShift ℤ :=
  CochainComplex.KFlatMonoidal.derivedMonoidal_tensorLeft_commShift (Mod R)
    (exists_kFlat_resolution R) K

/-- **`- ⊗^L L` commutes with the shift** on the derived category of modules on a ringed site,
for the monoidal structure of Tag 0FPT. -/
@[instance_reducible]
def commShift_derivedTensorRight (L : DerivedModules R) :
    letI := derivedMonoidal R
    (MonoidalCategory.tensorRight L).CommShift ℤ :=
  CochainComplex.KFlatMonoidal.derivedMonoidal_tensorRight_commShift (Mod R)
    (exists_kFlat_resolution R) L

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open AlgebraicGeometry Stacks.SheafOfModules.DerivedMonoidal

universe d

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (Mod X.sheaf)]

/-- **`K ⊗^L_{𝒪_X} -` commutes with the shift**, for the monoidal structure of Tag 0FPT on
`D(𝒪_X)`. -/
@[instance_reducible]
def commShift_derivedTensorLeft (K : DerivedModules X.sheaf) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    (MonoidalCategory.tensorLeft K).CommShift ℤ :=
  Stacks.SheafOfModules.DerivedMonoidal.commShift_derivedTensorLeft X.sheaf K

/-- **`- ⊗^L_{𝒪_X} K` commutes with the shift**, for the monoidal structure of Tag 0FPT on
`D(𝒪_X)`. -/
@[instance_reducible]
def commShift_derivedTensorRight (K : DerivedModules X.sheaf) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    (MonoidalCategory.tensorRight K).CommShift ℤ :=
  Stacks.SheafOfModules.DerivedMonoidal.commShift_derivedTensorRight X.sheaf K

/-- **Opposite shifts cancel in the derived tensor product**: `M⟦-n⟧ ⊗^L N⟦n⟧ ≅ M ⊗^L N` in
`D(𝒪_X)`, for the monoidal structure of Tag 0FPT. -/
def derivedTensorShiftCancelIso (M N : DerivedModules X.sheaf) (n : ℤ) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    MonoidalCategory.tensorObj ((shiftFunctor (DerivedModules X.sheaf) (-n)).obj M)
        ((shiftFunctor (DerivedModules X.sheaf) n).obj N) ≅
      MonoidalCategory.tensorObj M N :=
  letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  letI := fun K : DerivedModules X.sheaf => commShift_derivedTensorLeft.{u, d} X K
  letI := fun K : DerivedModules X.sheaf => commShift_derivedTensorRight.{u, d} X K
  MonoidalCategory.shiftNegTensorShiftIso M N n

/-- **Opposite shifts of modules cancel in the derived tensor product**:
`A[n] ⊗^L B[-n] ≅ A[0] ⊗^L B[0]` in `D(𝒪_X)`, for two `𝒪_X`-modules `A` and `B`. -/
def derivedTensorSingleShiftCancelIso (A B : Mod X.sheaf) (n : ℤ) :
    letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
    MonoidalCategory.tensorObj ((DerivedCategory.singleFunctor (Mod X.sheaf) n).obj A)
        ((DerivedCategory.singleFunctor (Mod X.sheaf) (-n)).obj B) ≅
      MonoidalCategory.tensorObj ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj A)
        ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj B) :=
  letI := Stacks.Cohomology.MonoidalDerived.derivedCategoryMonoidalCategory.{u, d} X
  MonoidalCategory.tensorIso
      (((DerivedCategory.singleFunctors (Mod X.sheaf)).shiftIso (-n) n 0 (by omega)).app A).symm
      (((DerivedCategory.singleFunctors (Mod X.sheaf)).shiftIso n (-n) 0 (by omega)).app B).symm ≪≫
    derivedTensorShiftCancelIso.{u, d} X _ _ n

end Stacks.Cohomology.MonoidalDerived

end
