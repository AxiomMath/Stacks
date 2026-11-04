module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.Pretriangulated

/-!
# Derived restriction of scalars and the translation, computed on modules

Let `φ : (A, d) → (B, d)` be a homomorphism of differential graded algebras over a commutative
ring. Restriction of scalars along `φ` does not change the underlying complex of a differential
graded `B`-module, so it commutes with the shift `N ↦ N[k]` on the nose: the identity of the
underlying module is a homomorphism `(N[k])_A ⟶ (N_A)[k]`. This file records that commutation
and descends it to derived restriction of scalars `(-)_A : D(B, d) ⥤ D(A, d)`, as a natural
isomorphism `(X[k])_A ≅ (X_A)[k]` whose value on the class of a differential graded `B`-module
is read off the identity of that module.

## Main definitions

* `DifferentialGradedModule.restrictScalarsShiftNatIso`: the commutation of restriction of scalars
  with the shift, on differential graded modules.
* `DifferentialGradedModule.derivedRestrictionShiftIso`: its descent to the derived categories.

## Main results

* `DifferentialGradedModule.derivedRestrictionShiftIso_inv_app`: the value of the descended
  isomorphism on the class of a differential graded module.

## Implementation notes

The descended isomorphism is not claimed to be compatible with the structure of the
translations (`shiftFunctorZero`, `shiftFunctorAdd`); it is the natural isomorphism with a known
value on the classes of modules that the comparison of the invertibility loci of
`StacksFrontier/CategoryTheory/Triangulated/TransposeLocus.lean` needs.

## References

* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public noncomputable section

open CategoryTheory

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-- Restriction of scalars commutes with the shift on the nose: the identity of the underlying
module of `N` is a homomorphism `(N[k])_A ⟶ (N_A)[k]`. -/
def restrictScalarsShiftHom (φ : A.Hom B) (k : ℤ) (N : DifferentialGradedModule.{u, u, u} B) :
    (restrictScalarsFunctor φ).obj ((CategoryTheory.shiftFunctor _ k).obj N) ⟶
      (CategoryTheory.shiftFunctor _ k).obj ((restrictScalarsFunctor φ).obj N) where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := rfl

/-- The inverse of `restrictScalarsShiftHom`, again the identity of the underlying module. -/
def restrictScalarsShiftInv (φ : A.Hom B) (k : ℤ) (N : DifferentialGradedModule.{u, u, u} B) :
    (CategoryTheory.shiftFunctor _ k).obj ((restrictScalarsFunctor φ).obj N) ⟶
      (restrictScalarsFunctor φ).obj ((CategoryTheory.shiftFunctor _ k).obj N) where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx
  map_d := rfl

/-- **Restriction of scalars commutes with the shift**, by the identity of the underlying
modules. -/
def restrictScalarsShiftNatIso (φ : A.Hom B) (k : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule.{u, u, u} B) k ⋙
        restrictScalarsFunctor φ ≅
      restrictScalarsFunctor φ ⋙ CategoryTheory.shiftFunctor _ k :=
  NatIso.ofComponents
    (fun N ↦
      { hom := restrictScalarsShiftHom φ k N
        inv := restrictScalarsShiftInv φ k N
        hom_inv_id := Hom.ext rfl
        inv_hom_id := Hom.ext rfl })
    (fun _ ↦ Hom.ext rfl)

/-- The component of `restrictScalarsShiftNatIso` at `N` is the identity of the underlying
module. -/
@[simp] theorem restrictScalarsShiftNatIso_hom_app_toFun (φ : A.Hom B) (k : ℤ)
    (N : DifferentialGradedModule.{u, u, u} B) :
    ((restrictScalarsShiftNatIso φ k).hom.app N).toFun = LinearMap.id :=
  rfl

/-- The component of the inverse of `restrictScalarsShiftNatIso` at `N` is the identity of the
underlying module. -/
@[simp] theorem restrictScalarsShiftNatIso_inv_app_toFun (φ : A.Hom B) (k : ℤ)
    (N : DifferentialGradedModule.{u, u, u} B) :
    ((restrictScalarsShiftNatIso φ k).inv.app N).toFun = LinearMap.id :=
  rfl

/-- The class functor `Mod(B, d) ⥤ D(B, d)`: the homotopy quotient followed by localization at
the quasi-isomorphisms. -/
abbrev classFunctor (B : DifferentialGradedAlgebra.{u, u} R) :
    DifferentialGradedModule.{u, u, u} B ⥤ derivedCategory' B :=
  toHomotopyCategory B ⋙ (quasiIsomorphisms' B).Q

/-- The commutation of derived restriction with the shift, on the classes of differential graded
`B`-modules, as a natural isomorphism of functors out of `Mod(B, d)`. It is assembled from the
factorization of derived restriction through restriction on homotopy categories, the
commutation of the class functors with the shift, and `restrictScalarsShiftNatIso`. -/
def derivedRestrictionShiftIsoOnModules (φ : A.Hom B) (k : ℤ) :
    classFunctor B ⋙ derivedRestriction φ ⋙ CategoryTheory.shiftFunctor _ k ≅
      classFunctor B ⋙ CategoryTheory.shiftFunctor _ k ⋙ derivedRestriction φ :=
  (Functor.isoWhiskerLeft (toHomotopyCategory B)
      (Functor.isoWhiskerRight (derivedRestrictionFactorization φ)
        (CategoryTheory.shiftFunctor _ k)) :
      classFunctor B ⋙ derivedRestriction φ ⋙ CategoryTheory.shiftFunctor _ k ≅
        toHomotopyCategory B ⋙ (restrictScalarsHomotopyFunctor φ ⋙ (quasiIsomorphisms' A).Q) ⋙
          CategoryTheory.shiftFunctor _ k) ≪≫
    (Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso φ)
        ((quasiIsomorphisms' A).Q ⋙ CategoryTheory.shiftFunctor _ k) :
      _ ≅ restrictScalarsFunctor φ ⋙ classFunctor A ⋙ CategoryTheory.shiftFunctor _ k) ≪≫
    Functor.isoWhiskerLeft (restrictScalarsFunctor φ) ((classFunctor A).commShiftIso k).symm ≪≫
    (Functor.isoWhiskerRight (restrictScalarsShiftNatIso φ k).symm (classFunctor A) :
      restrictScalarsFunctor φ ⋙ CategoryTheory.shiftFunctor _ k ⋙ classFunctor A ≅
        CategoryTheory.shiftFunctor _ k ⋙ restrictScalarsFunctor φ ⋙ classFunctor A) ≪≫
    (Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor _ k)
        (Functor.isoWhiskerRight (restrictScalarsHomotopyFunctorIso φ).symm
          (quasiIsomorphisms' A).Q) :
      _ ≅ CategoryTheory.shiftFunctor _ k ⋙ toHomotopyCategory B ⋙
        restrictScalarsHomotopyFunctor φ ⋙ (quasiIsomorphisms' A).Q) ≪≫
    (Functor.isoWhiskerLeft (CategoryTheory.shiftFunctor _ k ⋙ toHomotopyCategory B)
        (derivedRestrictionFactorization φ).symm :
      _ ≅ CategoryTheory.shiftFunctor _ k ⋙ classFunctor B ⋙ derivedRestriction φ) ≪≫
    (Functor.isoWhiskerRight ((classFunctor B).commShiftIso k) (derivedRestriction φ) :
      _ ≅ classFunctor B ⋙ CategoryTheory.shiftFunctor _ k ⋙ derivedRestriction φ)

/-- **The commutation of derived restriction of scalars with the shift**, descended from
`derivedRestrictionShiftIsoOnModules` through the homotopy quotient and the localization. -/
def derivedRestrictionShiftIso (φ : A.Hom B) (k : ℤ) :
    CategoryTheory.shiftFunctor (derivedCategory' B) k ⋙ derivedRestriction φ ≅
      derivedRestriction φ ⋙ CategoryTheory.shiftFunctor (derivedCategory' A) k :=
  (Localization.liftNatIso (quasiIsomorphisms' B).Q (quasiIsomorphisms' B)
    ((quasiIsomorphisms' B).Q ⋙ derivedRestriction φ ⋙ CategoryTheory.shiftFunctor _ k)
    ((quasiIsomorphisms' B).Q ⋙ CategoryTheory.shiftFunctor _ k ⋙ derivedRestriction φ)
    (derivedRestriction φ ⋙ CategoryTheory.shiftFunctor _ k)
    (CategoryTheory.shiftFunctor _ k ⋙ derivedRestriction φ)
    (CategoryTheory.Quotient.natIsoLift _ (derivedRestrictionShiftIsoOnModules φ k))).symm

/-- **The value of `derivedRestrictionShiftIso` on the class of a module**: it is
`derivedRestrictionShiftIsoOnModules`. -/
theorem derivedRestrictionShiftIso_inv_app (φ : A.Hom B) (k : ℤ)
    (N : DifferentialGradedModule.{u, u, u} B) :
    (derivedRestrictionShiftIso φ k).inv.app ((classFunctor B).obj N) =
      (derivedRestrictionShiftIsoOnModules φ k).hom.app N := by
  simp [derivedRestrictionShiftIso]

end DifferentialGradedModule

end
